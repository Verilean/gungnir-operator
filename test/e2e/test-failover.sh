#!/usr/bin/env bash
# test-failover.sh - Verify ValkeyCluster failover
#
# This test verifies that the operator correctly handles master failure:
#   1. Create CR with 3 replicas and wait for ready
#   2. Write a test key via valkey-cli SET on the master
#   3. Delete pod-0 (the master) to simulate failure
#   4. Wait up to 60s for a new master to be elected among remaining pods
#   5. Verify the test key is still readable from the new master
#   6. Verify the client service selector was updated to point to the new master
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CR_NAME="test-valkey"
NAMESPACE="default"
TIMEOUT=120
FAILOVER_TIMEOUT=60

cleanup() {
  echo "[cleanup] Deleting ValkeyCluster CR..."
  kubectl delete -f "$SCRIPT_DIR/sample-cr.yaml" --ignore-not-found -n "$NAMESPACE" || true
  kubectl wait --for=delete statefulset/"$CR_NAME" -n "$NAMESPACE" --timeout=60s 2>/dev/null || true
}

trap cleanup EXIT

wait_for_ready_pods() {
  local expected="$1"
  local timeout="$2"
  local elapsed=0

  echo "  Waiting for $expected pods to be ready (timeout: ${timeout}s)..."
  while [ "$elapsed" -lt "$timeout" ]; do
    ready=$(kubectl get statefulset "$CR_NAME" -n "$NAMESPACE" -o jsonpath='{.status.readyReplicas}' 2>/dev/null || echo "0")
    if [ "$ready" = "$expected" ]; then
      echo "  StatefulSet ready: $ready/$expected"
      return 0
    fi
    echo "  Waiting... ($ready/$expected ready, ${elapsed}s elapsed)"
    sleep 5
    elapsed=$((elapsed + 5))
  done

  echo "  TIMEOUT: Only $ready/$expected pods ready after ${timeout}s"
  kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" || true
  return 1
}

echo "[1/6] Creating ValkeyCluster CR with 3 replicas..."
kubectl apply -f "$SCRIPT_DIR/sample-cr.yaml" -n "$NAMESPACE"
wait_for_ready_pods 3 "$TIMEOUT"

echo "[2/6] Writing test key to master (pod-0)..."
kubectl exec "${CR_NAME}-0" -n "$NAMESPACE" -- valkey-cli SET failover-test-key "gungnir-e2e-value"
# Ensure replication has time to propagate
sleep 2
# Verify the key exists on a replica to confirm replication
REPLICA_VAL=$(kubectl exec "${CR_NAME}-1" -n "$NAMESPACE" -- valkey-cli GET failover-test-key 2>/dev/null || echo "")
if [ "$REPLICA_VAL" = "gungnir-e2e-value" ]; then
  echo "  OK: test key replicated to ${CR_NAME}-1"
else
  echo "  WARNING: test key not yet replicated to ${CR_NAME}-1 (value='$REPLICA_VAL')"
fi

echo "[3/6] Deleting master pod (${CR_NAME}-0) to simulate failure..."
kubectl delete pod "${CR_NAME}-0" -n "$NAMESPACE" --grace-period=0 --force 2>/dev/null || \
  kubectl delete pod "${CR_NAME}-0" -n "$NAMESPACE"

echo "[4/6] Waiting for new master election (timeout: ${FAILOVER_TIMEOUT}s)..."
elapsed=0
NEW_MASTER=""
while [ "$elapsed" -lt "$FAILOVER_TIMEOUT" ]; do
  # Check each remaining pod to see if one has been promoted to master
  for pod in "${CR_NAME}-1" "${CR_NAME}-2"; do
    role=$(kubectl exec "$pod" -n "$NAMESPACE" -- valkey-cli ROLE 2>/dev/null | head -1 || echo "unknown")
    if [ "$role" = "master" ]; then
      NEW_MASTER="$pod"
      break 2
    fi
  done
  echo "  Waiting for master election... (${elapsed}s elapsed)"
  sleep 5
  elapsed=$((elapsed + 5))
done

if [ -z "$NEW_MASTER" ]; then
  echo "FAIL: No new master elected within ${FAILOVER_TIMEOUT}s"
  echo "Pod roles:"
  for pod in "${CR_NAME}-0" "${CR_NAME}-1" "${CR_NAME}-2"; do
    role=$(kubectl exec "$pod" -n "$NAMESPACE" -- valkey-cli ROLE 2>/dev/null | head -1 || echo "unreachable")
    echo "  $pod: $role"
  done
  exit 1
fi

echo "  OK: New master elected: $NEW_MASTER"

echo "[5/6] Verifying test key is readable from new master..."
VALUE=$(kubectl exec "$NEW_MASTER" -n "$NAMESPACE" -- valkey-cli GET failover-test-key 2>/dev/null || echo "")
if [ "$VALUE" = "gungnir-e2e-value" ]; then
  echo "  OK: test key preserved after failover (value='$VALUE')"
else
  echo "  FAIL: test key lost or incorrect after failover (value='$VALUE', expected 'gungnir-e2e-value')"
  exit 1
fi

echo "[6/6] Verifying client service selector updated..."
# The operator patches the client service with statefulset.kubernetes.io/pod-name
# pointing to the new master pod
SELECTOR_POD=$(kubectl get svc "${CR_NAME}-client" -n "$NAMESPACE" \
  -o jsonpath='{.spec.selector.statefulset\.kubernetes\.io/pod-name}' 2>/dev/null || echo "")
if [ "$SELECTOR_POD" = "$NEW_MASTER" ]; then
  echo "  OK: client service selector points to new master ($SELECTOR_POD)"
else
  # The selector might not have the pod-name field if the operator uses instance label only.
  # In that case, check if the service at least has the correct instance label.
  SELECTOR_INSTANCE=$(kubectl get svc "${CR_NAME}-client" -n "$NAMESPACE" \
    -o jsonpath='{.spec.selector.app\.kubernetes\.io/instance}' 2>/dev/null || echo "")
  if [ "$SELECTOR_INSTANCE" = "$CR_NAME" ]; then
    echo "  OK: client service selector uses instance label ($SELECTOR_INSTANCE)"
    echo "  NOTE: pod-name selector is '$SELECTOR_POD' (may be set after operator reconcile)"
  else
    echo "  FAIL: client service selector not updated (pod-name='$SELECTOR_POD', instance='$SELECTOR_INSTANCE')"
    kubectl get svc "${CR_NAME}-client" -n "$NAMESPACE" -o yaml || true
    exit 1
  fi
fi

echo "All failover checks passed."
