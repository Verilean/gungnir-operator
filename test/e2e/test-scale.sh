#!/usr/bin/env bash
# test-scale.sh - Verify ValkeyCluster scaling
#
# This test verifies that the operator correctly handles scaling:
#   1. Create CR with 3 replicas and wait for ready
#   2. Scale up to 5 replicas and wait for all 5 pods ready
#   3. Scale back down to 3 replicas and wait for 3 pods ready
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CR_NAME="test-valkey"
NAMESPACE="default"
TIMEOUT=120

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

echo "[1/5] Creating ValkeyCluster CR with 3 replicas..."
kubectl apply -f "$SCRIPT_DIR/sample-cr.yaml" -n "$NAMESPACE"
wait_for_ready_pods 3 "$TIMEOUT"

echo "[2/5] Scaling up to 5 replicas..."
kubectl patch valkeycluster "$CR_NAME" -n "$NAMESPACE" \
  --type merge -p '{"spec":{"replicas":5}}'
wait_for_ready_pods 5 "$TIMEOUT"

echo "[3/5] Verifying 5 pods are running..."
POD_COUNT=$(kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" \
  --field-selector=status.phase=Running -o name 2>/dev/null | wc -l | tr -d ' ')
if [ "$POD_COUNT" -eq 5 ]; then
  echo "  OK: $POD_COUNT pods running"
else
  echo "  FAIL: $POD_COUNT pods running, expected 5"
  exit 1
fi

echo "[4/5] Scaling back down to 3 replicas..."
kubectl patch valkeycluster "$CR_NAME" -n "$NAMESPACE" \
  --type merge -p '{"spec":{"replicas":3}}'
wait_for_ready_pods 3 "$TIMEOUT"

echo "[5/5] Verifying 3 pods are running..."
POD_COUNT=$(kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" \
  --field-selector=status.phase=Running -o name 2>/dev/null | wc -l | tr -d ' ')
if [ "$POD_COUNT" -eq 3 ]; then
  echo "  OK: $POD_COUNT pods running"
else
  echo "  FAIL: $POD_COUNT pods running, expected 3"
  exit 1
fi

echo "All scale checks passed."
