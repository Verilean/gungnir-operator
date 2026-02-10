#!/usr/bin/env bash
# test-basic-deploy.sh - Verify basic ValkeyCluster deployment
#
# This test creates a ValkeyCluster CR with 3 replicas and verifies:
#   1. The StatefulSet becomes ready within 120 seconds
#   2. All 6 sub-resources are created (headless svc, client svc, configmap, secret, statefulset, pdb)
#   3. Pod-0 is master (valkey-cli ROLE returns "master")
#   4. Pods 1 and 2 are replicas
#   5. The client service exists
#   6. Ready pod count equals 3
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CR_NAME="test-valkey"
NAMESPACE="default"
TIMEOUT=120

cleanup() {
  echo "[cleanup] Deleting ValkeyCluster CR..."
  kubectl delete -f "$SCRIPT_DIR/sample-cr.yaml" --ignore-not-found -n "$NAMESPACE" || true
  # Wait for resources to be cleaned up
  kubectl wait --for=delete statefulset/"$CR_NAME" -n "$NAMESPACE" --timeout=60s 2>/dev/null || true
}

trap cleanup EXIT

echo "[1/6] Creating ValkeyCluster CR..."
kubectl apply -f "$SCRIPT_DIR/sample-cr.yaml" -n "$NAMESPACE"

echo "[2/6] Waiting for StatefulSet to be ready (timeout: ${TIMEOUT}s)..."
elapsed=0
while [ "$elapsed" -lt "$TIMEOUT" ]; do
  ready=$(kubectl get statefulset "$CR_NAME" -n "$NAMESPACE" -o jsonpath='{.status.readyReplicas}' 2>/dev/null || echo "0")
  desired=$(kubectl get statefulset "$CR_NAME" -n "$NAMESPACE" -o jsonpath='{.spec.replicas}' 2>/dev/null || echo "0")
  if [ "$ready" = "$desired" ] && [ "$desired" = "3" ]; then
    echo "  StatefulSet ready: $ready/$desired"
    break
  fi
  echo "  Waiting... ($ready/$desired ready, ${elapsed}s elapsed)"
  sleep 5
  elapsed=$((elapsed + 5))
done

if [ "$elapsed" -ge "$TIMEOUT" ]; then
  echo "FAIL: StatefulSet did not become ready within ${TIMEOUT}s"
  kubectl get statefulset "$CR_NAME" -n "$NAMESPACE" -o yaml || true
  kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" || true
  exit 1
fi

echo "[3/6] Verifying all 6 sub-resources exist..."
FAIL_COUNT=0

# Headless Service
if kubectl get svc "${CR_NAME}-headless" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: headless service (${CR_NAME}-headless)"
else
  echo "  MISSING: headless service (${CR_NAME}-headless)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

# Client Service
if kubectl get svc "${CR_NAME}-client" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: client service (${CR_NAME}-client)"
else
  echo "  MISSING: client service (${CR_NAME}-client)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

# ConfigMap
if kubectl get configmap "${CR_NAME}-config" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: configmap (${CR_NAME}-config)"
else
  echo "  MISSING: configmap (${CR_NAME}-config)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

# Secret
if kubectl get secret "${CR_NAME}-secret" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: secret (${CR_NAME}-secret)"
else
  echo "  MISSING: secret (${CR_NAME}-secret)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

# StatefulSet
if kubectl get statefulset "$CR_NAME" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: statefulset ($CR_NAME)"
else
  echo "  MISSING: statefulset ($CR_NAME)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

# PodDisruptionBudget
if kubectl get pdb "${CR_NAME}-pdb" -n "$NAMESPACE" &>/dev/null; then
  echo "  OK: poddisruptionbudget (${CR_NAME}-pdb)"
else
  echo "  MISSING: poddisruptionbudget (${CR_NAME}-pdb)"
  FAIL_COUNT=$((FAIL_COUNT + 1))
fi

if [ "$FAIL_COUNT" -gt 0 ]; then
  echo "FAIL: $FAIL_COUNT sub-resource(s) missing"
  exit 1
fi

echo "[4/6] Verifying pod roles (pod-0 = master, pods 1,2 = replica)..."

# Check pod-0 is master
ROLE_0=$(kubectl exec "${CR_NAME}-0" -n "$NAMESPACE" -- valkey-cli ROLE 2>/dev/null | head -1 || echo "unknown")
if [ "$ROLE_0" = "master" ]; then
  echo "  OK: ${CR_NAME}-0 is master"
else
  echo "  FAIL: ${CR_NAME}-0 role is '$ROLE_0', expected 'master'"
  exit 1
fi

# Check pod-1 is replica
ROLE_1=$(kubectl exec "${CR_NAME}-1" -n "$NAMESPACE" -- valkey-cli ROLE 2>/dev/null | head -1 || echo "unknown")
if [ "$ROLE_1" = "slave" ]; then
  echo "  OK: ${CR_NAME}-1 is replica"
else
  echo "  FAIL: ${CR_NAME}-1 role is '$ROLE_1', expected 'slave'"
  exit 1
fi

# Check pod-2 is replica
ROLE_2=$(kubectl exec "${CR_NAME}-2" -n "$NAMESPACE" -- valkey-cli ROLE 2>/dev/null | head -1 || echo "unknown")
if [ "$ROLE_2" = "slave" ]; then
  echo "  OK: ${CR_NAME}-2 is replica"
else
  echo "  FAIL: ${CR_NAME}-2 role is '$ROLE_2', expected 'slave'"
  exit 1
fi

echo "[5/6] Verifying client service exists..."
CLIENT_SVC_TYPE=$(kubectl get svc "${CR_NAME}-client" -n "$NAMESPACE" -o jsonpath='{.spec.type}' 2>/dev/null || echo "")
if [ "$CLIENT_SVC_TYPE" = "ClusterIP" ]; then
  echo "  OK: client service type is ClusterIP"
else
  echo "  FAIL: client service type is '$CLIENT_SVC_TYPE', expected 'ClusterIP'"
  exit 1
fi

echo "[6/6] Verifying ready pod count = 3..."
READY_PODS=$(kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" \
  --field-selector=status.phase=Running -o name 2>/dev/null | wc -l | tr -d ' ')
if [ "$READY_PODS" -eq 3 ]; then
  echo "  OK: $READY_PODS pods running"
else
  echo "  FAIL: $READY_PODS pods running, expected 3"
  kubectl get pods -l "app.kubernetes.io/instance=$CR_NAME" -n "$NAMESPACE" || true
  exit 1
fi

echo "All basic deploy checks passed."
