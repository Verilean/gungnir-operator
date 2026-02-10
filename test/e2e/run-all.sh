#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PASS=0
FAIL=0

run_test() {
  local name="$1"
  local script="$2"
  echo "=== Running: $name ==="
  if bash "$script"; then
    echo "=== PASS: $name ==="
    PASS=$((PASS + 1))
  else
    echo "=== FAIL: $name ==="
    FAIL=$((FAIL + 1))
  fi
}

run_test "Basic Deploy" "$SCRIPT_DIR/test-basic-deploy.sh"
run_test "Scale" "$SCRIPT_DIR/test-scale.sh"
run_test "Failover" "$SCRIPT_DIR/test-failover.sh"

echo ""
echo "Results: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
