/-
  Sentinel.lean - Integrated Sentinel state machine for Valkey operator

  This module defines the Sentinel functionality integrated directly into the
  operator (Operator-as-Sentinel pattern). Instead of running separate Sentinel
  containers with quorum-based consensus, the operator acts as a single authority
  for failure detection and failover.

  Key simplifications over traditional Redis/Valkey Sentinel:
  - No SDOWN -> ODOWN transition (single authority)
  - No quorum voting (K8s Lease provides leader election)
  - No Sentinel-to-Sentinel gossip
  - Direct failover decision by the operator leader

  State machine:
    Healthy -> SDOWN -> SelectingReplica -> Promoting -> UpdatingService -> Done

  Uses ValkeyClusterSentinelView from Gungnir.K8s for configuration parameters.

  Reference: plans.md Section "Sentinel Integration Pattern"
-/

import Gungnir.K8s.K8s

namespace Gungnir.Sentinel

open Gungnir.K8s

-- Health status of a single Valkey node.
inductive NodeHealth where
  | Healthy
  | Degraded (consecutiveFailures : Nat)
  | SDOWN    -- Subjectively Down (enough consecutive PING failures)
  deriving DecidableEq, Repr

-- Information about a single Valkey node.
-- This extends NodeHealthStatus from K8s types with replication-specific fields
-- needed for replica selection.
structure NodeInfo where
  podName : String
  ip : String
  port : Nat := 6379
  role : ValkeyRole
  health : NodeHealth
  replOffset : Nat        -- replication offset (higher = more data)
  priority : Nat := 100   -- replica-priority (lower = preferred, 0 = never promote)
  runId : String           -- for tiebreaking
  deriving Repr

-- The state of the Sentinel state machine.
inductive SentinelState where
  | Monitoring           -- Normal operation: PINGing nodes
  | FailureDetected      -- Master SDOWN detected
  | SelectingReplica     -- Choosing best replica to promote
  | Promoting            -- Sending REPLICAOF NO ONE to selected replica
  | ReconfiguringReplicas -- Reconfiguring other replicas to follow new master
  | UpdatingService      -- Updating K8s Service selector
  | Completed            -- Failover complete
  | FailoverError (msg : String) -- Failover failed
  deriving Repr

-- The full Sentinel context: config + cluster state.
-- Uses ValkeyClusterSentinelView from K8s types for configuration.
structure SentinelContext where
  config : ValkeyClusterSentinelView
  nodes : List NodeInfo
  sentinelState : SentinelState
  selectedReplica : Option NodeInfo := none
  deriving Repr

-- Detect SDOWN: a node is subjectively down when consecutive PING failures
-- multiplied by the ping interval exceed the down-after threshold.
def detectSDOWN (config : ValkeyClusterSentinelView) (node : NodeInfo) : Bool :=
  match node.health with
  | NodeHealth.Degraded failures =>
    failures * config.pingIntervalMs >= config.downAfterMs
  | NodeHealth.SDOWN => true
  | _ => false

-- Check if any master node is in SDOWN state.
def masterIsDown (nodes : List NodeInfo) : Bool :=
  nodes.any fun n => n.role == ValkeyRole.Master && n.health == NodeHealth.SDOWN

-- Find the current master node.
def findMaster (nodes : List NodeInfo) : Option NodeInfo :=
  nodes.find? fun n => n.role == ValkeyRole.Master

-- Get all replica nodes that are eligible for promotion.
-- Filter out:
-- - Nodes with priority 0 (never promote)
-- - Nodes in SDOWN state
def eligibleReplicas (nodes : List NodeInfo) : List NodeInfo :=
  nodes.filter fun n =>
    n.role == ValkeyRole.Replica &&
    n.priority != 0 &&
    n.health != NodeHealth.SDOWN

-- Replica selection: choose the best replica to promote.
-- Priority order:
-- 1. Lower replica-priority value (higher priority)
-- 2. Higher replication offset (more data)
-- 3. Lexicographically smaller runId (tiebreaker)
def selectBestReplica (replicas : List NodeInfo) : Option NodeInfo :=
  let eligible := replicas.filter fun r => r.priority != 0 && r.health != NodeHealth.SDOWN
  match eligible with
  | [] => none
  | _ =>
    let sorted := eligible.mergeSort fun a b =>
      if a.priority != b.priority then a.priority < b.priority
      else if a.replOffset != b.replOffset then a.replOffset > b.replOffset
      else a.runId < b.runId
    sorted.head?

-- The Sentinel transition function.
-- Given the current context, produce the next context.
def sentinelNext (ctx : SentinelContext) : SentinelContext :=
  match ctx.sentinelState with
  | SentinelState.Monitoring =>
    -- Check if master is down
    if masterIsDown ctx.nodes then
      { ctx with sentinelState := SentinelState.FailureDetected }
    else
      ctx

  | SentinelState.FailureDetected =>
    -- Transition to replica selection
    { ctx with sentinelState := SentinelState.SelectingReplica }

  | SentinelState.SelectingReplica =>
    -- Select the best replica
    let replicas := eligibleReplicas ctx.nodes
    match selectBestReplica replicas with
    | some replica =>
      { ctx with
        sentinelState := SentinelState.Promoting
        selectedReplica := some replica
      }
    | none =>
      { ctx with
        sentinelState := SentinelState.FailoverError "no eligible replica found"
      }

  | SentinelState.Promoting =>
    -- After promotion command sent, move to reconfiguration
    { ctx with sentinelState := SentinelState.ReconfiguringReplicas }

  | SentinelState.ReconfiguringReplicas =>
    -- After reconfiguring replicas, update K8s Service
    { ctx with sentinelState := SentinelState.UpdatingService }

  | SentinelState.UpdatingService =>
    -- After service update, failover is complete
    { ctx with sentinelState := SentinelState.Completed }

  | SentinelState.Completed =>
    -- Terminal state
    ctx

  | SentinelState.FailoverError _ =>
    -- Terminal state
    ctx

-- Check if the Sentinel state machine is in a terminal state.
def sentinelTerminal (state : SentinelState) : Prop :=
  match state with
  | SentinelState.Completed => True
  | SentinelState.FailoverError _ => True
  | _ => False

-- Check if the Sentinel state machine is monitoring (normal operation).
def sentinelMonitoring (state : SentinelState) : Prop :=
  match state with
  | SentinelState.Monitoring => True
  | _ => False

-- SDOWN detection predicate for a specific node (Prop version).
def nodeIsSDOWN (config : ValkeyClusterSentinelView) (node : NodeInfo) : Prop :=
  match node.health with
  | NodeHealth.Degraded failures =>
    failures * config.pingIntervalMs >= config.downAfterMs
  | NodeHealth.SDOWN => True
  | _ => False

-- The Sentinel state machine always makes forward progress (no cycles).
-- This ordering is used to prove termination.
def sentinelStateOrder (s : SentinelState) : Nat :=
  match s with
  | SentinelState.Monitoring            => 0
  | SentinelState.FailureDetected       => 1
  | SentinelState.SelectingReplica      => 2
  | SentinelState.Promoting             => 3
  | SentinelState.ReconfiguringReplicas => 4
  | SentinelState.UpdatingService       => 5
  | SentinelState.Completed             => 6
  | SentinelState.FailoverError _       => 6

end Gungnir.Sentinel
