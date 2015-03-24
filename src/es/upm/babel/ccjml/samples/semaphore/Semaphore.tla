----------------------- MODULE Semaphore ------------------------
(* Required modules. *)
EXTENDS 
    Naturals,
    TLC

------------------------------------------------------------------------
CONSTANTS
  BOUND

VARIABLES
  value

BoundedSempahore_state == <<value>>

------------------------------------------------------------------------
PrintOp(op) ==
  /\ Print("--------- Step:", TRUE)
  /\ Print(BoundedSempahore_state, TRUE)
  /\ Print(op,TRUE)
  /\ Print(BoundedSempahore_state', TRUE)

------------------------------------------------------------------------
Types ==
  /\ value \in Nat

Invariant ==
  /\ value <= 2 
  /\ value >= 0

Init ==
  /\ value = 0

------------------------------------------------------------------------
V == 
  (* CPRE *)
  /\ value < 2
  (* POST *)
  /\ value' = value + 1
  /\ PrintOp("v()")

------------------------------------------------------------------------
P == 
  (* CPRE *)
  /\ value > 0
  (* POST *)
  /\ value' = value - 1
  /\ PrintOp("p()")

------------------------------------------------------------------------
(* Next-step relation *)
Next ==
  \/ V
  \/ P

------------------------------------------------------------------------
(*Resource specification. *)
Spec == Init /\ [][Next]_BoundedSempahore_state

========================================================================
