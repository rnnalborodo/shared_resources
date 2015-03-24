----------------------- MODULE BoundedSemaphore ------------------------
(* Required modules. *)
EXTENDS 
    Naturals,
    TLC

------------------------------------------------------------------------
CONSTANTS
  BOUND

\*ASSUME
\*  /\ BOUND \in Nat /\ BOUND > 0

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
  /\ value <= BOUND 
  /\ value >= 0

Init ==
  /\ value = 0

------------------------------------------------------------------------
V == 
  (* CPRE *)
  /\ value < BOUND
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
