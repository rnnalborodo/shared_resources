---------------------------- MODULE Plant -----------------------------
(* Required modules. *)
LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC

------------------------------------------------------------------------
(* Declaration of constants: specification is parameterised on this constants *)
CONSTANTS
  MAX_CRANES,
  MIN_W_CRANE,
  MAX_W_CRANE,
  MAX_W_CONTAINER

ASSUME
  (* Properties on constants: mainly type information *)
  /\ MAX_CRANES \in Nat /\ MAX_CRANES > 0
  /\ MIN_W_CRANE \in Nat /\ MIN_W_CRANE > 0
  /\ MAX_W_CRANE \in Nat /\ MIN_W_CRANE <= MAX_W_CRANE
  /\ MAX_W_CONTAINER \in Nat

------------------------------------------------------------------------
(* Variables to represent resource state *)
VARIABLES
  weight,
  state,
  accessing,
  cranes_full

Plant_state == <<weight,state,accessing,cranes_full>>

------------------------------------------------------------------------
(* Representation of types. *)
Weight == (MIN_W_CRANE .. MAX_W_CRANE)

Crane_Id == (1 .. MAX_CRANES)

State_Ty == {"ready", "to_replace", "replacing"}

------------------------------------------------------------------------
(* Auxiliary action to print state transitions during checking. *)
PrintOp(op) == TRUE
(*
  /\ Print("Step:", TRUE)
  /\ Print(Plant_state, TRUE)
  /\ Print(op,TRUE)
  /\ Print(Plant_state', TRUE)
*)

------------------------------------------------------------------------
(* Type of variables (invariante) *)
Types ==
  /\ weight \in Nat
  /\ state \in State_Ty
  /\ accessing \in Nat
  /\ cranes_full \in Nat

------------------------------------------------------------------------
(* Resource invariant *)
Invariant ==
  /\ weight <= MAX_W_CONTAINER
  /\ accessing <= MAX_CRANES
  /\ cranes_full <= MAX_CRANES

------------------------------------------------------------------------
(* Initial state of the resource *)
Init ==
  /\ weight = 0
  /\ state = "ready"
  /\ accessing = 0
  /\ cranes_full = 0

------------------------------------------------------------------------
------------------------------------------------------------------------
(* Resource operations (no information about "protocols") *)

------------------------------------------------------------------------
Prepare_Replacement ==
  (* CPRE *)
  /\ state = "to_replace"
  /\ accessing = 0
  (* POST *)
  /\ UNCHANGED weight
  /\ state' = "replacing"
  /\ accessing' = 0
  /\ UNCHANGED cranes_full
  /\ PrintOp("Prepare_Replacement")

------------------------------------------------------------------------
Notify_Replacement ==
  (* CPRE *)
  /\ TRUE
  (* POST *)
  /\ weight' = 0
  /\ state' = "ready"
  /\ accessing' = 0
  /\ cranes_full' = 0
  /\ PrintOp("Notify_Replacement")

------------------------------------------------------------------------
Notify_Weight(w) ==
  (* Type checking *)
  /\ w \in Weight
  (* PRE *)
  /\ w <= MAX_W_CRANE
  (* CPRE *)
  /\ state # "replacing"
  (* POST *)
  /\ UNCHANGED weight
  /\ weight + w > MAX_W_CONTAINER => cranes_full' = cranes_full + 1
  /\ weight + w =< MAX_W_CONTAINER => UNCHANGED cranes_full
  /\ cranes_full' = MAX_CRANES => state' = "to_replace"
  /\ cranes_full' # MAX_CRANES => UNCHANGED state
  /\ UNCHANGED accessing
  /\ PrintOp(<<"Notify_Weight",w>>)

------------------------------------------------------------------------
(* Operation used to illustrate translation *)

TYPE_Increment_Weight(w) == w \in Weight

PRE_Increment_Weight(w) == w <= MAX_W_CRANE

CPRE_Increment_Weight(w) ==
  /\ weight + w =< MAX_W_CONTAINER
  /\ state # "replacing"
  /\ accessing < MAX_CRANES  (* Added after TLC found a violation of the invariant *)

POST_Increment_Weight(w) == 
  /\ weight' = weight + w
  /\ UNCHANGED state
  /\ accessing' = accessing + 1
  /\ UNCHANGED cranes_full

Increment_Weight(w) ==
  /\ TYPE_Increment_Weight(w) 
  /\ PRE_Increment_Weight(w) 
  /\ CPRE_Increment_Weight(w) 
  /\ POST_Increment_Weight(w) 
  /\ PrintOp(<<"Increment_Weight",w>>)

------------------------------------------------------------------------
Notify_Drop ==
  (* CPRE *)
  /\ TRUE
  /\ accessing > 0 (* Added after TLC found a violation of the invariant *)
  (* POST *)
  /\ UNCHANGED weight
  /\ UNCHANGED state
  /\ accessing' = accessing - 1
  /\ UNCHANGED cranes_full
  /\ PrintOp("Notify_Drop")

------------------------------------------------------------------------
(* Next-step relation *)
Next ==
  \/ Prepare_Replacement
  \/ Notify_Replacement
  \/ \E w \in Weight : Notify_Weight(w)
  \/ \E w \in Weight : Increment_Weight(w)
  \/ Notify_Drop

------------------------------------------------------------------------
(*Resource specification. *)
Spec == Init /\ [][Next]_Plant_state

========================================================================
