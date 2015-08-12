---- MODULE BoundedBuffer ----
EXTENDS
  Naturals,
  Sequences,
  FiniteSets,
  TLC

CONSTANTS
  ProcSet,
  MAX,
  MAX_FIN,
  Data

VARIABLE
  reqPut,
  reqGet,
  finPut,
  finGet,
  buffer

\*AllSeqs == {<<r,s,t,u,v>> :
\*              r \in Data,
\*              s \in Data,
\*              t \in Data,
\*              u \in Data,
\*              v \in Data}
(*
              w \in Data,
              x \in Data,
              y \in Data,
              z \in Data}
*)

PrintState == TRUE (*\/ Print(<<reqPut,reqGet,finPut,finGet,buffer>>, TRUE)*)

\*AllSeq(n) == {SubSeq(s,1,i) : s \in AllSeqs, i \in (1..n)}

Invariant ==
  /\ buffer \in Seq(Data)
  /\ Len(buffer) <= MAX

Init ==
  /\ buffer = <<>>
  /\ reqPut = {}
  /\ finPut = <<>>
  /\ reqGet = {}
  /\ finGet = <<>>

PIDReq ==
  {r[1] : r \in reqPut} \union {r[1] : r \in reqGet}

PutReq(p,d) ==
  /\ p \in ProcSet
  /\ d \in Seq(Data)
  /\ p \notin PIDReq
  /\ reqPut' = reqPut \union {<<p,d>>}
  /\ UNCHANGED finPut
  /\ UNCHANGED reqGet
  /\ UNCHANGED finGet
  /\ UNCHANGED buffer
  /\ PrintState

GetReq(p,n) ==
  /\ p \in ProcSet
  /\ n \in Nat
  /\ p \notin PIDReq
  /\ UNCHANGED reqPut
  /\ UNCHANGED finPut
  /\ reqGet' = reqGet \union {<<p,n>>}
  /\ UNCHANGED finGet
  /\ UNCHANGED buffer
  /\ PrintState

PutFin ==
  \E r \in reqPut :
    /\ Len(finPut) < MAX_FIN
    /\ Len(r[2]) <= MAX - Len(buffer)
    /\ buffer' = buffer \o r[2]
    /\ reqPut' = {s \in reqPut : s # r}
    /\ finPut' = Append(finPut,r)
    /\ UNCHANGED reqGet
    /\ UNCHANGED finGet
    /\ PrintState

GetFin ==
  \E r \in reqGet :
    /\ Len(finGet) < MAX_FIN
    /\ r[2] <= Len(buffer)
    /\ buffer' = SubSeq(buffer,r[2]+1,Len(buffer))
    /\ UNCHANGED reqPut
    /\ UNCHANGED finPut
    /\ reqGet' = {s \in reqGet : s # r}
    /\ finGet' = Append(finGet,r)
    /\ PrintState

Next ==
  \/ \E p \in ProcSet, d \in AllSeq(1) : PutReq(p,d)
  \/ \E p \in ProcSet, n \in (0..MAX) : GetReq(p,n)
  \/ PutFin
  \/ GetFin

====
