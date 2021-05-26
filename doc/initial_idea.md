1)
This can be derived even without distributivity:
A1 \/ A2 -> B1 /\ B2 <: (A1 -> B1) /\ (A2 -> B2)

The reversed one cannot be derived in the ICFP work:
(A1 -> B1) /\ (A2 -> B2) <: (A1 \/ A2) -> (B1 /\ B2)

Although these two can

---------------------------------------------- :: distArrU
(A1 -> B1) /\ (A2 -> B2) <: A1\/A2 -> B1\/B2


---------------------------------------------- :: distArr
(A1 -> B1) /\ (A2 -> B2) <: A1&A2 -> B1&B2


In the other direction, we can
derive  (A1 -> B) /\ (A2 -> B) <: A1 \/ A2 -> B (distArrU)
and    (A -> B1) /\ (A -> B2) <: A -> B1 /\ B2 (distArr)
by (A1 -> B1) /\ (A2 -> B2) <: (A1 \/ A2) -> (B1 /\ B2)


2)
Using transitivity +
(A1 /\ A2) -> B  <: (A1 -> B) \/ (A2 -> B)
A -> B1 \/ B2    <: (A -> B1) \/ (A -> B2)
We *cannot* derive:
(A1 /\ A2) -> (B1 \/ B2) <: (A1 -> B1) \/ (A2 -> B2)
Here is a failed attempt:
(A1 /\ A2) -> (B1 \/ B2)
<:
(A1 /\ A2 -> B1) \/ (A1 /\ A2 -> B2)
<:
(A1 -> B1) \/ (A2 -> B1) \/ (A1 -> B2) \/ (A2 -> B2)
<: {INVALID}
(A1 -> B1) \/ (A2 -> B2)

What we would like is to have a system with either:
(A1 /\ A2) -> (B1 \/ B2) <: (A1 -> B1) \/ (A2 -> B2)     and
A1 \/ A2 -> B1 /\ B2 <: (A1 -> B1) /\ (A2 -> B2)
or
A1 \/ A2 -> B <: (A1 -> B) /\ (A2 -> B)
A -> B1 /\ B2 <: (A -> B1) /\ (A -> B2)    and
(A1 /\ A2) -> B  <: (A1 -> B) \/ (A2 -> B)
A -> B1 \/ B2    <: (A -> B1) \/ (A -> B2)
