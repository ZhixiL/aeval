(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and(
  >= x1 (* 2 y)
) (
  >= (* 3 y) x2 
)))
