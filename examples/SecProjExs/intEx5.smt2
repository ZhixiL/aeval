(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (
  <= (/ (* 2 y) 3) x1
) (
  > (* 6 y) x2
)))
