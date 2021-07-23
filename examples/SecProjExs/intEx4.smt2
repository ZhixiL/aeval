(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (
  <= (* 5 (/ (* 3 y) 7)) x1
) (
  > (* 2 y) x2
)))
