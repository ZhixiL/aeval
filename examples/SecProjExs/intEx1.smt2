(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (
  >= (+ x1 x2) (* y 2)
) (
  > (* 4 y) x1
)))
