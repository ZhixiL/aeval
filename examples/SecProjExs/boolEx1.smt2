(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun b1 () Bool)
(declare-fun y () Bool)

(assert (and (
  >= (+ x1 x2) (* x1 2)
) (
  and b1 y
)))

