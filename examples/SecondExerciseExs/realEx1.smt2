(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)

(assert (and (
  >= (+ x1 x2) (* y 0.5)
) (
  > (* 3.5 y) x1
)))
