(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)

(assert (and (and (
  >= (+ x1 x2) (* y 1.5)
) (
  >= y (* (- 3.1) x2)
)) (and (
  < (* 0.5 y) x1
) (and (
  > y (- x1 2.1)
) (
  <= y (+ x2 7.1)
)))))
