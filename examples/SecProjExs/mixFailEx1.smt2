(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Int)

(assert (and (and (
  >= (+ x1 x2) (* x2 1.5)
) (
  >= y (* 2 x2)
)) (and (
  < (* 2 y) x1
) (and (
  > y (- x1 4)
) (
  <= y (+ x2 7.1)
)))))
