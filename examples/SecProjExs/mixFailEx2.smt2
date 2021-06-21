(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Int)

(assert (and (and (
  > x1 x2
) (
  > y (+ x1 4.1)
)) (and (
  <= y (- x1 5.3)
) (and (
  < y (+ 4.5 x2)
) (
  >= y (* x1 3.1)
)))))
