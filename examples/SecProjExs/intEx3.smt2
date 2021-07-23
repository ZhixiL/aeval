(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (and (and (
  >= (+ x1 x2) (/ y 3)
) (
  >= y (* 3 x2)
)) (and (
  < (* 2 y) x1
) (and (
  > y (- x1 2)
) (
  <= y (+ x2 7)
)))))
