(declare-fun x1 () Int)
(declare-fun x2 () Real)

(assert (and (and (
  >= (+ x1 x2) (* x1 1.5)
) (
  < (* 1 x2) x1
)) (and (
  > x1 (- x2 2.1)
) (
  <= x1 (+ x2 7.1)
))))
