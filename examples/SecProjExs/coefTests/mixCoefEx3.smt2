(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Real)

(assert (and (and (
  >= x2 (* y 2)
)(
  > (* 3 y) x1
)) (and (and (
  <= y x2
)(
  >= x2 (* 2 x3)
)) (and (
  >= x2 (* 7 y)
) (and (
  <= (* 6 y) (+ x2 x1)
) (and (and (
  > x3 x1
) (
  <= x1 1.4
)) (and (
  < x1 (* y 4)
) (
  > 1.3 x3
))))))))
