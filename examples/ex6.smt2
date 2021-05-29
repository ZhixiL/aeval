; pi = (x <= y) && (x > y - 10) && (x < 12) && (x + y > 12)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (and (
    <= x y
) (
    > x (- y 10)
)) (and (
    > x 12
) (
    > (+ x y) 12
))))