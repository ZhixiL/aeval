; pi = (y <= x) && (y > x - 10) && (y != 12) && (4 * y > 12)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (and (
    <= y x
) (
    > y (- x 10)
)) (and (
    not(= (* 3 y) 12)
) (
    > (* 4 y) 12
))))