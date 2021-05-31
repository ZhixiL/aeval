(declare-fun x () Int)
(declare-fun y () Int)

(assert (and (and (
    <= 1 x
) (
    > y (- x 10)
)) (and (
    not(= (* 3 y) 12)
) (
    > (* 4 (* 5 y)) 12
))))