;Test for long expression
(declare-fun y () Int)
(declare-fun x () Int)

(assert (and (and (and (and (
    = x (/ y 10)
) (
    = (/ y 12) x
)) (and (
    < (* 12 y) (* x 140) 
) (
    <= (+ x (/ x 15)) (/ y 12)
))) (and (and (
    < (* x 140) (* 12 y)
) (
    not(= (* 17 x) (/ y 14))
)) (and (
    > y 14
) (
    > y x
)))) (and (and (
    not(= y x)
) (
    > (/ y 17) (+ x x)
)) (and (
    >= (* 99999 y) x
) (
    >= (/ y 1) x
)))))