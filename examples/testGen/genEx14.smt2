(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (/ x1 4) (/ y 3))
) (
>= (* (- 4) x1) (* 4 y)
)) (
>= (+ (/ x1 4) 1 ) (/ y 2)
)
))
