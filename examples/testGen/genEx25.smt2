(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
>= (* (- 3) y) (+ (+ (+ (/ x1 2) (/ x2 2)) (/ x3 2)) 2 )
) (
> (* 3 y) (/ x1 3)
)) (
< (/ y 2) (+ (+ (* 3 x3) (/ x1 2)) (* (- 3) x2))
)
))
