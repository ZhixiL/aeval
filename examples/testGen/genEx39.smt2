(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (/ x1 2) (* 4 y)
) (
> (/ y 2) (/ x1 3)
)) (
>= (* 4 y) (+ (+ (+ (/ x1 4) (/ x2 3)) (/ x3 2)) 2 )
)
))
