(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (/ y 2) (+ (+ (+ (/ x1 3) (/ x2 4)) (* 5 x3)) 4 )
) (
> (+ (/ x1 4) (/ x2 2)) (* 5 y)
)) (
<= (+ (+ (/ x2 2) (/ x1 4)) (* 4 x3)) (/ y 3)
)
))
