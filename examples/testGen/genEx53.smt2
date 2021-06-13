(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (/ x1 4) (* (- 5) x2)) (* 5 y)
) (
> (/ x1 3) (/ y 2)
)) (
<= (* 5 y) (+ (+ (+ (+ (* 5 x3) (/ x4 4)) (* 5 x2)) (* 5 x1)) 3 )
)
))
