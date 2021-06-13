(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (/ y 2) (+ (* (- 3) x1) 1 )
) (
<= (+ (+ (+ (+ (* 3 x1) (/ x4 3)) (* 4 x3)) (/ x2 4)) 4 ) (/ y 3)
)) (
> (+ (+ (* 3 x2) (* (- 5) x1)) (/ x3 2)) (/ y 4)
)
))
