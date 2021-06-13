(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (* 4 y) (+ (+ (+ (+ (/ x1 2) (* 5 x4)) (/ x3 2)) (/ x2 3)) 3 )
) (
<= (/ y 4) (+ (+ (* (- 5) x2) (/ x1 3)) 1 )
)
))
