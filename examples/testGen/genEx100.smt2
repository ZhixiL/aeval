(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (+ (+ (+ (* (- 5) x1) (* 5 x4)) (/ x3 4)) (/ x2 3)) 4 ) (/ y 4)
) (
< (* (- 3) y) (+ (+ (+ (+ (/ x2 4) (/ x1 3)) (/ x4 4)) (* 5 x3)) 1 )
)
))
