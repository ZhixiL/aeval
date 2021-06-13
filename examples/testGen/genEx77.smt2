(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (/ y 4) (+ (* 3 x1) (* (- 5) x2))
) (
< (/ y 2) (+ (+ (+ (+ (/ x3 3) (/ x4 4)) (* 4 x2)) (/ x1 4)) 3 )
)
))
