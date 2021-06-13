(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
>= (+ (+ (+ (/ x1 3) (* 3 x4)) (* 3 x3)) (/ x2 3)) (* (- 3) y)
) (
= (/ y 4) (+ (+ (* (- 4) x2) (* (- 3) x1)) 1 )
)
))
