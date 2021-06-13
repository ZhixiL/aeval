(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (+ (+ (/ x1 2) (/ x4 3)) (* 3 x3)) (* (- 4) x2)) (/ y 2)
) (
> (* (- 3) y) (+ (* (- 4) x1) 3 )
)
))
