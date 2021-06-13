(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (+ (+ (* (- 5) x1) (/ x2 4)) (/ x3 3)) 2 ) (* 4 y)
) (
<= (/ y 4) (+ (+ (+ (* (- 5) x3) (/ x1 4)) (* (- 3) x2)) (/ x4 4))
)
))
