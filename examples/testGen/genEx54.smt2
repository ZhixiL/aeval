(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
= (* (- 5) y) (+ (+ (+ (/ x1 3) (/ x4 3)) (* (- 5) x3)) (* 3 x2))
) (
> (+ (+ (+ (* (- 4) x2) (/ x1 4)) (* (- 3) x4)) (* 3 x3)) (* (- 5) y)
)
))
