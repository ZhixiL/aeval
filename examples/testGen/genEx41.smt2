(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
<= (+ (+ (+ (* (- 5) x1) (/ x4 3)) (* (- 5) x3)) (* 4 x2)) (* (- 3) y)
) (
= (+ (+ (/ x2 2) (/ x1 4)) 3 ) (* (- 5) y)
)
))
