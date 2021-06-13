(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
<= (+ (+ (+ (+ (* (- 5) x1) (* (- 4) x4)) (* 5 x3)) (/ x2 4)) 4 ) (* 4 y)
) (
<= (/ x1 2) (/ y 2)
)) (and (
<= (/ y 2) (+ (+ (* 5 x2) (/ x1 4)) 3 )
) (
= (+ (+ (+ (+ (/ x1 3) (* 5 x3)) (* (- 3) x4)) (* (- 3) x2)) 1 ) (* 3 y)
))
))
