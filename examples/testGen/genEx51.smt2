(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
<= (+ (+ (/ x1 2) (/ x2 3)) 2 ) (/ y 3)
) (
not (= (/ y 3) (+ (+ (+ (+ (* (- 4) x3) (* 3 x4)) (/ x2 3)) (* 4 x1)) 2 ))
)) (and (
= (+ (+ (* (- 5) x1) (/ x3 2)) (/ x2 2)) (* 4 y)
) (
>= (+ (+ (+ (+ (/ x2 2) (/ x3 3)) (* (- 3) x1)) (* (- 5) x4)) 3 ) (/ y 2)
))
))
