(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
>= (/ y 4) (+ (+ (* (- 5) x1) (/ x2 3)) (/ x3 4))
) (
<= (+ (/ x1 3) 4 ) (* (- 5) y)
)) (and (
< (+ (/ x1 3) 3 ) (/ y 3)
) (
< (* (- 3) y) (+ (+ (* 4 x3) (/ x1 3)) (* 5 x2))
))
))
