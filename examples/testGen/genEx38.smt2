(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (+ (+ (* (- 5) x1) (* (- 3) x4)) (* (- 3) x3)) (* (- 5) x2)) 4 ) (/ y 3))
) (
> (* (- 5) y) (+ (+ (+ (+ (/ x2 3) (* (- 4) x1)) (* 4 x4)) (* (- 4) x3)) 4 )
)) (and (
<= (+ (+ (+ (+ (* 3 x2) (/ x3 2)) (* (- 4) x1)) (/ x4 4)) 3 ) (/ y 3)
) (
>= (* (- 3) y) (+ (* (- 3) x2) (/ x1 2))
))
))
