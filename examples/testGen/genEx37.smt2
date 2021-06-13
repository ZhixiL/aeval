(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (+ (/ x1 4) (* (- 3) x2)) (/ x3 2)) 3 ) (/ y 4))
) (
>= (/ x1 2) (/ y 4)
)) (and (
>= (+ (+ (+ (* (- 4) x3) (* (- 3) x1)) (* (- 5) x2)) 1 ) (* 3 y)
) (
<= (* (- 5) y) (+ (+ (/ x1 3) (* (- 5) x3)) (/ x2 4))
))
))
