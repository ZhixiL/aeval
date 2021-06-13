(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (* 5 y) (+ (/ x1 3) 3 ))
) (
not (= (+ (+ (* 3 x1) (/ x2 2)) (* (- 4) x3)) (* 5 y))
)) (and (
<= (+ (/ x1 3) 2 ) (/ y 4)
) (
>= (* (- 4) x1) (* (- 3) y)
))
))
