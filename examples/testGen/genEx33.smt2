(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (* (- 5) x1) (* 4 x2)) 2 ) (/ y 3))
) (
= (* 3 y) (+ (+ (+ (* (- 5) x3) (* 3 x2)) (* 4 x1)) 4 )
)) (and (
= (+ (+ (* 4 x2) (/ x1 2)) (* 5 x3)) (/ y 3)
) (
> (* 4 y) (* 5 x1)
))
))
