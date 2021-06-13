(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
< (+ (+ (+ (+ (/ x1 3) (/ x4 2)) (* (- 4) x3)) (/ x2 4)) 3 ) (* 3 y)
) (
< (* 5 y) (+ (+ (+ (+ (/ x2 3) (* 4 x1)) (/ x4 4)) (* 4 x3)) 4 )
)) (and (
not (= (+ (* 3 x1) 1 ) (/ y 4))
) (
= (/ y 4) (+ (+ (+ (* 4 x2) (* 5 x3)) (/ x1 2)) (* (- 3) x4))
))
))
