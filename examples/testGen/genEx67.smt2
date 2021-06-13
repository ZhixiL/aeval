(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (/ x1 3) (/ y 4))
) (
not (= (/ y 4) (+ (+ (* 5 x1) (* 3 x2)) (/ x3 4)))
)) (and (
< (+ (+ (+ (+ (* 3 x3) (* (- 5) x1)) (* 4 x2)) (/ x4 4)) 1 ) (* 5 y)
) (
<= (/ y 4) (+ (+ (* 4 x2) (* 4 x1)) 4 )
))
))
