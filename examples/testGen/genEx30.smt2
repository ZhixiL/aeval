(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (+ (+ (+ (/ x1 3) (* 5 x4)) (* 4 x3)) (* 5 x2)) (* (- 5) y)
) (
not (= (+ (+ (/ x2 4) (/ x1 4)) 3 ) (/ y 2))
)) (and (
= (/ y 3) (* (- 5) x1)
) (
not (= (+ (+ (/ x1 2) (* (- 3) x2)) 1 ) (/ y 2))
))
))
