(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (/ x1 2) (/ x2 2)) (/ y 2))
) (
< (+ (+ (+ (+ (* 5 x3) (* (- 3) x4)) (* 4 x2)) (* 4 x1)) 3 ) (* 5 y)
)) (
< (* 3 y) (+ (+ (+ (* 4 x1) (/ x3 4)) (/ x2 4)) 3 )
)
))
