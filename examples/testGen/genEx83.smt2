(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (* (- 5) y) (+ (+ (+ (/ x1 4) (* (- 4) x2)) (/ x3 2)) 3 ))
) (
= (+ (+ (/ x1 2) (/ x2 3)) 2 ) (* 4 y)
)) (
< (* 5 y) (+ (+ (+ (* (- 3) x2) (/ x1 2)) (/ x3 3)) 4 )
)
))
