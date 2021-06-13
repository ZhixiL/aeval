(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (+ (/ x1 2) (* (- 4) x2)) (* 5 x3)) 3 ) (/ y 2))
) (
> (+ (+ (* (- 5) x3) (* (- 4) x1)) (* 5 x2)) (* (- 4) y)
)) (and (
< (* 3 y) (+ (/ x1 4) (* 4 x2))
) (
< (/ y 2) (+ (+ (* 3 x2) (* 3 x3)) (* 4 x1))
))
))
