(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (+ (+ (+ (+ (* (- 3) x1) (* 5 x4)) (* (- 4) x3)) (/ x2 2)) 4 ) (/ y 4))
) (
> (/ x1 3) (* (- 3) y)
)) (and (
not (= (* (- 5) y) (+ (+ (+ (* (- 3) x2) (/ x1 4)) (* 5 x3)) 1 ))
) (
> (* (- 3) y) (+ (+ (+ (/ x4 4) (/ x3 3)) (* (- 4) x1)) (/ x2 2))
))
))
