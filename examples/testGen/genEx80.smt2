(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (* (- 5) x1) (/ x2 2)) (* 5 y)
) (
not (= (/ y 3) (+ (+ (+ (* (- 4) x3) (* 4 x2)) (/ x1 3)) 4 ))
)
))
