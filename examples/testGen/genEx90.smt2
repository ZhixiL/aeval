(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (* (- 4) x1) (* (- 3) x2)) (* (- 4) y)
) (
not (= (+ (+ (/ x1 4) (* 5 x2)) 1 ) (/ y 2))
)
))
