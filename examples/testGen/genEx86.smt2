(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
not (= (* (- 4) y) (+ (/ x1 3) (/ x2 3)))
) (
> (+ (/ x1 4) 4 ) (* 3 y)
)
))