; pi = (y > 4 * x1) /\ (y>= -3 * x2 + 1) /\ (y < x1 + x2)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun y () Int)

(assert (and (and (
    > y (* 4 x1)
) (
    >= y (+ (* (- 3) x2) 1)
)) (
    < y (+ x1 x2)
)))
(check-sat)