;x1 + x2 < y /\ (x1 < 7 \/ x2 + 9 = y) /\ (y < x1 + 4 \/ x2 > x1 - 5 * y)
(declare-fun y () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)

(assert (and (< (+ x1 x2) y) (and (or (< x1 7.0) (= (+ x2 9.0) y)) (or (< y (+ x1 4.2)) (> x2 (- x1 (* 5.3 y)))))))