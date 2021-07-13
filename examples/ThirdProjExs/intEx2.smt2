(assert (forall ((x1 Int) (x2 Int))
(exists ((y Int)) 
(and (< (+ x1 (* (- 2) (+ x1 x2))) 0) (< (let ((a!1 (- (div (* 2 (+ x1 x2)) 4))))
  (+ (div x1 4) a!1)) 0)))))