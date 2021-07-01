(assert (forall ((x1 Int) (x2 Int))
(exists ((y Int)) 
(and (>= y x1) (>= (div y 3) (* x2 3)) (or (= y x1) (= y x2)))
)))