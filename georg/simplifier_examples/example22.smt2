(assert
(and (not (= x 5)) (ite (<= (+ x (- 4)) 0) (<= 0 (+ x (- 5))) (or (<= (+ x (- 5)) 0) (<= x 5)))) 
)
