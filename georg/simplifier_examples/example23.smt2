(assert
(let ((.cse7 (+ x_1_6 (- 5 ) )) ) (let ((.cse6 (<= 0 .cse7 )) (.cse5 (<= x_1_6 5 )) ) (let ((.cse3 (<= x_2_6 10 )) (.cse0 (ite (<= (+ x_1_6 (- 4 ) ) 0 ) .cse6 (or (<= .cse7 0 ) .cse5 ) )) ) (let ((.cse1 (and flag_Label_T_2_94_2 (and .cse3 .cse0 ) )) (.cse2 (and flag_Label_T_2_94_2 (and (let ((.cse4 (- x_1_6 )) ) (ite (<= (+ .cse4 6 ) 0 ) .cse5 (or (<= (+ .cse4 5 ) 0 ) .cse6 ) )) .cse3 ) )) ) (ite flag_Label_T_2_94_2 (and (or .cse0 .cse1 .cse2 ) (or .cse3 .cse1 .cse2 ) ) (or .cse1 .cse2 ) )))))
)
