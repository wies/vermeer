(assert
(let ((.cse17 (- 4 )) ) (let ((.cse10 (<= (+ x_14_1 x_12_1 ) (+ x_10_1 (- 58 ) ) )) (.cse0 (<= (+ x_14_1 x_16_1 x_12_1 ) (+ x_10_1 (- 57 ) ) )) (.cse1 (<= (+ x_14_1 x_7_6 x_16_1 x_12_1 ) (+ x_10_1 (- 21 ) ) )) (.cse15 (<= x_12_1 (+ x_10_1 (- 61 ) ) )) (.cse14 (<= x_10_1 60 )) (.cse16 (let ((.cse18 (+ x_6_6 (- 5 ) )) ) (ite (<= (+ x_6_6 .cse17 ) 0 ) (<= 0 .cse18 ) (or (<= .cse18 0 ) (<= x_6_6 5 ) ) ))) (.cse12 (<= 0 (+ x_3_2 (- 2 ) ) )) (.cse9 (<= 0 (+ x_5_2 (- 3 ) ) )) (.cse11 (<= 0 (+ x_4_2 .cse17 ) )) (.cse13 (ite (<= x_2_2 0 ) (<= 0 (+ x_2_2 (- 1 ) ) ) (<= x_2_2 1 ) )) ) (let ((.cse7 (and .cse10 .cse0 .cse1 .cse15 .cse14 .cse16 .cse12 .cse9 .cse11 .cse13 )) (.cse8 (and .cse0 .cse1 .cse10 .cse15 .cse14 .cse13 .cse16 .cse12 .cse9 .cse11 )) ) (let ((.cse3 (or .cse16 .cse7 .cse8 )) ) (let ((.cse2 (or .cse15 .cse7 .cse8 )) (.cse4 (or (and .cse14 .cse3 ) .cse7 .cse8 )) (.cse5 (or .cse13 .cse7 .cse8 )) (.cse6 (or .cse12 .cse7 .cse8 )) ) (and (or (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 ) .cse7 .cse8 ) (or .cse9 .cse7 .cse8 ) .cse3 (or .cse10 .cse7 .cse8 ) .cse2 .cse4 .cse5 .cse6 (or .cse11 .cse7 .cse8 ) ))))))
)