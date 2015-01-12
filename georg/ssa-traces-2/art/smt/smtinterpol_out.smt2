(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :produce-unsat-cores false)
(set-option :timeout 10000)
(reset)
(set-option :print-success false)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores false)
(set-logic QF_LIA)
(define-sort Unknown () Int)
(declare-fun x_0_0 () Int)
(declare-fun x_0_1 () Int)
(declare-fun x_0_2 () Int)
(declare-fun x_0_3 () Int)
(declare-fun x_0_4 () Int)
(declare-fun x_0_5 () Int)
(declare-fun x_11_1 () Int)
(declare-fun x_12_1 () Int)
(declare-fun x_12_2 () Int)
(declare-fun x_13_1 () Int)
(declare-fun x_13_2 () Int)
(declare-fun x_14_1 () Int)
(declare-fun x_14_2 () Int)
(declare-fun x_16_1 () Int)
(declare-fun x_17_1 () Int)
(declare-fun x_17_2 () Int)
(declare-fun x_17_3 () Int)
(declare-fun x_17_4 () Int)
(declare-fun x_18_1 () Int)
(declare-fun x_18_2 () Int)
(declare-fun x_19_1 () Int)
(declare-fun x_19_2 () Int)
(declare-fun x_20_1 () Int)
(declare-fun x_20_2 () Int)
(declare-fun x_21_1 () Int)
(declare-fun x_21_2 () Int)
(assert (! (= x_0_0 0 ) :named PS_12))
(assert (! (= x_11_1 2 ) :named PS_20))
(assert (! (=> (= (+ (- 2) x_11_1 ) 0 ) (= x_12_1 0 ) ) :named PS_22))
(assert (! (=> (and (< (+ (- 9) x_12_1 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_13_1 x_0_0 ) ) :named PS_24))
(assert (! (=> (and (< (+ (- 9) x_12_1 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_13_2 (+ 10 x_13_1 ) ) ) :named PS_25))
(assert (! (=> (and (< (+ (- 9) x_12_1 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_0_1 x_13_2 ) ) :named PS_26))
(assert (! (=> (= (+ (- 2) x_11_1 ) 0 ) (= x_12_2 (+ 1 x_12_1 ) ) ) :named PS_28))
(assert (! (=> (and (< (+ (- 9) x_12_2 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_14_1 x_0_1 ) ) :named PS_30))
(assert (! (=> (and (< (+ (- 9) x_12_2 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_14_2 (+ 10 x_14_1 ) ) ) :named PS_31))
(assert (! (=> (and (< (+ (- 9) x_12_2 ) 0 ) (= (+ (- 2) x_11_1 ) 0 ) ) (= x_0_2 x_14_2 ) ) :named PS_32))
(assert (! (= x_16_1 1 ) :named PS_37))
(assert (! (=> (= (+ (- 1) x_16_1 ) 0 ) (= x_17_1 0 ) ) :named PS_39))
(assert (! (=> (and (< (+ (- 9) x_17_1 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_18_1 x_0_2 ) ) :named PS_41))
(assert (! (=> (and (< (+ (- 9) x_17_1 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_18_2 (+ 1 x_18_1 ) ) ) :named PS_42))
(assert (! (=> (and (< (+ (- 9) x_17_1 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_0_3 x_18_2 ) ) :named PS_43))
(assert (! (=> (= (+ (- 1) x_16_1 ) 0 ) (= x_17_2 (+ 1 x_17_1 ) ) ) :named PS_45))
(assert (! (=> (and (< (+ (- 9) x_17_2 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_19_1 x_0_3 ) ) :named PS_47))
(assert (! (=> (and (< (+ (- 9) x_17_2 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_19_2 (+ 1 x_19_1 ) ) ) :named PS_48))
(assert (! (=> (and (< (+ (- 9) x_17_2 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_0_4 x_19_2 ) ) :named PS_49))
(assert (! (=> (= (+ (- 1) x_16_1 ) 0 ) (= x_17_3 (+ 1 x_17_2 ) ) ) :named PS_51))
(assert (! (=> (and (< (+ (- 9) x_17_3 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_20_1 x_0_4 ) ) :named PS_53))
(assert (! (=> (and (< (+ (- 9) x_17_3 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_20_2 (+ 1 x_20_1 ) ) ) :named PS_54))
(assert (! (=> (and (< (+ (- 9) x_17_3 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_0_5 x_20_2 ) ) :named PS_55))
(assert (! (=> (= (+ (- 1) x_16_1 ) 0 ) (= x_17_4 (+ 1 x_17_3 ) ) ) :named PS_57))
(assert (! (=> (and (< (+ (- 9) x_17_4 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_21_1 x_0_5 ) ) :named PS_59))
(assert (! (=> (and (< (+ (- 9) x_17_4 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (= x_21_2 (+ 1 x_21_1 ) ) ) :named PS_60))
(assert (! (=> (and (< (+ (- 9) x_17_4 ) 0 ) (= (+ (- 1) x_16_1 ) 0 ) ) (distinct (+ (- 24) x_21_2 ) 0 ) ) :named PS_62))
(check-sat)
(get-interpolants  PS_12 PS_20 PS_22 PS_24 PS_25 PS_26 PS_28 PS_30 PS_31 PS_32 PS_37 PS_39 PS_41 PS_42 PS_43 PS_45 PS_47 PS_48 PS_49 PS_51 PS_53 PS_54 PS_55 PS_57 PS_59 PS_60 PS_62)
(exit)
