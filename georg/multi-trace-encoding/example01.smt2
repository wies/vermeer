(set-option :print-success false)
(set-option :produce-proofs true)
(set-logic QF_LIA)

; declaration of SSA versions of variable x
(declare-fun x_0_t0 () Int)
(declare-fun x_1_t0 () Int)
(declare-fun x_0_t1 () Int)
(declare-fun x_0_t2 () Int)

; declaration of blocks
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun b3 () Int)
(declare-fun b4 () Int)
(declare-fun b5 () Int)

; constraints from single statements (except pi and phi nodes)
(assert (! (= x_0_t0 0) :named CODE_B1))
(assert (! (= x_0_t1 1) :named CODE_B4))
(assert (! (= x_0_t2 2) :named CODE_B5))
; code assertion
(assert (! (= x_1_t0 0) :named CODE_B3))

; program order constraints
(assert (! (< b1 b2) :named ORDER_B1_B2))
(assert (! (< b2 b3) :named ORDER_B2_B3))

; constraints from pi nodes
; we read the local value of x (thread t0)
; TODO improve!
(assert (! (=> (and (< b4 b1) (< b5 b1)) (= x_1_t0 x_0_t0)) :named DATAFLOW_T0_T0)) 
; we read the value from thread t1
(assert (! (=> (and (< b4 b2) (< b1 b4) (or (< b5 b4) (< b2 b5))) (= x_1_t0 x_0_t1)) :named DATAFLOW_T1_T0))
; we read the value from thread t2
(assert (! (=> (and (< b5 b2) (< b1 b5) (or (< b2 b4) (< b4 b5))) (= x_1_t0 x_0_t2)) :named DATAFLOW_T2_T0))

; the happens before order has to follow one of the traces that we used to produce the encoding
(assert (! (or 
  (and (< b5 b1) (< b1 b4) (< b4 b2))
  (and (< b4 b1) (< b1 b5) (< b5 b2))
) :named TRACES))

; requiring different values for the timestamps of the blocks
(assert (! (not (= b1 b2)) :named NEQ_B1_B2)
(assert (! (not (= b1 b3)) :named NEQ_B1_B3)
(assert (! (not (= b1 b4)) :named NEQ_B1_B4)
(assert (! (not (= b1 b5)) :named NEQ_B1_B5)
(assert (! (not (= b2 b3)) :named NEQ_B2_B3)
(assert (! (not (= b2 b4)) :named NEQ_B2_B4)
(assert (! (not (= b2 b5)) :named NEQ_B2_B5)
(assert (! (not (= b3 b4)) :named NEQ_B3_B4)
(assert (! (not (= b3 b5)) :named NEQ_B3_B5)
(assert (! (not (= b4 b5)) :named NEQ_B4_B5)

(check-sat)

(get-interpolants (and CODE_B1 CODE_B4 CODE_B5 ORDER_B1_B2 ORDER_B2_B3 DATAFLOW_T0_T0 DATAFLOW_T1_T0 DATAFLOW_T2_T0 TRACES NEQ_B1_B2 NEQ_B1_B3 NEQ_B1_B4 NEQ_B1_B5 NEQ_B2_B3 NEQ_B2_B4 NEQ_B2_B5 NEQ_B3_B4 NEQ_B3_B5 NEQ_B4_B5) CODE_B3)

(exit)
