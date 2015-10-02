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
(assert (= x_0_t0 0))
(assert (= x_0_t1 1))
(assert (= x_0_t2 2))
; code assertion
(assert (= x_1_t0 0))

; program order constraints
(assert (< b1 b2))
(assert (< b2 b3))

; constraints from pi nodes
; we read the local value of x (thread t0)
; TODO improve!
(assert (=> (and (< b4 b1) (< b5 b1)) (= x_1_t0 x_0_t0))) 
; we read the value from thread t1
(assert (=> (and (< b4 b2) (< b1 b4) (or (< b5 b4) (< b2 b5))) (= x_1_t0 x_0_t1)))
; we read the value from thread t2
(assert (=> (and (< b5 b2) (< b1 b5) (or (< b2 b4) (< b4 b5))) (= x_1_t0 x_0_t2)))

; the happens before order has to follow one of the traces that we used to produce the encoding
(assert (or 
  (and (< b5 b1) (< b1 b4) (< b4 b2))
  (and (< b4 b1) (< b1 b5) (< b5 b2))
))

; requiring different values for the timestamps of the blocks
(assert (not (= b1 b2)))
(assert (not (= b1 b3)))
(assert (not (= b1 b4)))
(assert (not (= b1 b5)))
(assert (not (= b2 b3)))
(assert (not (= b2 b4)))
(assert (not (= b2 b5)))
(assert (not (= b3 b4)))
(assert (not (= b3 b5)))
(assert (not (= b4 b5)))

(check-sat)
(exit)
