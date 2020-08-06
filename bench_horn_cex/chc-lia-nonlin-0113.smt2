;; Original file: id_i15_o15_false-unreach-call_true-termination.c.smt2
(set-logic HORN)
(set-info :source "CHC Constraint Logic: QF_LIA
                   Contains non-linear Horn clauses: true")
(declare-fun id_L6-1 (Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startENTRY (Int Int Int Int Int Bool) Bool)
(declare-fun id_idFINAL (Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L12 (Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L11-1 (Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startFINAL (Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L11 (Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L9 (Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L13 (Int Int Int Int Int Bool) Bool)
(declare-fun id_L6 (Int Int Int Int Bool) Bool)
(declare-fun id_idEXIT (Int Int Int Int Bool) Bool)
(declare-fun id_L5 (Int Int Int Int Bool) Bool)
(declare-fun id_idENTRY (Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startEXIT (Int Int Int Int Int Bool) Bool)
(assert (forall ((hhv_ULTIMATE.start_L11_0_Int Int) (hhv_ULTIMATE.start_L11_1_Int Int) (hhv_ULTIMATE.start_L11_2_Int Int) (hhv_ULTIMATE.start_L11_3_Int Int) (hhv_ULTIMATE.start_L11_4_Int Int) (hhv_ULTIMATE.start_L11_5_Bool Bool) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_5_Bool Bool)) (=> (and (ULTIMATE.start_ULTIMATE.startENTRY hbv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int hhv_ULTIMATE.start_L11_1_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int hhv_ULTIMATE.start_L11_5_Bool) (or (= hhv_ULTIMATE.start_L11_3_Int 15) hhv_ULTIMATE.start_L11_5_Bool)) (ULTIMATE.start_L11 hhv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_L11_2_Int hhv_ULTIMATE.start_L11_3_Int hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_5_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L12_0_Int Int) (hhv_ULTIMATE.start_L12_1_Int Int) (hhv_ULTIMATE.start_L12_2_Int Int) (hhv_ULTIMATE.start_L12_3_Int Int) (hhv_ULTIMATE.start_L12_4_Int Int) (hhv_ULTIMATE.start_L12_5_Bool Bool) (hbv_ULTIMATE.start_L11-1_0_Int Int) (hbv_ULTIMATE.start_L11-1_1_Int Int) (hbv_ULTIMATE.start_L11-1_2_Int Int) (hbv_ULTIMATE.start_L11-1_3_Int Int) (hbv_ULTIMATE.start_L11-1_4_Int Int) (hbv_ULTIMATE.start_L11-1_5_Bool Bool)) (=> (and (ULTIMATE.start_L11-1 hbv_ULTIMATE.start_L11-1_0_Int hhv_ULTIMATE.start_L12_1_Int hhv_ULTIMATE.start_L12_2_Int hhv_ULTIMATE.start_L12_3_Int hbv_ULTIMATE.start_L11-1_4_Int hhv_ULTIMATE.start_L12_5_Bool) (or hhv_ULTIMATE.start_L12_5_Bool (and (<= hbv_ULTIMATE.start_L11-1_0_Int 2147483647) (= hhv_ULTIMATE.start_L12_4_Int hbv_ULTIMATE.start_L11-1_0_Int) (<= 0 (+ hbv_ULTIMATE.start_L11-1_0_Int 2147483648))))) (ULTIMATE.start_L12 hhv_ULTIMATE.start_L12_0_Int hhv_ULTIMATE.start_L12_1_Int hhv_ULTIMATE.start_L12_2_Int hhv_ULTIMATE.start_L12_3_Int hhv_ULTIMATE.start_L12_4_Int hhv_ULTIMATE.start_L12_5_Bool))))
(assert (forall ((hhv_id_L5_0_Int Int) (hhv_id_L5_1_Int Int) (hhv_id_L5_2_Int Int) (hhv_id_L5_3_Int Int) (hhv_id_L5_4_Bool Bool) (hbv_id_idENTRY_0_Int Int) (hbv_id_idENTRY_1_Int Int) (hbv_id_idENTRY_2_Int Int) (hbv_id_idENTRY_3_Int Int) (hbv_id_idENTRY_4_Bool Bool)) (=> (and (id_idENTRY hhv_id_L5_0_Int hhv_id_L5_1_Int hbv_id_idENTRY_2_Int hhv_id_L5_3_Int hhv_id_L5_4_Bool) (or (= hhv_id_L5_2_Int hhv_id_L5_3_Int) hhv_id_L5_4_Bool)) (id_L5 hhv_id_L5_0_Int hhv_id_L5_1_Int hhv_id_L5_2_Int hhv_id_L5_3_Int hhv_id_L5_4_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L13_0_Int Int) (hhv_ULTIMATE.start_L13_1_Int Int) (hhv_ULTIMATE.start_L13_2_Int Int) (hhv_ULTIMATE.start_L13_3_Int Int) (hhv_ULTIMATE.start_L13_4_Int Int) (hhv_ULTIMATE.start_L13_5_Bool Bool) (hbv_ULTIMATE.start_L12_0_Int Int) (hbv_ULTIMATE.start_L12_1_Int Int) (hbv_ULTIMATE.start_L12_2_Int Int) (hbv_ULTIMATE.start_L12_3_Int Int) (hbv_ULTIMATE.start_L12_4_Int Int) (hbv_ULTIMATE.start_L12_5_Bool Bool)) (=> (and (or hhv_ULTIMATE.start_L13_5_Bool (= hhv_ULTIMATE.start_L13_4_Int 15)) (ULTIMATE.start_L12 hhv_ULTIMATE.start_L13_0_Int hhv_ULTIMATE.start_L13_1_Int hhv_ULTIMATE.start_L13_2_Int hhv_ULTIMATE.start_L13_3_Int hhv_ULTIMATE.start_L13_4_Int hhv_ULTIMATE.start_L13_5_Bool)) (ULTIMATE.start_L13 hhv_ULTIMATE.start_L13_0_Int hhv_ULTIMATE.start_L13_1_Int hhv_ULTIMATE.start_L13_2_Int hhv_ULTIMATE.start_L13_3_Int hhv_ULTIMATE.start_L13_4_Int hhv_ULTIMATE.start_L13_5_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L9_0_Int Int) (hhv_ULTIMATE.start_L9_1_Int Int) (hhv_ULTIMATE.start_L9_2_Int Int) (hhv_ULTIMATE.start_L9_3_Int Int) (hhv_ULTIMATE.start_L9_4_Int Int) (hhv_ULTIMATE.start_L9_5_Bool Bool) (hbv_ULTIMATE.start_L12_0_Int Int) (hbv_ULTIMATE.start_L12_1_Int Int) (hbv_ULTIMATE.start_L12_2_Int Int) (hbv_ULTIMATE.start_L12_3_Int Int) (hbv_ULTIMATE.start_L12_4_Int Int) (hbv_ULTIMATE.start_L12_5_Bool Bool)) (=> (and (or (not (= hhv_ULTIMATE.start_L9_4_Int 15)) hhv_ULTIMATE.start_L9_5_Bool) (ULTIMATE.start_L12 hhv_ULTIMATE.start_L9_0_Int hhv_ULTIMATE.start_L9_1_Int hhv_ULTIMATE.start_L9_2_Int hhv_ULTIMATE.start_L9_3_Int hhv_ULTIMATE.start_L9_4_Int hhv_ULTIMATE.start_L9_5_Bool)) (ULTIMATE.start_L9 hhv_ULTIMATE.start_L9_0_Int hhv_ULTIMATE.start_L9_1_Int hhv_ULTIMATE.start_L9_2_Int hhv_ULTIMATE.start_L9_3_Int hhv_ULTIMATE.start_L9_4_Int hhv_ULTIMATE.start_L9_5_Bool))))
(assert (forall ((hhv_id_idFINAL_0_Int Int) (hhv_id_idFINAL_1_Int Int) (hhv_id_idFINAL_2_Int Int) (hhv_id_idFINAL_3_Int Int) (hhv_id_idFINAL_4_Bool Bool) (hbv_id_L5_0_Int Int) (hbv_id_L5_1_Int Int) (hbv_id_L5_2_Int Int) (hbv_id_L5_3_Int Int) (hbv_id_L5_4_Bool Bool)) (=> (and (id_L5 hbv_id_L5_0_Int hhv_id_idFINAL_1_Int hhv_id_idFINAL_2_Int hhv_id_idFINAL_3_Int hhv_id_idFINAL_4_Bool) (or hhv_id_idFINAL_4_Bool (and (= hhv_id_idFINAL_0_Int 0) (= 0 hhv_id_idFINAL_2_Int)))) (id_idFINAL hhv_id_idFINAL_0_Int hhv_id_idFINAL_1_Int hhv_id_idFINAL_2_Int hhv_id_idFINAL_3_Int hhv_id_idFINAL_4_Bool))))
(assert (forall ((hhv_id_L6_0_Int Int) (hhv_id_L6_1_Int Int) (hhv_id_L6_2_Int Int) (hhv_id_L6_3_Int Int) (hhv_id_L6_4_Bool Bool) (hbv_id_L5_0_Int Int) (hbv_id_L5_1_Int Int) (hbv_id_L5_2_Int Int) (hbv_id_L5_3_Int Int) (hbv_id_L5_4_Bool Bool)) (=> (and (id_L5 hhv_id_L6_0_Int hhv_id_L6_1_Int hhv_id_L6_2_Int hhv_id_L6_3_Int hhv_id_L6_4_Bool) (or hhv_id_L6_4_Bool (not (= 0 hhv_id_L6_2_Int)))) (id_L6 hhv_id_L6_0_Int hhv_id_L6_1_Int hhv_id_L6_2_Int hhv_id_L6_3_Int hhv_id_L6_4_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool Bool) (hbv_ULTIMATE.start_L13_0_Int Int) (hbv_ULTIMATE.start_L13_1_Int Int) (hbv_ULTIMATE.start_L13_2_Int Int) (hbv_ULTIMATE.start_L13_3_Int Int) (hbv_ULTIMATE.start_L13_4_Int Int) (hbv_ULTIMATE.start_L13_5_Bool Bool)) (=> (and (ULTIMATE.start_L13 hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hbv_ULTIMATE.start_L13_5_Bool) hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool) (ULTIMATE.start_ULTIMATE.startEXIT hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L9_0_Int Int) (hhv_ULTIMATE.start_L9_1_Int Int) (hhv_ULTIMATE.start_L9_2_Int Int) (hhv_ULTIMATE.start_L9_3_Int Int) (hhv_ULTIMATE.start_L9_4_Int Int) (hhv_ULTIMATE.start_L9_5_Bool Bool) (hbv_ULTIMATE.start_L13_0_Int Int) (hbv_ULTIMATE.start_L13_1_Int Int) (hbv_ULTIMATE.start_L13_2_Int Int) (hbv_ULTIMATE.start_L13_3_Int Int) (hbv_ULTIMATE.start_L13_4_Int Int) (hbv_ULTIMATE.start_L13_5_Bool Bool)) (=> (and (ULTIMATE.start_L13 hhv_ULTIMATE.start_L9_0_Int hhv_ULTIMATE.start_L9_1_Int hhv_ULTIMATE.start_L9_2_Int hhv_ULTIMATE.start_L9_3_Int hhv_ULTIMATE.start_L9_4_Int hhv_ULTIMATE.start_L9_5_Bool) hhv_ULTIMATE.start_L9_5_Bool) (ULTIMATE.start_L9 hhv_ULTIMATE.start_L9_0_Int hhv_ULTIMATE.start_L9_1_Int hhv_ULTIMATE.start_L9_2_Int hhv_ULTIMATE.start_L9_3_Int hhv_ULTIMATE.start_L9_4_Int hhv_ULTIMATE.start_L9_5_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Bool Bool) (hbv_ULTIMATE.start_L9_0_Int Int) (hbv_ULTIMATE.start_L9_1_Int Int) (hbv_ULTIMATE.start_L9_2_Int Int) (hbv_ULTIMATE.start_L9_3_Int Int) (hbv_ULTIMATE.start_L9_4_Int Int) (hbv_ULTIMATE.start_L9_5_Bool Bool)) (=> (and (or hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Bool (= hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int)) (ULTIMATE.start_L9 hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int hbv_ULTIMATE.start_L9_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Bool)) (ULTIMATE.start_ULTIMATE.startFINAL hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Bool))))
(assert (forall ((hhv_id_idEXIT_0_Int Int) (hhv_id_idEXIT_1_Int Int) (hhv_id_idEXIT_2_Int Int) (hhv_id_idEXIT_3_Int Int) (hhv_id_idEXIT_4_Bool Bool) (hbv_id_idFINAL_0_Int Int) (hbv_id_idFINAL_1_Int Int) (hbv_id_idFINAL_2_Int Int) (hbv_id_idFINAL_3_Int Int) (hbv_id_idFINAL_4_Bool Bool)) (=> (id_idFINAL hhv_id_idEXIT_0_Int hhv_id_idEXIT_1_Int hhv_id_idEXIT_2_Int hhv_id_idEXIT_3_Int hhv_id_idEXIT_4_Bool) (id_idEXIT hhv_id_idEXIT_0_Int hhv_id_idEXIT_1_Int hhv_id_idEXIT_2_Int hhv_id_idEXIT_3_Int hhv_id_idEXIT_4_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool Bool) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_5_Bool Bool)) (=> (ULTIMATE.start_ULTIMATE.startFINAL hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool) (ULTIMATE.start_ULTIMATE.startEXIT hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L11-1_0_Int Int) (hhv_ULTIMATE.start_L11-1_1_Int Int) (hhv_ULTIMATE.start_L11-1_2_Int Int) (hhv_ULTIMATE.start_L11-1_3_Int Int) (hhv_ULTIMATE.start_L11-1_4_Int Int) (hhv_ULTIMATE.start_L11-1_5_Bool Bool) (hbv_ULTIMATE.start_L11_0_Int Int) (hbv_ULTIMATE.start_L11_1_Int Int) (hbv_ULTIMATE.start_L11_2_Int Int) (hbv_ULTIMATE.start_L11_3_Int Int) (hbv_ULTIMATE.start_L11_4_Int Int) (hbv_ULTIMATE.start_L11_5_Bool Bool) (hbv_id_idEXIT_0_Int Int) (hbv_id_idEXIT_1_Int Int) (hbv_id_idEXIT_2_Int Int) (hbv_id_idEXIT_3_Int Int) (hbv_id_idEXIT_4_Bool Bool)) (=> (and (id_idEXIT hbv_id_idEXIT_0_Int hbv_id_idEXIT_1_Int hbv_id_idEXIT_2_Int hbv_id_idEXIT_3_Int hbv_id_idEXIT_4_Bool) (= hbv_id_idEXIT_3_Int hhv_ULTIMATE.start_L11-1_3_Int) (let ((.cse0 (or hbv_id_idEXIT_4_Bool hbv_ULTIMATE.start_L11_5_Bool))) (or (and .cse0 hhv_ULTIMATE.start_L11-1_5_Bool) (and (not .cse0) (not hhv_ULTIMATE.start_L11-1_5_Bool)))) (ULTIMATE.start_L11 hbv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11-1_1_Int hhv_ULTIMATE.start_L11-1_2_Int hhv_ULTIMATE.start_L11-1_3_Int hhv_ULTIMATE.start_L11-1_4_Int hbv_ULTIMATE.start_L11_5_Bool) (= hhv_ULTIMATE.start_L11-1_0_Int hbv_id_idEXIT_0_Int)) (ULTIMATE.start_L11-1 hhv_ULTIMATE.start_L11-1_0_Int hhv_ULTIMATE.start_L11-1_1_Int hhv_ULTIMATE.start_L11-1_2_Int hhv_ULTIMATE.start_L11-1_3_Int hhv_ULTIMATE.start_L11-1_4_Int hhv_ULTIMATE.start_L11-1_5_Bool))))
(assert (forall ((hhv_id_L6-1_0_Int Int) (hhv_id_L6-1_1_Int Int) (hhv_id_L6-1_2_Int Int) (hhv_id_L6-1_3_Int Int) (hhv_id_L6-1_4_Bool Bool) (hbv_id_L6_0_Int Int) (hbv_id_L6_1_Int Int) (hbv_id_L6_2_Int Int) (hbv_id_L6_3_Int Int) (hbv_id_L6_4_Bool Bool) (hbv_id_idEXIT_0_Int Int) (hbv_id_idEXIT_1_Int Int) (hbv_id_idEXIT_2_Int Int) (hbv_id_idEXIT_3_Int Int) (hbv_id_idEXIT_4_Bool Bool)) (=> (and (id_L6 hhv_id_L6-1_0_Int hbv_id_L6_1_Int hhv_id_L6-1_2_Int hhv_id_L6-1_3_Int hbv_id_L6_4_Bool) (id_idEXIT hbv_id_idEXIT_0_Int hbv_id_idEXIT_1_Int hbv_id_idEXIT_2_Int hbv_id_idEXIT_3_Int hbv_id_idEXIT_4_Bool) (= hbv_id_idEXIT_3_Int (+ hhv_id_L6-1_2_Int (- 1))) (= hhv_id_L6-1_1_Int hbv_id_idEXIT_0_Int) (let ((.cse0 (or hbv_id_idEXIT_4_Bool hbv_id_L6_4_Bool))) (or (and .cse0 hhv_id_L6-1_4_Bool) (and (not hhv_id_L6-1_4_Bool) (not .cse0))))) (id_L6-1 hhv_id_L6-1_0_Int hhv_id_L6-1_1_Int hhv_id_L6-1_2_Int hhv_id_L6-1_3_Int hhv_id_L6-1_4_Bool))))
(assert (forall ((hhv_id_idFINAL_0_Int Int) (hhv_id_idFINAL_1_Int Int) (hhv_id_idFINAL_2_Int Int) (hhv_id_idFINAL_3_Int Int) (hhv_id_idFINAL_4_Bool Bool) (hbv_id_L6-1_0_Int Int) (hbv_id_L6-1_1_Int Int) (hbv_id_L6-1_2_Int Int) (hbv_id_L6-1_3_Int Int) (hbv_id_L6-1_4_Bool Bool)) (=> (and (id_L6-1 hbv_id_L6-1_0_Int hbv_id_L6-1_1_Int hhv_id_idFINAL_2_Int hhv_id_idFINAL_3_Int hhv_id_idFINAL_4_Bool) (or hhv_id_idFINAL_4_Bool (and (= hhv_id_idFINAL_0_Int (+ hbv_id_L6-1_1_Int 1)) (<= 0 (+ hbv_id_L6-1_1_Int 2147483648)) (<= hbv_id_L6-1_1_Int 2147483647)))) (id_idFINAL hhv_id_idFINAL_0_Int hhv_id_idFINAL_1_Int hhv_id_idFINAL_2_Int hhv_id_idFINAL_3_Int hhv_id_idFINAL_4_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_5_Bool Bool)) (=> (not hhv_ULTIMATE.start_ULTIMATE.startENTRY_5_Bool) (ULTIMATE.start_ULTIMATE.startENTRY hhv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_5_Bool))))
(assert (forall ((hhv_id_idENTRY_0_Int Int) (hhv_id_idENTRY_1_Int Int) (hhv_id_idENTRY_2_Int Int) (hhv_id_idENTRY_3_Int Int) (hhv_id_idENTRY_4_Bool Bool)) (=> (not hhv_id_idENTRY_4_Bool) (id_idENTRY hhv_id_idENTRY_0_Int hhv_id_idENTRY_1_Int hhv_id_idENTRY_2_Int hhv_id_idENTRY_3_Int hhv_id_idENTRY_4_Bool))))
(assert (forall ((hbv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool Bool)) (=> (and hbv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool (ULTIMATE.start_ULTIMATE.startEXIT hbv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_5_Bool)) false)))
(check-sat)
