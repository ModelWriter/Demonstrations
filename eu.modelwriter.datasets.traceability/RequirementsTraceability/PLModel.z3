;Requirements_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

; Example Begin

(declare-datatypes () ((Requirement Requirement12 Requirement28 Requirement1 Requirement18 Requirement10 Requirement26 Requirement16 Requirement9 Requirement7 Requirement14 Requirement21 Requirement25 Requirement31 Requirement3 Requirement5 Requirement23 Requirement19 Requirement2 Requirement13 Requirement29 Requirement11 Requirement27 Requirement17 Requirement15 Requirement8 Requirement20 Requirement4 Requirement24 Requirement30 Requirement22 Requirement6)))

(declare-fun requires (Requirement Requirement) Bool)
(declare-fun contains (Requirement Requirement) Bool)
(declare-fun refines (Requirement Requirement) Bool)
(declare-fun p_refines (Requirement Requirement) Bool)
(declare-fun conflicts (Requirement Requirement) Bool)
(declare-fun _equals (Requirement Requirement) Bool)

(assert (!(conflicts Requirement12 Requirement9):named conf_12_9))
(assert (!(conflicts Requirement12 Requirement11):named conf_12_11))
(assert (!(conflicts Requirement12 Requirement10):named conf_12_10))
(assert (!(requires Requirement12 Requirement18):named requ_12_18))
(assert (!(requires Requirement12 Requirement6):named requ_12_6))
;(assert (!(requires Requirement12 Requirement13):named requ_12_13))
(assert (!(requires Requirement12 Requirement17):named requ_12_17))
(assert (!(refines Requirement12 Requirement8):named refi_12_8))
(assert (!(conflicts Requirement28 Requirement29):named conf_28_29))
(assert (!(refines Requirement28 Requirement27):named refi_28_27))
(assert (!(refines Requirement18 Requirement16):named refi_18_16))
(assert (!(conflicts Requirement10 Requirement9):named conf_10_9))
(assert (!(conflicts Requirement10 Requirement12):named conf_10_12))
(assert (!(conflicts Requirement10 Requirement11):named conf_10_11))
(assert (!(requires Requirement10 Requirement18):named requ_10_18))
(assert (!(refines Requirement10 Requirement8):named refi_10_8))
(assert (!(refines Requirement26 Requirement25):named refi_26_25))
(assert (!(conflicts Requirement9 Requirement12):named conf_9_12))
(assert (!(conflicts Requirement9 Requirement10):named conf_9_10))
(assert (!(conflicts Requirement9 Requirement11):named conf_9_11))
(assert (!(requires Requirement9 Requirement18):named requ_9_18))
(assert (!(refines Requirement9 Requirement8):named refi_9_8))
(assert (!(refines Requirement7 Requirement4):named refi_7_4))
(assert (!(conflicts Requirement14 Requirement13):named conf_14_13))
(assert (!(conflicts Requirement14 Requirement15):named conf_14_15))
(assert (!(refines Requirement14 Requirement8):named refi_14_8))
(assert (!(conflicts Requirement21 Requirement20):named conf_21_20))
(assert (!(requires Requirement21 Requirement22):named requ_21_22))
(assert (!(refines Requirement21 Requirement19):named refi_21_19))
(assert (!(contains Requirement31 Requirement22):named cont_31_22))
(assert (!(contains Requirement31 Requirement26):named cont_31_26))
(assert (!(conflicts Requirement3 Requirement2):named conf_3_2))
(assert (!(refines Requirement3 Requirement1):named refi_3_1))
(assert (!(conflicts Requirement5 Requirement6):named conf_5_6))
(assert (!(conflicts Requirement5 Requirement11):named conf_5_11))
(assert (!(refines Requirement5 Requirement4):named refi_5_4))
(assert (!(conflicts Requirement23 Requirement24):named conf_23_24))
(assert (!(refines Requirement23 Requirement22):named refi_23_22))
(assert (!(requires Requirement19 Requirement25):named requ_19_25))
(assert (!(conflicts Requirement2 Requirement3):named conf_2_3))
(assert (!(refines Requirement2 Requirement1):named refi_2_1))
(assert (!(conflicts Requirement13 Requirement15):named conf_13_15))
(assert (!(conflicts Requirement13 Requirement6):named conf_13_6))
(assert (!(conflicts Requirement13 Requirement14):named conf_13_14))
(assert (!(requires Requirement13 Requirement5):named requ_13_5))
(assert (!(refines Requirement13 Requirement8):named refi_13_8))
(assert (!(conflicts Requirement29 Requirement28):named conf_29_28))
(assert (!(requires Requirement29 Requirement30):named requ_29_30))
(assert (!(refines Requirement29 Requirement27):named refi_29_27))
(assert (!(conflicts Requirement11 Requirement9):named conf_11_9))
(assert (!(conflicts Requirement11 Requirement5):named conf_11_5))
(assert (!(conflicts Requirement11 Requirement12):named conf_11_12))
(assert (!(conflicts Requirement11 Requirement10):named conf_11_10))
(assert (!(requires Requirement11 Requirement17):named requ_11_17))
(assert (!(refines Requirement11 Requirement8):named refi_11_8))
(assert (!(refines Requirement27 Requirement25):named refi_27_25))
(assert (!(refines Requirement17 Requirement16):named refi_17_16))
(assert (!(conflicts Requirement15 Requirement14):named conf_15_14))
(assert (!(conflicts Requirement15 Requirement13):named conf_15_13))
(assert (!(requires Requirement15 Requirement6):named requ_15_6))
(assert (!(refines Requirement15 Requirement8):named refi_15_8))
(assert (!(conflicts Requirement20 Requirement21):named conf_20_21))
(assert (!(requires Requirement20 Requirement26):named requ_20_26))
(assert (!(refines Requirement20 Requirement19):named refi_20_19))
(assert (!(conflicts Requirement24 Requirement23):named conf_24_23))
(assert (!(requires Requirement24 Requirement30):named requ_24_30))
(assert (!(refines Requirement24 Requirement22):named refi_24_22))
(assert (!(p_refines Requirement24 Requirement31):named part_24_31))
(assert (!(conflicts Requirement6 Requirement5):named conf_6_5))
(assert (!(conflicts Requirement6 Requirement13):named conf_6_13))
(assert (!(refines Requirement6 Requirement4):named refi_6_4))

; Example End

; Non-reflexive requires
(assert
  (forall ((r Requirement))
    (not (requires r r))
  )
)

; Non-Symmetric requires
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (requires r1 r2) (not (requires r2 r1)))
  )
)

; Transitive requires
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (requires r1 r2) (requires r2 r3))
      (requires r1 r3)
    )
  )
)

; Non-reflexive contains
(assert
  (forall ((r Requirement))
    (not (contains r r))
  )
)

; Non-Symmetric contains
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (contains r1 r2) (not (contains r2 r1)))
  )
)

; Transitive contains
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (contains r1 r2) (contains r2 r3))
      (contains r1 r3)
    )
  )
)

; Non-reflexive refines
(assert
  (forall ((r Requirement))
    (not (refines r r))
  )
)

; Non-Symmetric refines
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (refines r1 r2) (not (refines r2 r1)))
  )
)

; Transitive refines
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (refines r1 r2) (refines r2 r3))
      (refines r1 r3)
    )
  )
)

; Non-reflexive p_refines
(assert
  (forall ((r Requirement))
    (not (p_refines r r))
  )
)

; Non-Symmetric p_refines
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (p_refines r1 r2) (not (p_refines r2 r1)))
  )
)

; Transitive p_refines
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (p_refines r1 r2) (p_refines r2 r3))
      (p_refines r1 r3)
    )
  )
)

; Non-reflexive conflicts
(assert
  (forall ((r Requirement))
    (not (conflicts r r))
  )
)

; Symmetric conflicts
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (conflicts r1 r2) (conflicts r2 r1))
  )
)

; Reflexive _equals
(assert
  (forall ((r Requirement))
    (_equals r r)
  )
)

; Symmetric _equals
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (_equals r1 r2) (_equals r2 r1))
  )
)

; Transitive _equals
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (_equals r1 r2) (_equals r2 r3))
      (_equals r1 r3)
    )
  )
)

; There is at most one relation between two requirements
(assert
  (forall ((r1 Requirement) (r2 Requirement))
    ( and
      (=> (requires r1 r2) (not (refines r1 r2)))
      (=> (requires r1 r2) (not (contains r1 r2)))
      (=> (requires r1 r2) (not (p_refines r1 r2)))
      (=> (requires r1 r2) (not (_equals r1 r2)))
      (=> (requires r1 r2) (not (conflicts r1 r2)))
      
      (=> (requires r1 r2) (not (refines r2 r1)))
      (=> (requires r1 r2) (not (contains r2 r1)))
      (=> (requires r1 r2) (not (p_refines r2 r1)))
      (=> (requires r1 r2) (not (_equals r2 r1)))
      (=> (requires r1 r2) (not (conflicts r2 r1)))
      
      (=> (refines r1 r2) (not (requires r1 r2)))
      (=> (refines r1 r2) (not (contains r1 r2)))
      (=> (refines r1 r2) (not (p_refines r1 r2)))
      (=> (refines r1 r2) (not (_equals r1 r2)))
      (=> (refines r1 r2) (not (conflicts r1 r2)))
      
      (=> (refines r1 r2) (not (requires r2 r1)))
      (=> (refines r1 r2) (not (contains r2 r1)))
      (=> (refines r1 r2) (not (p_refines r2 r1)))
      (=> (refines r1 r2) (not (_equals r2 r1)))
      (=> (refines r1 r2) (not (conflicts r2 r1)))
      
      (=> (contains r1 r2) (not (requires r1 r2)))
      (=> (contains r1 r2) (not (refines r1 r2)))
      (=> (contains r1 r2) (not (p_refines r1 r2)))
      (=> (contains r1 r2) (not (_equals r1 r2)))
      (=> (contains r1 r2) (not (conflicts r1 r2)))
      
      (=> (contains r1 r2) (not (requires r2 r1)))
      (=> (contains r1 r2) (not (refines r2 r1)))
      (=> (contains r1 r2) (not (p_refines r2 r1)))
      (=> (contains r1 r2) (not (_equals r2 r1)))
      (=> (contains r1 r2) (not (conflicts r2 r1)))
      
      (=> (p_refines r1 r2) (not (requires r1 r2)))
      (=> (p_refines r1 r2) (not (refines r1 r2)))
      (=> (p_refines r1 r2) (not (contains r1 r2)))
      (=> (p_refines r1 r2) (not (_equals r1 r2)))
      (=> (p_refines r1 r2) (not (conflicts r1 r2)))
      
      (=> (p_refines r1 r2) (not (requires r2 r1)))
      (=> (p_refines r1 r2) (not (refines r2 r1)))
      (=> (p_refines r1 r2) (not (contains r2 r1)))
      (=> (p_refines r1 r2) (not (_equals r2 r1)))
      (=> (p_refines r1 r2) (not (conflicts r2 r1)))
      
      (=> (_equals r1 r2) (not (requires r1 r2)))
      (=> (_equals r1 r2) (not (refines r1 r2)))
      (=> (_equals r1 r2) (not (contains r1 r2)))
      (=> (_equals r1 r2) (not (p_refines r1 r2)))
      (=> (_equals r1 r2) (not (conflicts r1 r2)))
      
      (=> (_equals r1 r2) (not (requires r2 r1)))
      (=> (_equals r1 r2) (not (refines r2 r1)))
      (=> (_equals r1 r2) (not (contains r2 r1)))
      (=> (_equals r1 r2) (not (p_refines r2 r1)))
      (=> (_equals r1 r2) (not (conflicts r2 r1)))
      
      (=> (conflicts r1 r2) (not (requires r1 r2)))
      (=> (conflicts r1 r2) (not (refines r1 r2)))
      (=> (conflicts r1 r2) (not (contains r1 r2)))
      (=> (conflicts r1 r2) (not (p_refines r1 r2)))
      (=> (conflicts r1 r2) (not (_equals r1 r2)))
      
      (=> (conflicts r1 r2) (not (requires r2 r1)))
      (=> (conflicts r1 r2) (not (refines r2 r1)))
      (=> (conflicts r1 r2) (not (contains r2 r1)))
      (=> (conflicts r1 r2) (not (p_refines r2 r1)))
      (=> (conflicts r1 r2) (not (_equals r2 r1)))
    )
  )
)

; _equals facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (_equals r1 r2) (requires r2 r3)) (requires r1 r3))
      (=> (and (_equals r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (_equals r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (_equals r1 r2) (contains r2 r3)) (contains r1 r3))
      (=> (and (_equals r1 r2) (conflicts r2 r3)) (conflicts r1 r3))
      
      (=> (and (requires r1 r2) (_equals r2 r3)) (requires r1 r3))
      (=> (and (refines r1 r2) (_equals r2 r3)) (refines r1 r3))
      (=> (and (p_refines r1 r2) (_equals r2 r3)) (p_refines r1 r3))
      (=> (and (contains r1 r2) (_equals r2 r3)) (contains r1 r3))
      (=> (and (conflicts r1 r2) (_equals r2 r3)) (conflicts r1 r3))
    )
  )
)

; infer requires facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (requires r1 r2) (refines r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (refines r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (requires r1 r2) (contains r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (contains r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
    )
  )
)

; infer refines facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (contains r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (refines r1 r2) (contains r2 r3)) (refines r1 r3))
    )
  )
)

; infer p_refines facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (contains r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (refines r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (p_refines r1 r2) (refines r2 r3)) (p_refines r1 r3))
    )
  )
)

; infer conflicts facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (or (requires r1 r2) (refines r1 r2) (contains r1 r2)) (conflicts r2 r3)) (conflicts r1 r3))
  )
)

; Requirements_Theory End

(check-sat)
;(get-model)
(get-unsat-core)
