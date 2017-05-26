;Requirements_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

; Example Begin

(declare-datatypes () ((Requirement Requirement28 Requirement1 Requirement47 Requirement113 Requirement10 Requirement9 Requirement103 Requirement14 Requirement72 Requirement120 Requirement71 Requirement66 Requirement53 Requirement86 Requirement33 Requirement92 Requirement2 Requirement112 Requirement29 Requirement11 Requirement102 Requirement73 Requirement15 Requirement46 Requirement121 Requirement67 Requirement52 Requirement32 Requirement91 Requirement87 Requirement12 Requirement115 Requirement49 Requirement108 Requirement26 Requirement16 Requirement59 Requirement101 Requirement7 Requirement51 Requirement21 Requirement68 Requirement122 Requirement80 Requirement98 Requirement31 Requirement90 Requirement88 Requirement41 Requirement78 Requirement114 Requirement13 Requirement48 Requirement109 Requirement61 Requirement27 Requirement100 Requirement58 Requirement17 Requirement8 Requirement50 Requirement99 Requirement70 Requirement20 Requirement89 Requirement30 Requirement60 Requirement79 Requirement40 Requirement69 Requirement76 Requirement18 Requirement43 Requirement106 Requirement57 Requirement62 Requirement81 Requirement116 Requirement5 Requirement38 Requirement96 Requirement23 Requirement37 Requirement19 Requirement77 Requirement42 Requirement117 Requirement63 Requirement56 Requirement107 Requirement82 Requirement83 Requirement22 Requirement36 Requirement97 Requirement6 Requirement39 Requirement74 Requirement45 Requirement118 Requirement93 Requirement64 Requirement55 Requirement111 Requirement104 Requirement35 Requirement84 Requirement25 Requirement3 Requirement94 Requirement119 Requirement44 Requirement75 Requirement65 Requirement54 Requirement110 Requirement105 Requirement34 Requirement85 Requirement95 Requirement4 Requirement24 Requirement123)))

(declare-fun requires (Requirement Requirement) Bool)
(declare-fun contains (Requirement Requirement) Bool)
(declare-fun refines (Requirement Requirement) Bool)
(declare-fun p_refines (Requirement Requirement) Bool)
(declare-fun conflicts (Requirement Requirement) Bool)
(declare-fun _equals (Requirement Requirement) Bool)

;;;
;(assert (!(conflicts Requirement98 Requirement48):named conf_98_48))
;(assert (!(conflicts Requirement48 Requirement98):named conf_48_98))
;(assert (!(p_refines Requirement60 Requirement59):named part_60_59))
;;;

(assert (!(contains Requirement123 Requirement97):named cont_123_97))
(assert (!(contains Requirement123 Requirement98):named cont_123_98))
(assert (!(contains Requirement123 Requirement99):named cont_123_99))
(assert (!(contains Requirement123 Requirement100):named cont_123_100))
(assert (!(conflicts Requirement28 Requirement26):named conf_28_26))
(assert (!(refines Requirement28 Requirement27):named refi_28_27))
(assert (!(refines Requirement47 Requirement46):named refi_47_46))
(assert (!(refines Requirement113 Requirement110):named refi_113_110))
(assert (!(requires Requirement10 Requirement11):named requ_10_11))
(assert (!(requires Requirement9 Requirement1):named requ_9_1))
(assert (!(requires Requirement9 Requirement4):named requ_9_4))
(assert (!(conflicts Requirement103 Requirement60):named conf_103_60))
(assert (!(requires Requirement14 Requirement2):named requ_14_2))
(assert (!(refines Requirement120 Requirement121):named refi_120_121))
(assert (!(refines Requirement71 Requirement70):named refi_71_70))
(assert (!(conflicts Requirement66 Requirement29):named conf_66_29))
(assert (!(refines Requirement53 Requirement68):named refi_53_68))
(assert (!(refines Requirement33 Requirement30):named refi_33_30))
(assert (!(refines Requirement2 Requirement1):named refi_2_1))
(assert (!(refines Requirement112 Requirement110):named refi_112_110))
(assert (!(conflicts Requirement29 Requirement66):named conf_29_66))
(assert (!(conflicts Requirement29 Requirement107):named conf_29_107))
(assert (!(requires Requirement29 Requirement8):named requ_29_8))
(assert (!(refines Requirement29 Requirement27):named refi_29_27))
(assert (!(requires Requirement11 Requirement48):named requ_11_48))
(assert (!(requires Requirement11 Requirement1):named requ_11_1))
(assert (!(requires Requirement11 Requirement97):named requ_11_97))
(assert (!(conflicts Requirement102 Requirement60):named conf_102_60))
(assert (!(p_refines Requirement102 Requirement100):named part_102_100))
(assert (!(p_refines Requirement73 Requirement72):named part_73_72))
(assert (!(requires Requirement15 Requirement2):named requ_15_2))
(assert (!(requires Requirement67 Requirement75):named requ_67_75))
(assert (!(requires Requirement52 Requirement48):named requ_52_48))
(assert (!(refines Requirement52 Requirement68):named refi_52_68))
(assert (!(refines Requirement32 Requirement30):named refi_32_30))
(assert (!(requires Requirement12 Requirement4):named requ_12_4))
(assert (!(requires Requirement115 Requirement113):named requ_115_113))
(assert (!(requires Requirement115 Requirement111):named requ_115_111))
(assert (!(requires Requirement115 Requirement112):named requ_115_112))
(assert (!(requires Requirement115 Requirement114):named requ_115_114))
(assert (!(refines Requirement115 Requirement110):named refi_115_110))
(assert (!(refines Requirement49 Requirement48):named refi_49_48))
(assert (!(requires Requirement108 Requirement109):named requ_108_109))
(assert (!(conflicts Requirement26 Requirement85):named conf_26_85))
(assert (!(conflicts Requirement26 Requirement28):named conf_26_28))
(assert (!(refines Requirement26 Requirement6):named refi_26_6))
(assert (!(requires Requirement16 Requirement8):named requ_16_8))
(assert (!(requires Requirement16 Requirement4):named requ_16_4))
(assert (!(refines Requirement16 Requirement7):named refi_16_7))
(assert (!(conflicts Requirement59 Requirement100):named conf_59_100))
(assert (!(p_refines Requirement101 Requirement100):named part_101_100))
(assert (!(requires Requirement51 Requirement48):named requ_51_48))
(assert (!(conflicts Requirement21 Requirement119):named conf_21_119))
(assert (!(refines Requirement122 Requirement92):named refi_122_92))
(assert (!(p_refines Requirement80 Requirement68):named part_80_68))
(assert (!(refines Requirement31 Requirement30):named refi_31_30))
(assert (!(requires Requirement90 Requirement53):named requ_90_53))
(assert (!(requires Requirement90 Requirement15):named requ_90_15))
(assert (!(refines Requirement41 Requirement35):named refi_41_35))
(assert (!(refines Requirement114 Requirement110):named refi_114_110))
(assert (!(requires Requirement13 Requirement15):named requ_13_15))
(assert (!(requires Requirement13 Requirement14):named requ_13_14))
(assert (!(requires Requirement13 Requirement17):named requ_13_17))
(assert (!(conflicts Requirement61 Requirement104):named conf_61_104))
(assert (!(p_refines Requirement61 Requirement59):named part_61_59))
(assert (!(conflicts Requirement100 Requirement59):named conf_100_59))
(assert (!(refines Requirement58 Requirement56):named refi_58_56))
(assert (!(requires Requirement8 Requirement11):named requ_8_11))
(assert (!(refines Requirement50 Requirement48):named refi_50_48))
(assert (!(requires Requirement20 Requirement4):named requ_20_4))
(assert (!(conflicts Requirement89 Requirement30):named conf_89_30))
(assert (!(requires Requirement89 Requirement88):named requ_89_88))
(assert (!(conflicts Requirement30 Requirement89):named conf_30_89))
(assert (!(conflicts Requirement60 Requirement103):named conf_60_103))
(assert (!(conflicts Requirement60 Requirement102):named conf_60_102))
(assert (!(requires Requirement60 Requirement11):named requ_60_11))
(assert (!(refines Requirement40 Requirement35):named refi_40_35))
(assert (!(p_refines Requirement69 Requirement68):named part_69_68))
(assert (!(conflicts Requirement18 Requirement74):named conf_18_74))
(assert (!(requires Requirement18 Requirement7):named requ_18_7))
(assert (!(refines Requirement18 Requirement17):named refi_18_17))
(assert (!(refines Requirement43 Requirement42):named refi_43_42))
(assert (!(refines Requirement106 Requirement104):named refi_106_104))
(assert (!(refines Requirement57 Requirement56):named refi_57_56))
(assert (!(requires Requirement81 Requirement80):named requ_81_80))
(assert (!(requires Requirement116 Requirement4):named requ_116_4))
(assert (!(refines Requirement5 Requirement4):named refi_5_4))
(assert (!(refines Requirement38 Requirement35):named refi_38_35))
(assert (!(conflicts Requirement23 Requirement119):named conf_23_119))
(assert (!(refines Requirement37 Requirement35):named refi_37_35))
(assert (!(requires Requirement19 Requirement1):named requ_19_1))
(assert (!(requires Requirement117 Requirement7):named requ_117_7))
(assert (!(conflicts Requirement107 Requirement29):named conf_107_29))
(assert (!(p_refines Requirement82 Requirement68):named part_82_68))
(assert (!(conflicts Requirement83 Requirement84):named conf_83_84))
(assert (!(conflicts Requirement22 Requirement119):named conf_22_119))
(assert (!(refines Requirement36 Requirement35):named refi_36_35))
(assert (!(requires Requirement97 Requirement4):named requ_97_4))
(assert (!(requires Requirement97 Requirement1):named requ_97_1))
(assert (!(requires Requirement6 Requirement5):named requ_6_5))
(assert (!(refines Requirement6 Requirement4):named refi_6_4))
(assert (!(refines Requirement39 Requirement35):named refi_39_35))
(assert (!(conflicts Requirement74 Requirement18):named conf_74_18))
(assert (!(refines Requirement45 Requirement44):named refi_45_44))
(assert (!(conflicts Requirement118 Requirement65):named conf_118_65))
(assert (!(refines Requirement118 Requirement122):named refi_118_122))
(assert (!(refines Requirement55 Requirement54):named refi_55_54))
(assert (!(refines Requirement111 Requirement110):named refi_111_110))
(assert (!(conflicts Requirement104 Requirement61):named conf_104_61))
(assert (!(p_refines Requirement104 Requirement100):named part_104_100))
(assert (!(conflicts Requirement84 Requirement85):named conf_84_85))
(assert (!(conflicts Requirement84 Requirement83):named conf_84_83))
(assert (!(requires Requirement25 Requirement24):named requ_25_24))
(assert (!(requires Requirement3 Requirement2):named requ_3_2))
(assert (!(refines Requirement3 Requirement1):named refi_3_1))
(assert (!(conflicts Requirement119 Requirement22):named conf_119_22))
(assert (!(conflicts Requirement119 Requirement21):named conf_119_21))
(assert (!(conflicts Requirement119 Requirement23):named conf_119_23))
(assert (!(conflicts Requirement65 Requirement118):named conf_65_118))
(assert (!(requires Requirement65 Requirement59):named requ_65_59))
(assert (!(refines Requirement54 Requirement68):named refi_54_68))
(assert (!(requires Requirement110 Requirement4):named requ_110_4))
(assert (!(refines Requirement105 Requirement104):named refi_105_104))
(assert (!(refines Requirement34 Requirement30):named refi_34_30))
(assert (!(conflicts Requirement85 Requirement26):named conf_85_26))
(assert (!(conflicts Requirement85 Requirement84):named conf_85_84))
(assert (!(requires Requirement24 Requirement7):named requ_24_7))

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
(get-model)
(get-unsat-core)
(exit)
