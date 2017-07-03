(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(set-option :produce-unsat-cores true)


;sig Thing {}
;sig List {
;car: lone Thing,
;cdr: lone List
; }

(declare-datatypes () ((Thing thing_1 thing_2)))
(declare-datatypes () ((List1 list_1 list_2 list_3 nil_1 nil_2)))

(declare-fun isThing(Thing) Bool)
(declare-fun isList(List1) Bool)

(declare-fun car(List1 Thing) Bool)
(declare-fun cdr(List1 List1) Bool)

(declare-fun oneThing(List1) Thing)
(declare-fun oneList(List1) List1)

(assert (forall ((l List1)(t Thing)) 
  (=> (car l t) 
    (and (isList l) (isThing t) ) ) ) )

(assert (forall ((l List1)(t Thing)) 
  (=> (car l t) 
    (= t (oneThing l) ) ) ) )
    
(assert (forall ((l_1 List1)(l_2 List1)) 
  (=> (cdr l_1 l_2) 
    (and (isList l_1) (isList l_2) ) ) ) )
    
(assert (forall ((l_1 List1)(l_2 List1)) 
  (=> (cdr l_1 l_2) 
    (= l_2 (oneList l_1) ) ) ) )

;--------------------------------------------------------    

;one sig Nil extends List {}

(declare-fun isNil(List1) Bool)

(assert (forall ((nil List1)) 
  (=> (isNil nil) 
    (isList nil) ) ) )

(assert (exists ((nil List1)) (isNil nil) ) )

(assert (forall ((nil_1 List1)(nil_1 List1)) 
  (=> (and (isNil nil_1) (isNil nil_2)) 
    (= nil_1 nil_2) ) ) )
    


;-----------------------------------------------------

;fact {
;no Nil.car
;no Nil.cdr
;all l: List − Nil | some l.car and some l.cdr
;all l: List | Nil in l.*cdr
;}    
 
;no Nil.car   
(assert (forall ((nil List1)) 
  (=> (isNil nil) 
    (not (exists ((t Thing)) (car nil t) ) ) ) ) )

;no Nil.cdr    
(assert (forall ((nil List1)) 
  (=> (isNil nil) 
    (not (exists ((l List1)) (cdr nil l) ) ) ) ) )

;all l: List − Nil | some l.car and some l.cdr
(assert (forall ((l_1 List1)) 
  (=> (not (isNil l_1) ) 
    (exists ((t_1 Thing)) (car l_1 t_1) ) ) ) )
 
(assert (forall ((l_1 List1)) 
  (=> (not (isNil l_1) ) 
    (exists ((l_2 List1)) (cdr l_1 l_2) ) ) ) )
    

;all l: List | Nil in l.*cdr
(declare-fun trCdr(Int List1 List1) Bool)

(assert (forall ((i Int)(l_1 List1)(l_2 List1)) 
  (=> (< i 1) 
    (not (trCdr i l_1 l_2) ) ) ) )
    
(assert (forall ((l_1 List1)(l_2 List1)) 
  (= (trCdr 1 l_1 l_2) 
    (cdr l_1 l_2) ) ) )
    
(assert (forall ((i Int)(l_1 List1)(l_2 List1)) 
  (=> (> i 1) 
    (= (trCdr i l_1 l_2) 
      (or (trCdr (- i 1) l_1 l_2) (exists ((w List1)) (and (trCdr (- i 1) l_1 w) (cdr w l_2) ) ) ) ) ) ) )

(assert (forall ((l List1)(nil List1)) 
  (=> (and (isNil nil) (not (isNil l) ) ) 
    (exists ((i Int)) (trCdr i l nil) ) ) ) )
      
;-----------------------------------------------------------------------------------------------------

;pred prefixes[ pre: List → List ] {
;all l: List | Nil in l.pre
;all l: List − Nil | l not in Nil.pre
;all l, p: List − Nil | (p in l.pre) iff (l.car = p.car and p.cdr in l.cdr.pre)
; }

(declare-fun pre(List1 List1) Bool)
(declare-fun prefixes() Bool)

;all l: List | Nil in l.pre
;all l: List − Nil | l not in Nil.pre
(assert (forall ((nil List1)) (=> (isNil nil) (pre nil nil) ) ) )
(assert (forall ((l List1)(nil List1)) (=> (and (not (isNil l)) (isNil nil)) (pre l nil) ) ) )
(assert (forall ((l List1)(nil List1)) (=> (and (not (isNil l)) (isNil nil)) (not (pre nil l)) ) ) )

;all l, p: List − Nil | (p in l.pre) iff (l.car = p.car and p.cdr in l.cdr.pre)
(declare-fun cdrJoinPre(List1 List1) Bool)

(assert (forall ((l_1 List1)(l_2 List1)) 
  (=> (cdrJoinPre l_1 l_2) 
    (exists ((list List1)) (and (cdr l_1 list) (pre list l_2) ) ) ) ) )


;-------------------------------------------------------------------------------------------------------

;unsat
;(assert (!(isNil nil_1)  :named axiom1))
;(assert (!(isNil nil_2)  :named axiom2))

;unsat
;(assert (!(isNil nil_1)  :named axiom3))
;(assert (!(car nil_1 thing_1)  :named axiom4))

;unsat
;(assert (!(isNil nil_1)  :named axiom5))
;(assert (!(cdr nil_1 list_1)  :named axiom6))

;unsat
;(assert (!(isNil nil_1)  :named axiom7))
;(assert (!(cdr list_1 list_2)  :named axiom10))
;(assert (!(cdr list_2 list_3)  :named axiom11))
;(assert (!(cdr list_3 nil_1)  :named axiom12))
;(assert (!(not(exists ((i Int)) (trCdr i list_1 nil_1) ))  :named axiom13))

;-------------------------------------------------------------------------------------

;all l, p: List − Nil | (p in l.pre) iff (l.car = p.car and p.cdr in l.cdr.pre)
(assert (!(forall ((l List1)(p List1)) (=> (and (not (isNil l)) (not (isNil p))) (= (pre l p) (and (forall ((t Thing)) (= (car l t) (car p t))) (cdrJoinPre l (oneList p)) )) ) )  :named axiom14))

;check {
;all pre: List → List | all l, p: List |
;(prefixes[pre] and p in l.pre and l in p.pre) implies p = l
;} for 3
(assert (!(forall ((l List1)(p List1)) (=> (and (= prefixes true) (pre l p) (pre p l)) (= p l) ) )  :named axiom15))


(check-sat)
(get-unsat-core)



