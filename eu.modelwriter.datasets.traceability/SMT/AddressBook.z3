(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(set-option :produce-unsat-cores true)


;---------------------------------------

;abstract sig Target { }
;sig Addr extends Target { }
;abstract sig Name extends Target { }

;sig Alias, Group extends Name { }

(declare-datatypes () ((Target address_1 address_2 group_1 group_2 group_3 alias_1 alias_2)))

(declare-fun isTarget(Target) Bool)
(declare-fun isAddr(Target) Bool)
(declare-fun isName(Target) Bool)
(declare-fun isAlias(Target) Bool)
(declare-fun isGroup(Target) Bool)

(assert (forall ((t Target)) 
  (=> (isAddr t) 
    (isTarget t) ) ) )
    
(assert (forall ((t Target)) 
  (=> (isName t) 
    (isTarget t) ) ) )
    
(assert (forall ((t Target)) 
  (=> (isTarget t) 
    (or (isAddr t) (isName t) ) ) ) )  
    
(assert (forall ((t Target)) 
  (=> (isTarget t) 
    (not (and (isAddr t) (isName t) ) ) ) ) )


(assert (forall ((t Target)) 
  (=> (isAlias t) 
    (isName t) ) ) )

(assert (forall ((t Target)) 
  (=> (isGroup t) 
    (isName t) ) ) )

(assert (forall ((t Target)) 
  (=> (isName t) 
    (or (isAlias t) (isGroup t) ) ) ) )
    
(assert (forall ((t Target)) 
  (=> (isName t) 
    (not (and (isAlias t) (isGroup t) ) ) ) ) )    

;------------------------------------------------

;sig Book {
;	names: set Name,
;	addr: names->some Target
;} {
;	no n: Name | n in n.^addr
;	all a: Alias | lone a.addr
;}

(declare-datatypes () ((Book book_1 book_2)))
(declare-fun isBook(Book) Bool)

(declare-fun names(Book Target) Bool)

(assert (forall ((book Book)(name Target)) 
  (=> (names book name) 
    (and (isBook book) (isName name) ) ) ) )
 
 
(declare-fun addr(Book Target Target) Bool)
(declare-fun oneTarget(Book Target) Target)

(assert (forall ((book Book)(name Target)(target Target)) 
  (=> (addr book name target) 
    (and (isBook book) (isName name) (isTarget target) ) ) ) )
    
(assert (forall ((book Book)(name Target))
   (=> (and (isBook book) (isName name) )
      (addr book name (oneTarget book name) ) ) ) )

;--------------------------------------------------------------------------

;	no n: Name | n in n.^addr
(declare-fun trAddr2(Int Target Target) Bool)

(assert (forall ((i Int)(t_1 Target)(t_2 Target)) 
  (=> (< i 1) 
    (not (trAddr2 i t_1 t_2)) ) ) )

(assert (forall ((t_1 Target)(t_2 Target)) 
  (= (trAddr2 1 t_1 t_2) 
    (exists ((b Book)) (addr b t_1 t_2) ) ) ) )

(assert (forall ((i Int)(t_1 Target)(t_2 Target)) 
  (=> (> i 1) 
    (= (trAddr2 i t_1 t_2) 
      (or (trAddr2 (- i 1) t_1 t_2) (exists ((w Target)) (and (trAddr2 (- i 1) t_1 w) (exists ((b Book)) (addr b w t_2) ) ) ) ) ) ) ) )

(assert (forall ((t Target)) 
  (=> (isName t) 
    (not (exists ((i Int)) (trAddr2 i t t) ) ) ) ) )


;--------------------------------------------------------------------------------------------------------

;all a: Alias | lone a.addr

(declare-fun oneTargetForAlias(Target) Target)

(assert (forall ((book Book)(alias Target)(target Target)) 
  (=> (and (isAlias alias) (addr book alias target) ) 
    (= target (oneTargetForAlias alias) ) ) ) )
    
;--------------------------------------------------------------------------------------------------------

;unsat
;(assert (!(isGroup group_1) :named axiom1))
;(assert (!(isAlias group_1) :named axiom2))


;unsat
;(assert (!(isGroup group_1) :named axiom3))
;(assert (!(isGroup group_2) :named axiom4))
;(assert (!(isGroup group_3) :named axiom5))
;(assert (!(isAddr address_1) :named axiom6))
;(assert (!(addr book_1 group_1 group_2) :named axiom7))
;(assert (!(addr book_2 group_2 group_3) :named axiom8))
;(assert (!(addr book_1 group_3 address_1) :named axiom9))
;(assert (!(addr book_2 group_3 group_1) :named axiom10))

;unsat
;(assert (!(isAlias alias_1) :named axiom11))
;(assert (!(isAlias alias_2) :named axiom12))
;(assert (!(isAddr address_1) :named axiom13))
;(assert (!(isAddr address_2) :named axiom14))
;(assert (!(addr book_1 alias_1 alias_2) :named axiom15))
;(assert (!(addr book_1 alias_1 address_1) :named axiom16))
;(assert (!(addr book_2 alias_1 address_2) :named axiom17))


(check-sat)
(get-unsat-core)


