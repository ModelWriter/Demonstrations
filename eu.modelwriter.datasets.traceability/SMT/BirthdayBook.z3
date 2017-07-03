(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(set-option :produce-unsat-cores true)

;sig Name {}
;sig Date {}
;sig BirthdayBook {known: set Name, date: known -> one Date}


(declare-datatypes () ((BirthdayBook bb1 bb2 bb3 bb4)))
(declare-datatypes () ((Name n1 n2)))
(declare-datatypes () ((Date d1 d2)))


(declare-fun isName(Name) Bool)
(declare-fun isDate(Date) Bool)
(declare-fun isBirthdayBook(BirthdayBook) Bool)

(declare-fun known(BirthdayBook Name) Bool)

(assert (forall ((bb BirthdayBook)(n Name)) 
  (=> (known bb n) 
    (and (isBirthdayBook bb) (isName n) ) ) ) )
 
(declare-fun date(BirthdayBook Name Date) Bool)
(declare-fun oneDate(BirthdayBook Name) Date)

(assert (forall ((bb BirthdayBook)(n Name)(d Date)) 
  (=> (date bb n d) 
    (and (isBirthdayBook bb) (isName n) (isDate d) ) ) ) )
    
(assert (forall((bb BirthdayBook)(n Name)(d Date)) 
  (=> (date bb n d) 
    (= d (oneDate bb n) ) ) ) )
    
(assert (forall ((bb BirthdayBook)(n Name)) 
  (=> (and (isBirthdayBook bb) (isName n)) 
    (date bb n (oneDate bb n) ) ) ) )
    
;-------------------------------------------------

;pred AddBirthday [bb, bb': BirthdayBook, n: Name, d: Date] {
;    bb'.date = bb.date ++ (n->d)
;    }

(declare-fun addBirthday(BirthdayBook BirthdayBook Name Date) Bool)

(assert (forall ((bb BirthdayBook)(bb! BirthdayBook)(n Name)(d Date)) 
  (=> (addBirthday bb bb! n d) 
    (and (date bb! n d) 
      (not (date bb n d) ) ) ) ) )
    
;--------------------------------------------------------------------

;pred DelBirthday [bb, bb': BirthdayBook, n: Name] {
;    bb'.date = bb.date - (n->Date)
;   }

(declare-fun delBirthday(BirthdayBook BirthdayBook Name) Bool)

(assert (forall ((bb BirthdayBook)(bb! BirthdayBook)(n Name)) 
  (=> (delBirthday bb bb! n) 
    (and (not (date bb! n (oneDate bb n))) 
      (date bb n (oneDate bb n) ) ) ) ) )

;-------------------------------------------------------------------  

;pred FindBirthday [bb: BirthdayBook, n: Name, d: lone Date] {
;    d = bb.date[n]
;    }

(declare-fun findBirthday(BirthdayBook Name Date) Bool)

(assert (forall ((bb BirthdayBook)(n Name)(d Date)) 
  (=> (findBirthday bb n d) 
    (date bb n d) ) ) )


(assert (!(addBirthday bb1 bb2 n1 d1)  :named axiom1))
(assert (!(delBirthday bb2 bb3 n1)  :named axiom2))
(assert (!(findBirthday bb3 n1 d1)  :named axiom3))


(check-sat)
(get-unsat-core)
(exit)



