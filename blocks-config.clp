(deffacts stare-initiala
	(stiva A B C)
	(stiva D E F)
	
	(stivaf E B)
	(stivaf A F D)
	(stivaf C)
)

(defglobal ?*pas* = 1)

(defrule bloc-pe-podea (declare (salience 17)) ;important prioritate
	(stivaf $? ?bloc)
	(stiva $? ?bloc ? $?)
	=>
	(assert (scop muta ?bloc pe podea))
	(printout t "#1 Se creeaza scopul: muta " ?bloc " pe podea " crlf)
)

(defrule bloc-pe-bloc (declare (salience 20)) ;important prioritate
	(stivaf $? ?bloc ?sub $?)
	(not (stiva $? ?bloc ?sub $?))
	=>
	(assert (scop muta ?bloc pe ?sub))
	(printout t "#1 Se creeaza scopul: muta " ?bloc " pe " ?sub crlf)	
)

(defrule sterge-stivaf (declare (salience 15))
	?a<-(stivaf $? ?bloc ?sub $?)
	(forall (stivaf $? ?bloc ?sub $?) (scop muta ?bloc pe ?sub))	
	=>
	(retract ?a)
	(printout t "#1 Se sterge o stivaf " crlf)	
)

(defrule singurul-bloc-pe-podea-creeaza-scop (declare (salience 20))
	?a<-(stivaf ?bloc)
	(not (stiva $? ?bloc))
	=>
	(retract ?a)
	(assert (scop muta ?bloc pe podea))
	(printout t "#1 Se creeaza scopul: muta " ?bloc " pe podea" crlf "& Se sterge o stivaf" crlf)	
)

(defrule singurul-bloc-pe-podea-nu-creeaza-scop (declare (salience 20))
	?a<-(stivaf ?bloc)
	(stiva $? ?bloc)
	=>
	(retract ?a)
	(printout t " Se sterge o stivaf" crlf)	
)


(defrule mutare-directa (declare (salience 10)) ; (A B C)(D E F)=>(C)(E B)(A F D) problema- scop muta A pe podea exista totusi in baza de fapte
	?scop <- (scop muta ?bloc1 pe ?bloc2)
	?stiva1 <- (stiva ?bloc1 $?rest1)
	?stiva2 <- (stiva ?bloc2 $?rest2)
	(not (scop muta ?bloc2 pe ?)) ;important
	=>
	(retract ?scop ?stiva1 ?stiva2)
	(assert (stiva $?rest1) (stiva ?bloc1 ?bloc2 $?rest2) )
	(printout t "Mutare #" ?*pas* " : Blocul " ?bloc1 " este mutat pe blocul " ?bloc2 crlf)
	(bind ?*pas* (+ ?*pas* 1))
)

(defrule eliberare-sursa
	(scop muta ?sursa pe ?dest)
	(stiva $? ?pe-sursa ?sursa $?)
	(not (scop muta ?pe-sursa pe podea))
	=>
	(assert (scop muta ?pe-sursa pe podea) )
	(printout t "#2 Se creeaza scopul: muta " ?pe-sursa " pe podea " crlf)
)

(defrule eliberare-dest
	(scop muta ?sursa pe ?dest)
	(stiva $? ?pe-dest ?dest $?)
	(not (scop muta ?pe-dest pe podea))
	=>
	(assert (scop muta ?pe-dest pe podea) )
	(printout t "#2 Se creeaza scopul: muta " ?pe-dest " pe podea " crlf)
)

(defrule mutare-pe-podea
	?scop <- (scop muta ?sursa pe podea)
	?stiva1 <- (stiva ?sursa $?rest)
	=>
	(retract ?scop ?stiva1)
	(assert (stiva ?sursa) (stiva $?rest))
	(printout t "Mutare #" ?*pas* " : Blocul " ?sursa " este mutat pe podea " crlf)
	(bind ?*pas* (+ ?*pas* 1))
)

(defrule sterge-stiva
	?podea <-(stiva)
	=>
	(retract ?podea)
)

(defrule mutare-de-pe-podea (declare (salience 10))
	?scop <- (scop muta ?bloc1 pe ?bloc2)
	?stiva1 <- (stiva ?bloc1)
	?stiva2 <- (stiva ?bloc2 $?rest2)
	(not (scop muta ?bloc2 pe ?)) ;important
	=>
	(retract ?scop ?stiva1 ?stiva2)
	(assert (stiva ?bloc1 ?bloc2 $?rest2) )
	(printout t "Mutare #" ?*pas* " : Blocul " ?bloc1 " este mutat pe blocul " ?bloc2 crlf)
	(bind ?*pas* (+ ?*pas* 1))
)
