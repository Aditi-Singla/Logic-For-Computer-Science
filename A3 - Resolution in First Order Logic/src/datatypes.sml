(* datatypes.sml *)

signature FOL = sig
	datatype Term = CONST of string
				|	VAR of string
				|	FUNC of string * Term list

	datatype Form = TOP1
				|	BOTTOM1
				|	PRED of string * Term list
				|	NOT1 of Form
				|	AND1 of Form * Form
				|	OR1 of Form * Form
				|	IMP1 of Form * Form
				|	IFF1 of Form * Form
				|	ITE1 of Form * Form * Form
				|	FORALL of string * Form
				|	EXISTS of string * Form

	datatype Quant = F of string | E of string
	datatype Lit =  P of string * Term list | N of string * Term list
	datatype Clause = CLS of (Lit list)
	datatype Cnf 	= CNF of (Clause list)

	val makePrenex : Form -> Form
	val makePCNF : Form -> Form
	val makeSCNF : Form -> Form
	val makeCNF : Form -> Cnf
	val unify : Form -> Form -> (Term * Term) list
	val resolve : Form -> bool
end

structure AST : FOL =
	struct
		datatype Term = CONST of string
					|	VAR of string
					|	FUNC of string * Term list

		datatype Form = TOP1
					|	BOTTOM1
					|	PRED of string * Term list
					|	NOT1 of Form
					|	AND1 of Form * Form
					|	OR1 of Form * Form
					|	IMP1 of Form * Form
					|	IFF1 of Form * Form
					|	ITE1 of Form * Form * Form
					|	FORALL of string * Form
					|	EXISTS of string * Form

		datatype Quant = F of string | E of string
		datatype Lit = P of string * Term list | N of string * Term list
		datatype Clause = CLS of (Lit list)
		datatype Cnf 	= CNF of (Clause list)

		fun simplify (TOP1) 		= TOP1
		| 	simplify (BOTTOM1) 		= BOTTOM1
		| 	simplify (PRED(s,l)) 	= PRED(s,l)
		| 	simplify (NOT1(p))		= NOT1(simplify(p))
		| 	simplify (AND1(p,q))	= AND1(simplify(p),simplify(q))
		| 	simplify (OR1(p,q))		= OR1(simplify(p),simplify(q))
		| 	simplify (IMP1(p,q)) 	= OR1(NOT1(simplify(p)),simplify(q))
		| 	simplify (IFF1(p,q))	= AND1(simplify(IMP1(p,q)),simplify(IMP1(q,p)))
		| 	simplify (ITE1(p,q,r))	= OR1(AND1(simplify(p),simplify(q)),AND1(NOT1(simplify(p)),simplify(r)))
		|	simplify (FORALL(s,p))	= FORALL(s,simplify(p))
		|	simplify (EXISTS(s,p))	= EXISTS(s,simplify(p));

		fun nnf (TOP1) 				= TOP1
		|	nnf (BOTTOM1) 			= BOTTOM1
		|	nnf (NOT1(TOP1)) 		= BOTTOM1
		|	nnf (NOT1(BOTTOM1)) 	= TOP1
		|	nnf (PRED(s,l)) 		= PRED(s,l)
		|	nnf (NOT1(PRED(s,l))) 	= NOT1(PRED(s,l))
		|	nnf (NOT1(NOT1(p))) 	= nnf(p)
		|	nnf (AND1(p,q)) 		= AND1(nnf(p),nnf(q))
		|	nnf (NOT1(AND1(p,q)))	= nnf(OR1(NOT1(p),NOT1(q)))
		|	nnf (OR1(p,q)) 			= OR1(nnf(p),nnf(q))
		|	nnf (NOT1(OR1(p,q))) 	= nnf(AND1(NOT1(p),NOT1(q)))
		|	nnf (FORALL(s,q))		= FORALL(s,nnf(q))
		|	nnf (NOT1(FORALL(s,q)))	= EXISTS(s,nnf(NOT1(q)))
		|	nnf (EXISTS(s,q))		= EXISTS(s,nnf(q))
		|	nnf (NOT1(EXISTS(s,q)))	= FORALL(s,nnf(NOT1(q)));

		fun subsStr v1 w1 p = case p of
							VAR(s) 		=> (if (s=v1) then VAR(w1) else VAR(s))
						|	FUNC(s,l) 	=> FUNC(s,(map (subsStr v1 w1) l))
						|	CONST(s)	=> CONST(s);
		
		fun substitute(v1,w1,p)	= case p of
							TOP1					=>	TOP1
						|	BOTTOM1					=>	BOTTOM1
						|	PRED(s,l)				=>	PRED(s, (map (subsStr v1 w1) l))
						|	NOT1(PRED(s,l))			=>	NOT1(PRED(s, (map (subsStr v1 w1) l)))
						|	AND1(p,q)				=>	AND1(substitute(v1,w1,p),substitute(v1,w1,q))
						|	OR1(p,q)				=>	OR1(substitute(v1,w1,p),substitute(v1,w1,q))
						|	FORALL(s,p)				=>	if (s=v1) then FORALL(s,p) else FORALL(s,substitute(v1,w1,p))
						|	EXISTS(s,p)				=>	if (s=v1) then EXISTS(s,p) else EXISTS(s,substitute(v1,w1,p));

		fun subsVar (v1,w1) p = case v1 of
								VAR(a)	  => (case p of
												VAR(s) 		=> (if (s=a) then w1 else p)
											|	FUNC(s,l) 	=> FUNC(s,(map (subsVar (v1,w1)) l))
											|	CONST(s)	=> p)
							|	FUNC(s,l) => p
							|	CONST(s)  => p;

		fun substituteVar(v1,w1,p)	= case p of
							TOP1					=>	TOP1
						|	BOTTOM1					=>	BOTTOM1
						|	PRED(s,l)				=>	PRED(s, (map (subsVar (v1,w1)) l))
						|	NOT1(PRED(s,l))			=>	NOT1(PRED(s, (map (subsVar (v1,w1)) l)))
						|	AND1(p,q)				=>	AND1(substituteVar(v1,w1,p),substituteVar(v1,w1,q))
						|	OR1(p,q)				=>	OR1(substituteVar(v1,w1,p),substituteVar(v1,w1,q));

		fun prenex (TOP1,c)				= (TOP1,c)
		|	prenex (BOTTOM1,c)			= (BOTTOM1,c)
		|	prenex ((PRED(s,l)),c)		= ((PRED(s,l)),c)
		|	prenex ((NOT1(PRED(s,l))),c)= ((NOT1(PRED(s,l))),c)
		|	prenex (AND1(p,q),c)		= (case (p,q) of
									(FORALL(s1,p1),FORALL(s2,q2)) => (FORALL(Int.toString c ^ "!",FORALL(Int.toString (c+1) ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(FORALL(s1,p1),EXISTS(s2,q2)) => (FORALL(Int.toString c ^ "!",EXISTS(Int.toString (c+1) ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(FORALL(s1,p1),_) 			  => (FORALL(Int.toString c ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),q))),c+1)
								|	(EXISTS(s1,p1),FORALL(s2,q2)) => (EXISTS(Int.toString c ^ "!",FORALL(Int.toString (c+1) ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(EXISTS(s1,p1),EXISTS(s2,q2)) => (EXISTS(Int.toString c ^ "!",EXISTS(Int.toString (c+1) ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(EXISTS(s1,p1),_) 			  => (EXISTS(Int.toString c ^ "!",(AND1(substitute(s1,Int.toString c ^ "!",p1),q))),c+1)
								|	(_,FORALL(s2,q2))			  => (FORALL(Int.toString c ^ "!",(AND1(p,substitute(s2,Int.toString c ^ "!",q2)))),c+1)
								|	(_,EXISTS(s2,q2))			  => (EXISTS(Int.toString c ^ "!",(AND1(p,substitute(s2,Int.toString c ^ "!",q2)))),c+1)
								|	(_,_)						  => (let
																		val (f1,c1) = prenex(p,c)
																		val (f2,c2) = prenex(q,c1)
																	in 
																		(AND1(f1,f2),c2)
																	end)
							)
		|	prenex (OR1(p,q),c)		= (case (p,q) of
									(FORALL(s1,p1),FORALL(s2,q2)) => (FORALL(Int.toString c ^ "!",FORALL(Int.toString (c+1) ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(FORALL(s1,p1),EXISTS(s2,q2)) => (FORALL(Int.toString c ^ "!",EXISTS(Int.toString (c+1) ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(FORALL(s1,p1),_) 			  => (FORALL(Int.toString c ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),q))),c+1)
								|	(EXISTS(s1,p1),FORALL(s2,q2)) => (EXISTS(Int.toString c ^ "!",FORALL(Int.toString (c+1) ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(EXISTS(s1,p1),EXISTS(s2,q2)) => (EXISTS(Int.toString c ^ "!",EXISTS(Int.toString (c+1) ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),substitute(s2,Int.toString (c+1) ^ "!",q2))))),c+2)
								|	(EXISTS(s1,p1),_) 			  => (EXISTS(Int.toString c ^ "!",(OR1(substitute(s1,Int.toString c ^ "!",p1),q))),c+1)
								|	(_,FORALL(s2,q2))			  => (FORALL(Int.toString c ^ "!",(OR1(p,substitute(s2,Int.toString c ^ "!",q2)))),c+1)
								|	(_,EXISTS(s2,q2))			  => (EXISTS(Int.toString c ^ "!",(OR1(p,substitute(s2,Int.toString c ^ "!",q2)))),c+1)
								|	(_,_)						  => (let
																			val (f1,c1) = prenex(p,c)
																			val (f2,c2) = prenex(q,c1)
																		in 
																			(OR1(f1,f2),c2)
																		end)
							)
		|	prenex (FORALL(s,p),c) = (let 
										val (f,c1) = prenex(p,c) 
									in
										(FORALL(s,f),c1)
									end)
		|	prenex (EXISTS(s,p),c) = (let
										val (f,c1) = prenex(p,c)
									in
										(EXISTS(s,f),c1)
									end);

		fun prenex1 f c = let
							val (f1,c1) = prenex(f,c)
						in
							(if (c = c1) then f1 else prenex1 f1 c1) 
						end;

		fun prenex2 f 	= prenex1 f 0;
		
		(*Takes in ordinary formula and gives PNF*)
		val makePrenex = prenex2 o nnf o simplify;

		(*Assumes prenex normal form*)
		fun formToList (FORALL(s,p),l) = formToList (p,F(s)::l)
		|	formToList (EXISTS(s,p),l) = formToList (p,E(s)::l)
		|	formToList (f,l)		   = (rev l,f);

		fun listToForm [] f 		= f 
		|	listToForm (F(s)::xs) f = FORALL(s,(listToForm xs f))
		|	listToForm (E(s)::xs) f = EXISTS(s,(listToForm xs f));

		(*Get CNF*)
		fun distOR (a,AND1(b,c)) = AND1(distOR(a,b),distOR(a,c))
		|	distOR (AND1(b,c),a) = AND1(distOR(b,a),distOR(c,a))
		|	distOR (a,b) 		= OR1(a,b);
		
		fun conjOfDisj (AND1(a,b)) = AND1(conjOfDisj(a),conjOfDisj(b))
		|	conjOfDisj (OR1(a,b))  = distOR(conjOfDisj(a),conjOfDisj(b))
		|	conjOfDisj (a) 		  = a;

		fun getCnf f = (let
							val (l,f1) = formToList(f,[])
							val f2 = conjOfDisj(f1)
						in
							(l,f2)
						end);

		fun getPcnf f = (let 
							val (l,f1) = getCnf f
						in
							listToForm l f1
						end);

		(*Takes in PNF and gives PCNF*)
		val makePCNF = getPcnf;

		fun makeVar v = case v of
							F(s) => VAR(s)
						|	E(s) => VAR(s);

		fun skolem (l1,l2,f,c) = case l1 of
							[]		=>	(rev l2,f)
						|	F(s)::l =>	skolem (l,F(s)::l2,f,c)
						|	E(s)::l =>	if (l2=[]) then
											(let
												val g = CONST(Int.toString c ^ "#")
												val f1 = substituteVar(VAR(s),g,f)
											in
												skolem(l,l2,f1,c+1)											
											end)
										else
											(let
												val g = FUNC(Int.toString c ^ "#",(map (makeVar) l2))
												val f1 = substituteVar(VAR(s),g,f)
											in
												skolem(l,l2,f1,c+1)											
											end);

		fun getScnf f = let
							val (l,f1) = formToList(f,[])
							val (l1,f2) = skolem(l,[],f1,0)
							val f3 = conjOfDisj(f2)
						in
							(l1,f3)
						end

		fun getScnf1 f = let
							val (l,f1) = getScnf f
						in	
							listToForm l f1
						end

		(*Takes in PNF and gives SCNF*)
		val makeSCNF = getScnf1;

		(*Obtain List of Clauses for resolution*)
		fun flattenOR (OR1(p,q))  = (let
										val (p1,p2) = flattenOR p
										val (q1,q2) = flattenOR q
									in
										(if (p1 andalso q1) then (true,(p2 @ q2)) else (false,[]))
									end)	
			
		|	flattenOR (PRED(s,l)) 	 	= (true,[P(s,l)])
		|	flattenOR (NOT1(PRED(s,l))) = (true,[N(s,l)])
		|	flattenOR (TOP1) 		 	= (false,[])
		|	flattenOR (BOTTOM1) 	 	= (true,[]);

		fun flattenAND (AND1(p,q)) 	= ((flattenAND p) @ (flattenAND q))
		|	flattenAND (TOP1)		= []
		|	flattenAND (BOTTOM1)	= ([CLS([])])
		|	flattenAND (p) 			= (let
											val (p1,p2) = flattenOR p
										in
											(if (p1) then ([CLS(p2)]) else [])
										end);

		fun getcnfl p = CNF(flattenAND(p));

		(* FINALLY GIVES THE LIST OF CLAUSES WHICH NEED TO RESOLVED *)
		fun makeCnf f = let
							val (l1,f1) = getScnf(makePrenex(f)) 
						in
							getcnfl f1
						end;

		val makeCNF = makeCnf;

		fun renameVarTerm c t = case t of
							CONST(s)	=> t
						|	VAR(s)		=> VAR(Int.toString c ^ s)
						|	FUNC(s,l) 	=> FUNC(s,(map (renameVarTerm c) l));

		fun renameVarLit c l = case l of
							P(s,l)	=> P(s,(map (renameVarTerm c) l))
						|	N(s,l)	=> N(s,(map (renameVarTerm c) l));

		fun renameVarClause (c,cl) = case cl of
							CLS(l)	=> CLS(map (renameVarLit c) l);

		fun pairup ([],c,l) 	= rev l
		|	pairup (x::xs,c,l)	= pairup(xs,c+1,(c,x)::l)

		fun renameVarCnf cnf = case cnf of
							CNF(l)	=> (let
											val l1 = pairup(l,0,[])
										in
											CNF(map renameVarClause l1)	
										end);

		fun checkOccur a t = case t of
								CONST(x)	=> false
							|	VAR(x)		=> (a=x)
							|	FUNC(s,l)	=> List.exists (checkOccur a) l;
		

		fun setSubstitution (l,subs) = case subs of
								[]		=> l
							|	z::zs	=> setSubstitution((map (subsVar z) l),zs);

		fun unifyTermList [] [] 		  = (true,[])
		|	unifyTermList (x::xs) (y::ys) = let
												fun mgu (r,s) = ( case (r,s) of
														(CONST(a),CONST(b)) => (a=b,[])
													|	(CONST(a),VAR(b))	=> (true,[(VAR(b),CONST(a))])
													|	(CONST(a),FUNC(b,l))=> (false,[])
													|	(VAR(a),CONST(b))	=> (true,[(VAR(a),CONST(b))])
													|	(VAR(a),VAR(b))		=> (if (a=b) then (true,[]) else (true,[(VAR(a),VAR(b))]))
													|	(VAR(a),FUNC(b,l))	=> if (checkOccur a (FUNC(b,l))) then (false,[]) else (true,[(VAR(a),FUNC(b,l))])
													|	(FUNC(a,l),CONST(b))=> (false,[])
													|	(FUNC(a,l),VAR(b))	=> mgu (VAR(b),FUNC(a,l))
													|	(FUNC(a,l),FUNC(b,m))=> if (a = b) then (unifyTermList l m) else (false,[])

												)
												val (b,mgu1) = mgu (x,y)
											in
												if b then 
												(
													let 
														val xs1 = setSubstitution(xs,mgu1)
														val ys1 = setSubstitution(ys,mgu1)
														val (b1,l) = unifyTermList xs1 ys1
													in
														(if b1 then (b1,mgu1 @ l) else (b1,[]))
													end
												)
												else (false,[])
											end;

		fun unifyPreds(P(s1,l1),N(s2,l2)) =	if (s1=s2) then
												(if (length l1 = length l2) then (unifyTermList l1 l2) else (false,[]))
											else (false,[])
		|	unifyPreds(N(s1,l1),P(s2,l2)) = unifyPreds(P(s2,l2),N(s1,l1))
		|	unifyPreds(P(s1,l1),P(s2,l2)) = (false,[])
		|	unifyPreds(N(s1,l1),N(s2,l2)) = (false,[]);

		fun unification p1 p2 = let
									val q1 = renameVarCnf (makeCNF(makeSCNF(makePrenex p1)))
									val q2 = renameVarCnf (makeCNF(makeSCNF(makePrenex p2)))
									val CNF([(CLS([r1]))]) = q1
									val CNF([(CLS([r2]))]) = q2
									val (b,unifier) = unifyPreds(r1,r2)	
								in
									unifier
								end;

		val unify = unification;

		fun isPositive x = case x of
						P(s,l) => true
					|	N(s,l) => false;

		fun setSubstitutionPred subs (P(s,l)) = P(s,setSubstitution(l,subs))
		|	setSubstitutionPred subs (N(s,l)) = N(s,setSubstitution(l,subs))

		fun resolution [] [] n nl pl maxH 					= false
		|	resolution (x::xs) [] n nl pl maxH 				= resolution xs pl n (nl@[x]) [] maxH
		|	resolution [] ((CLS(y))::ys) n nl pl maxH 		= false
		|	resolution (x::xs) ((CLS(y))::ys) n nl pl maxH	= 	if (n <= maxH) then(
																	let
																		val ((pos::px),neg) = List.partition isPositive y
																		val (b,mgu) = unifyPreds(x,pos)
																	in
																		if b then
																			let
																				val remlist = (xs @ nl @ neg)
																				val resolvant = map (setSubstitutionPred mgu) remlist
																			in
																				if length resolvant = 0 then true 
																				else(
																					let
																						val b1 = (resolution resolvant (pl@((CLS(y))::(ys))) (n+1) [] [] maxH)
																					in
																						if b1 then true else (resolution (x::xs) (ys) n nl (pl@[(CLS(y))]) maxH)
																					end
																				)
																			end
																		else
																			resolution (x::xs) ys n nl (pl@[(CLS(y))]) maxH
																	end
																)
																else false

		fun resolution1 nl pl p = if (length nl = 0 orelse length pl = 0) then false
								else
									case nl of
										[] 				=> false
									|	(CLS(x))::xs 	=> (let
																val b = resolution x pl 0 [] [] p
															in
																if b then true else resolution1 xs pl p
															end)

		fun isProgramClause (CLS([])) 	 = false
		|	isProgramClause (CLS(x::xs)) = (isPositive x) orelse isProgramClause (CLS(xs));

		fun isEmptyClause (CLS(l)) = (length l = 0);

		fun resolution2 (CNF(clslist)) = 	let
												val (pos,neg) = List.partition isProgramClause clslist
												val b = List.exists isEmptyClause neg
											in
												if b then false else (resolution1 neg pos 60)
											end

		fun resolution3 formula = resolution2(renameVarCnf(makeCNF(makeSCNF(makePrenex(formula)))));

		val resolve = not o resolution3;
end;