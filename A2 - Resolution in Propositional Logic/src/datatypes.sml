(* datatypes.sml *)
signature AST = sig
	datatype Prop 	= TOP
					| BOTTOM
					| ATOM of string
					| NOT of Prop
					| AND of Prop * Prop
					| OR of Prop * Prop
					| IMP of Prop * Prop
					| IFF of Prop * Prop
					| ITE of Prop * Prop * Prop
	datatype Lit 	= P of string
					| N of string
	datatype Clause = CLS of (Lit list)
	datatype Cnf 	= CNF of (Clause list)
	val toPrefix	: Prop -> string
	val toPostfix	: Prop -> string
	val isEqual		: Prop -> Prop -> bool
	val makeCnf 	: Prop -> Cnf
	val resolve 	: Cnf -> bool

end

structure AST : AST =
	struct
		datatype Prop = TOP
				|	BOTTOM
				|	ATOM of string
				|	NOT of Prop
 				|	AND of Prop * Prop
				|	OR of Prop * Prop
				|	IMP of Prop * Prop
				|	IFF of Prop * Prop
				|	ITE of Prop * Prop * Prop
		datatype Lit = P of string
					| N of string
		datatype Clause = CLS of (Lit list)
		datatype Cnf 	= CNF of (Clause list)

		fun preOrder (TOP) 			= ("TOP") 
		|	preOrder (BOTTOM) 		= ("BOTTOM")
		|	preOrder (ATOM(s)) 		= (s) 
		|	preOrder (NOT(a)) 		= ("NOT ") ^ preOrder (a)
		|	preOrder (AND(a,b))		= ("AND ") ^ preOrder (a) ^ (" ") ^ preOrder (b)
		|	preOrder (OR(a,b))		= ("OR ") ^ preOrder (a) ^ (" ") ^ preOrder (b)
		|	preOrder (IMP(a,b))		= ("IMP ") ^ preOrder (a) ^ (" ") ^ preOrder (b)
		|	preOrder (IFF(a,b)) 	= ("IFF ") ^ preOrder (a) ^ (" ") ^ preOrder (b)
		|	preOrder (ITE(a,b,c))	= ("ITE ") ^ preOrder (a) ^ (" ") ^ preOrder (b) ^ (" ") ^ preOrder (c);

		fun postOrder (TOP) 		= ("TOP") 
		|	postOrder (BOTTOM) 		= ("BOTTOM")
		|	postOrder (ATOM(s)) 	= (s) 
		|	postOrder (NOT(a)) 		= postOrder (a) ^ (" NOT")
		|	postOrder (AND(a,b))	= postOrder (a) ^ (" ") ^ postOrder (b) ^ (" AND")
		|	postOrder (OR(a,b))		= postOrder (a) ^ (" ") ^ postOrder (b) ^ (" OR")
		|	postOrder (IMP(a,b))	= postOrder (a) ^ (" ") ^ postOrder (b) ^ (" IMP")
		|	postOrder (IFF(a,b)) 	= postOrder (a) ^ (" ") ^ postOrder (b) ^ (" IFF")
		|	postOrder (ITE(a,b,c))	= postOrder (a) ^ (" ") ^ postOrder (b) ^ (" ") ^ postOrder (c) ^ (" ITE");

		fun equals TOP TOP 							= true 
		|	equals BOTTOM BOTTOM 					= true
		|	equals (ATOM(s1)) (ATOM(s2)) 			= (s1 = s2)
		|	equals (NOT(a1)) (NOT(a2))				= equals a1 a2
		|	equals (AND(a1,b1)) (AND(a2,b2))		= (equals a1 a2) andalso (equals b1 b2)
		|	equals (OR(a1,b1)) (OR(a2,b2))			= (equals a1 a2) andalso (equals b1 b2)
		|	equals (IMP(a1,b1)) (IMP(a2,b2))		= (equals a1 a2) andalso (equals b1 b2)
		|	equals (IFF(a1,b1)) (IFF(a2,b2))		= (equals a1 a2) andalso (equals b1 b2)
		|	equals (ITE(a1,b1,c1)) (ITE(a2,b2,c2))	= (equals a1 a2) andalso (equals b1 b2) andalso (equals c1 c2)
		|	equals _ _ 								= false;

		val toPrefix = preOrder;
		val toPostfix = postOrder;
		val isEqual = equals;

		(*Acknowledgement : The code for CNF has been borrowed from the slides with some modifications*)

		fun simplify (TOP) 			= TOP
		| 	simplify (BOTTOM) 		= BOTTOM
		| 	simplify (ATOM s) 		= ATOM s
		| 	simplify (NOT(a))		= NOT(simplify(a))
		| 	simplify (AND(a,b))		= AND(simplify(a),simplify(b))
		| 	simplify (OR(a,b))		= OR(simplify(a),simplify(b))
		| 	simplify (IMP(a,b)) 	= OR(NOT(simplify(a)),simplify(b))
		| 	simplify (IFF(a,b))		= AND(simplify(IMP(a,b)),simplify(IMP(b,a)))
		| 	simplify (ITE(a,b,c))	= OR(AND(simplify(a),simplify(b)),AND(NOT(simplify(a)),simplify(c)));

		fun nnf (TOP) 			= TOP
		|	nnf (BOTTOM) 		= BOTTOM
		|	nnf (NOT(TOP)) 		= BOTTOM
		|	nnf (NOT(BOTTOM)) 	= TOP
		|	nnf (ATOM a) 		= ATOM a
		|	nnf (NOT(ATOM a)) 	= NOT(ATOM a)
		|	nnf (NOT(NOT(a))) 	= nnf(a)
		|	nnf (AND(a,b)) 		= AND(nnf(a),nnf(b))
		|	nnf (NOT(AND(a,b))) = nnf(OR(NOT(a),NOT(b)))
		|	nnf (OR(a,b)) 		= OR(nnf(a),nnf(b))
		|	nnf (NOT(OR(a,b))) 	= nnf(AND(NOT(a),NOT(b)));

		fun distOR (a,AND(b,c)) = AND(distOR(a,b),distOR(a,c))
		|	distOR (AND(b,c),a) = AND(distOR(b,a),distOR(c,a))
		|	distOR (a,b) 		= OR(a,b);
		
		fun conjOfDisj (AND(a,b)) = AND(conjOfDisj(a),conjOfDisj(b))
		|	conjOfDisj (OR(a,b))  = distOR(conjOfDisj(a),conjOfDisj(b))
		|	conjOfDisj (a) 		  = a;

		val getcnf = conjOfDisj o nnf o simplify;

		fun flattenOR (OR(a,b))		= (let
											val (a1,a2) = flattenOR a
											val (b1,b2) = flattenOR b
										in
											(if (a1 andalso b1) then (true,(a2 @ b2)) else (false,[]))
										end)	
			
		|	flattenOR (ATOM a) 		= (true,[P(a)])
		|	flattenOR (NOT(ATOM a)) = (true,[N(a)])
		|	flattenOR (TOP) 		= (false,[])
		|	flattenOR (BOTTOM) 		= (true,[]);

		fun flattenAND (AND(b,c)) 	= ((flattenAND b) @ (flattenAND c))
		|	flattenAND (TOP)		= []
		|	flattenAND (BOTTOM)		= ([CLS([])])
		|	flattenAND (a) 			= (let
											val (a1,a2) = flattenOR a
										in
											(if (a1) then ([CLS(a2)]) else [])
										end);

		fun getcnfl(a) = CNF(flattenAND(getcnf(a)));

		val makeCnf = getcnfl;

		(*Cleanup*)

		fun match x y = case (x,y) of
						(P(a),P(b)) => (a = b)
					|	(N(a),N(b)) => (a = b)
					|	(_,_)		=> false;

		fun negate (P(a)) = (N(a))
		|	negate (N(a)) = (P(a)); 

		fun duplicateRemoval (c:Lit list) = case c of
								  x::xs	=>  (let
												val (pos,neg) = List.partition (match x) xs
											in
												x::(duplicateRemoval(neg))
											end)
								| []	=> [];

		fun complimentRemoval (c:Lit list) = case c of
								  x::xs	=> (let
												val b = List.exists (match (negate(x))) xs
											in
												(if b then false else complimentRemoval(xs)) 
											end)
								| []		=> true;

		fun cleanup1 (clist:Clause list) = case clist of
									CLS(x)::xs	=>	(let
														val l1 = duplicateRemoval(x)
														val b = complimentRemoval(l1)
														val tail = cleanup1(xs)
													in
														(if b then CLS(l1)::tail else tail)
													end)
								|	[]			=>	[];

		fun isSuperSet a b = case (a,b) of
								(CLS([]),CLS([]))		=>	true
							|	(CLS(x::xs),CLS([]))	=>	false
							|	(CLS([]),CLS(x::xs))	=>	true
							|	(CLS(x::xs),CLS(y::ys))	=>	(let
																val (pos,neg) = List.partition (match x) (y::ys)
															in
																(if (length pos = 0) then false else isSuperSet (CLS(xs)) (CLS(neg)))
															end)

		fun removeSuperSet (clist:Clause list) = case clist of
													CLS(x)::xs	=>	(let
																		val (pos,neg) = List.partition (isSuperSet (CLS(x))) xs
																	in
																		(CLS(x)::(removeSuperSet(neg)))
																	end)
												|	[]			=>	[];

		fun cleanup (CNF(clist): Cnf) = (let
											val clist1 = cleanup1(clist)
											val clist2 = removeSuperSet(clist1)
										in
											CNF(clist2)
										end)
		
		(*Resolution*)

		fun containsEmptyClause cnf = case cnf of
										x::xs => if (x=CLS([])) then true else (containsEmptyClause xs)
									|	[]	  => false;		

		fun contains p (CLS(litlist)) = (List.exists (match p) litlist);
		
		fun containsatom p (CLS(litlist)) = ((List.exists (match p) litlist) orelse (List.exists (match (negate(p))) litlist));

		fun remove p (CLS(plist)) = (let
										val (pos,neg) = List.partition (match p) plist
									in
										(CLS(neg))	
									end);

		fun appendl a (CLS(b)) = (CLS(a @ b)); 

		fun getUnion (pos, neg, p) = (let
										val pos1 = map (remove p) pos
										val neg1 = map (remove (negate(p))) neg
									in
										(case pos1 of
											CLS(y)::ys 	=> (map (appendl y) neg1) @ (getUnion(ys,neg1,p))
										| 	[]	  		=> []
										)										
									end)

		fun resolve1 (CNF(cnf), p) = (let
										val (yes,no) = List.partition (containsatom p) cnf
										val (pos,neg) = List.partition (contains p) yes
										val delta = getUnion(pos,neg,p)
									in
										CNF(delta @ no)
									end)

		fun mergeClauses (cnf) = case cnf of
								CLS(x)::xs  => x @ mergeClauses(xs)
							|	[]			=> [];

		fun getComplimentaryPairs (litList) = case litList of
								x::xs => if (List.exists (match (negate x)) xs) then (true,x) else getComplimentaryPairs(xs)
							|	[]	  => (false,P(""));						 

		fun resolve (CNF(cnf)) = if (cnf = []) then true
								else if (containsEmptyClause cnf) then
									false
								else 
									(let
										val (b,p) = getComplimentaryPairs(mergeClauses(cnf))
									in
										(if (b=false) then
											true
										else
											(let
												val cnf1 = resolve1(CNF(cnf),p)
												val cnf2 = cleanup(cnf1)
											in
												resolve(cnf2)
											end))
									end);
end;