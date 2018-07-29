(* datatypes.sml *)
(* As specified in the statement *)
signature AST = sig
	datatype Prop = TOP
				|	BOTTOM
				|	ATOM of string
				|	NOT of Prop
				|	AND of Prop * Prop
				|	OR of Prop * Prop
				|	IMP of Prop * Prop
				|	IFF of Prop * Prop
				|	ITE of Prop * Prop * Prop
	val toPrefix	: Prop -> string
	val toPostfix	: Prop -> string
	val isEqual		: Prop -> Prop -> bool
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
end;