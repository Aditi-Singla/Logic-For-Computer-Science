Control.Print.printDepth := 1000;

use "datatypes.sml";
open AST;

(* Test cases for PNF, PCNF, & SCNF

val v0 = (FORALL("z", (EXISTS("u", (AND1(OR1(FORALL("r", (EXISTS("p", (PRED("W",[FUNC("f3",[FUNC("f4",[VAR("x"),VAR("p")]),VAR("r")])]))))),(PRED("P",[VAR("x")]))), (PRED("Q",[FUNC("f", [VAR("y"),VAR("u"),VAR("z")])]))))))));
val v1 = (EXISTS("u", (AND1(OR1(FORALL("r", (EXISTS("p", (PRED("W",[FUNC("f3",[FUNC("f4",[VAR("x"),VAR("p")]),VAR("r")])]))))),(PRED("P",[VAR("x")]))), (PRED("Q",[FUNC("f", [VAR("y"),VAR("u"),VAR("z")])]))))));

val v2 = makePrenex v1;
val v3 = makePCNF v2;
val v4 = makeSCNF v2;
val v5 = makeCNF v1;
*)

(* Test cases for unification

val p1 = PRED ("Q",[FUNC("f3",[FUNC("f4",[(FUNC("f5",[VAR("7")])),VAR("7")]), VAR("9")])]);
val p2 = PRED ("P",[FUNC("f5",[(VAR("7"))])]);
val p3 = PRED("Q",[FUNC("f5",[(VAR("7"))]), VAR("7")] );
val p4 = NOT1(PRED ("P",[FUNC("f5",[(VAR("23"))])]));
val p5 = NOT1(PRED ("Q",[FUNC("f5",[(VAR("17") )]), VAR("17")] ));

val l1 = unify p1 p2;
val l2 = unify p1 p3;
val l3 = unify p2 p4;
val l4 = unify p3 p5;
val l5 = unify p1 p5;

val w1 = NOT1(PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])]));
val w2 = PRED("p", [VAR("x")]);
val w3 = PRED("p", [FUNC("+1", [VAR("x")])]);

val wb1 = unify w1 w2;
val wb2 = unify w1 w3;
*)

(*Test cases for resolution*)

val v61 = (AND1
			(NOT1
				(PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])])), 
			AND1(
				PRED("p", [CONST("0")]), 
				FORALL("x", IMP1(
								PRED("p", [VAR("x")]),
								PRED("p", [FUNC("+1", [VAR("x")])])
								)
					)
				)
			)
		);

val v7 = makePrenex v61;
val v8 = makePCNF v7;
val v9 = makeSCNF v7;
val v10 = makeCNF v9;
val b = resolve v61;

val v62 = (AND1
			(NOT1(PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])])), 
			AND1(
				PRED("p", [CONST("0")]), 
				FORALL("x", IMP1(
								PRED("p", [FUNC("+1", [VAR("x")])]),
								PRED("p", [VAR("x")])
								)
					)
				)
			)
		);

val v7 = makePrenex v62;
val v8 = makePCNF v7;
val v9 = makeSCNF v7;
val v10 = makeCNF v9;
val b = resolve v62;

val v63 = (OR1	
			(BOTTOM1,
			AND1
				(NOT1(PRED("p", [FUNC("+1", [FUNC("+1", [FUNC("+1", [CONST("0")])])])])), 
				AND1(
					PRED("p", [CONST("0")]), 
					FORALL("x", IMP1(
									PRED("p", [FUNC("+1", [VAR("x")])]),
									PRED("p", [VAR("x")])
									)
						)
					)
				)
			)
		);

val v7 = makePrenex v63;
val v8 = makePCNF v7;
val v9 = makeSCNF v7;
val v10 = makeCNF v9;
val b = resolve v63;

val p1 = FORALL("x", FORALL("y", FORALL("z", AND1(PRED("q", [VAR("x"), VAR("y")]), PRED("q", [VAR("y"), VAR("z")])))));
val p2 = FORALL("x", FORALL("y", IMP1(PRED("q", [VAR("x"), VAR("y")]) ,PRED("q", [VAR("y"), VAR("x")]) )));
val s1 = FORALL("x", FORALL("y", FORALL("z", AND1(PRED("q", [VAR("x"), VAR("y")]), PRED("q", [VAR("z"), VAR("y")])))));
val v62 = AND1(AND1(NOT1(p1),p2),s1);

val v7 = makePrenex v62;
val v8 = makePCNF v7;
val v9 = makeSCNF v7;
val v10 = makeCNF v9;
val b = resolve v62;

OS.Process.exit(OS.Process.success);