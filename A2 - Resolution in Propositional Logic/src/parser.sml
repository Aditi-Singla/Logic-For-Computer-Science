structure Lcs  :
	sig
		val parser : string -> AST.Prop list
		val fileOutput : AST.Prop list -> string
	end
= struct 
	exception LcsError;
	structure LcsLrVals = LcsLrValsFun(
		structure Token = LrParser.Token)
	structure LcsLex = LcsLexFun(
		structure Tokens = LcsLrVals.Tokens);
	structure LcsParser = Join(
		structure LrParser = LrParser
		structure ParserData = LcsLrVals.ParserData
		structure Lex = LcsLex)

	val invoke = fn lexstream =>
		let val print_error = fn (str,pos,_) =>
			TextIO.output(TextIO.stdOut,
				"***Lcs Parser Error at character position " ^ (Int.toString pos) ^ "*** " ^ str ^ "\n")
		in LcsParser.parse(0,lexstream,print_error,())
		end
		
	fun newLexer fcn = 
		let val lexer = LcsParser.makeLexer fcn
			val _ = LcsLex.UserDeclarations.init()
		in lexer
		end

	fun stringToLexer str = (* creates a lexer from a string *)
		let val done = ref false
		in newLexer (fn n => if (!done) then "" else (done := true; str))
		end

	fun lexerToParser (lexer) = (* creates a parser from a lexer *)
		let val dummyEOF = LcsLrVals.Tokens.EOF(0,0)
			val (result,lexer) = invoke lexer
			val (nextToken,lexer) = LcsParser.Stream.get lexer
		in 
			if LcsParser.sameToken(nextToken,dummyEOF) then
				result
			else (TextIO.output(TextIO.stdOut,"*** LCS PARSER WARNING -- unconsumed input ***\n");
				result)
		end

	val parseString = lexerToParser o stringToLexer (* parses a string *)

	fun parser (filename : string) =
		let val ins = TextIO.openIn filename
			fun parsetree ins = case TextIO.inputLine ins of
						SOME line 	=> (let
											val ans = parseString(line)
										in
											ans::parsetree ins
										end
										handle LcsParser.ParseError => parsetree ins
									)
						| NONE		=> []	
		in parsetree ins before TextIO.closeIn ins
		end

	fun fileOutput (treelist) = case treelist of
						  x::xs	=> if AST.resolve(AST.makeCnf(x)) then "True\n" ^ (fileOutput xs) else "False\n" ^ (fileOutput xs)
						| [] 	=> "";
	
end (* struct *)