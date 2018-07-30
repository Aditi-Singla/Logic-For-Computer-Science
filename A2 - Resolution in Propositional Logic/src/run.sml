Control.Print.printDepth := 1000;

CM.make "lcs.cm";
open AST;

val list_arg = CommandLine.arguments();

fun run (infile:string, outfile:string) = 
	let fun printFile (str:string) =
			let val f = TextIO.openOut outfile
			in 	(TextIO.output (f, str); TextIO.closeOut f) 
			end
		val parsetrees = Lcs.parser infile
		val output = Lcs.fileOutput parsetrees
	in printFile (output)
	end

val out = run(hd (list_arg), hd (tl list_arg));
OS.Process.exit(OS.Process.success);