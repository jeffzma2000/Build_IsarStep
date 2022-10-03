fun printToOutStream outstream str = let val os = outstream
                                     in
                                       TextIO.output(os,str);
                                       TextIO.flushOut os;
                                       TextIO.closeOut os
                                     end;
val os = TextIO.openOut "./testfile.txt";
val r = printToOutStream os "Hello SML IO";     


fun copyTextFile(infile: string, outfile: string) =
  let
    val ins = TextIO.openIn infile
    val outs = TextIO.openOut outfile
    fun helper(copt: char option) =
      case copt of
           NONE => (TextIO.closeIn ins; TextIO.closeOut outs)
         | SOME(c) => (TextIO.output1(outs,c); helper(TextIO.input1 ins))
  in
    helper(TextIO.input1 ins)
  end;
