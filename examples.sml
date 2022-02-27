use "lang.sml";

TextIO.print "\n--- Reduce CHOICE ---\n";
printReduce (Choice(Seq(Skip,Skip), Seq(Assign("l", Integer 4), Skip)), [("l", 0)]);
TextIO.print "\n--- Typecheck CHOICE ---\n";
printTypecheck (Choice(Seq(Skip,Skip), Seq(Assign("l", Integer 4), Skip)), [("l", 0)]);

TextIO.print "\n--- Reduce PAR ---\n";
printReduce (Par(Seq(Skip,Assign("l", Integer 7)), Seq(Assign("l", Integer 4), Skip)), [("l", 0)]);
TextIO.print "\n--- Typecheck PAR ---\n";
printTypecheck (Par(Seq(Skip,Assign("l", Integer 7)), Seq(Assign("l", Integer 4), Skip)), [("l", 0)]);

TextIO.print "\n--- Reduce AWAIT False => True ---\n";
printReduce (Await(Seq(Assign("l", Op(Deref("l"), plus, Integer 1)), Op(Deref("l"), gt, Integer 5)), Skip), [("l", 0)]);
TextIO.print "\n--- Typecheck AWAIT False => True ---\n";
printTypecheck (Await(Seq(Assign("l", Op(Deref("l"), plus, Integer 1)), Op(Deref("l"), gt, Integer 5)), Skip), [("l", 0)]);

TextIO.print "\n--- Reduce AWAIT ---\n";
printReduce (Await(Op(Integer 1, gt, Integer 0), Seq(Assign("l", Integer 4), Assign("l", Op(Deref("l"), plus, Integer 1)))), [("l", 0)]);
TextIO.print "\n--- Typecheck AWAIT ---\n";
printTypecheck (Await(Op(Integer 1, gt, Integer 0), Seq(Assign("l", Integer 4), Assign("l", Op(Deref("l"), plus, Integer 1)))), [("l", 0)]);

TextIO.print "\n--- Reduce PAR + AWAIT ---\n";
printReduce (Par(Seq(Assign("m", Integer 42),Assign("l", Integer 7)), Await(Op(Deref("m"), gt, Integer 41), Seq(Assign("l", Integer 4), Assign("l", Op(Deref("l"), plus, Integer 1))))), [("l", 0), ("m", 1)]);
TextIO.print "\n--- Typecheck PAR + AWAIT ---\n";
printTypecheck (Par(Seq(Assign("m", Integer 42),Assign("l", Integer 7)), Await(Op(Deref("m"), gt, Integer 41), Seq(Assign("l", Integer 4), Assign("l", Op(Deref("l"), plus, Integer 1))))), [("l", 0), ("m", 1)]);

