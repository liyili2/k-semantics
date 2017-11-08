//This definition is rejected by K 4.0 but it is OK in K 3.6
//our K semantics will reject this definition as well.
//the correct behavior is to have kompile to reject this definition.
module TEST14-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST14
    imports TEST14-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int)
    syntax KItem ::= b(Int)
   
    rule k => a(2)
    rule A:KLabel(2) => b(2) [macro]

endmodule
