//test17a.k
module TEST17A-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST17A
    imports TEST17A-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= Int
    syntax KItem ::= a(K)
    syntax KItem ::= b(K)
   
    syntax Ints ::= List{Int,","}
    rule k => a(1,2,3,4,5)
    rule a(`_,_`(I:Ints, 5)) => .K

endmodule
