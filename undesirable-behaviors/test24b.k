//test24b.K
module TEST24B-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST24B
    imports TEST24B-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function]
    syntax KItem ::= b(Int) | c(Int) | "good"
   
    rule k => c(2)
    rule c(A:Int) => a(A)
    rule a(1) => 1
    //rule a(2) => 2
    rule a(3) => 3
    rule a(A:Int) => good [owise]

    rule a(2) => b(2)

endmodule
