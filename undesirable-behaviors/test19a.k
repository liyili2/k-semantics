//test19a.k
module TEST19A-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST19A
    imports TEST19A-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><store> .Map </store></T>

    syntax KItem ::= Int
    syntax KItem ::= "a"
    syntax KItem ::= "b" | c(Int,Int,Int)

    rule <k> k => a ...</k> <store> M:Map[a <- 2]</store>
    rule <k> a => b ...</k> <store> M:Map[a <- 2]</store>
    rule <k> b => X ...</k> <store>... a |-> X:K ...</store>
endmodule
