//In this program, K 3.6 fails to detect that the Map (a |-> 1) and (a |-> 2) is ill form. 
//Should not be able to compile.
module TEST21-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST21
    imports MAP
    imports TEST21-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><store> .Map </store></T>

    syntax KItem ::= Int
    syntax KItem ::= "a"
    syntax KItem ::= "b" | "c" | "d"

    rule <k> k => a ...</k> <store> M:Map (.Map => (a |-> 1) (a |-> 2))</store>

endmodule
