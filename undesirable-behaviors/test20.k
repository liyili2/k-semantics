//K built-in mapping function cannot 
//expected result: k cell has value 1 and Map has a maps to 1
module TEST20-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST20
    imports MAP
    imports TEST20-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><store> .Map </store></T>

    syntax KItem ::= Int
    syntax KItem ::= "a"
    syntax KItem ::= "b" | c(Int,Int,Int)

    rule <k> k => a ...</k> <store> M:Map (.Map => (a |-> 2))</store>
    rule <k> a => b ...</k> <store> M:Map[a <- 1]</store>
    rule <k> b => X ...</k> <store>... a |-> X:K ...</store>
endmodule
