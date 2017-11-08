//The current K implementation's built-in mapping function fails.
//The effect is universal. The mapping function should
//be able to insert two to parameter a. After running the program
//the result is b in the k cell and empty map in the Map.
//If we insert the rule: rule <k> b => X ...</k> <store>... a |-> X:K ...</store>
//the result will be k in the k cell and empty map in the Map,
//which is also unexpected providing that the test19.k actually goes through
//k => a => b
//It should have a result of b in the k cell and a |-> 2 in the map.
module TEST19-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST19
    imports TEST19-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><store> .Map </store></T>

    syntax KItem ::= Int
    syntax KItem ::= "a"
    syntax KItem ::= "b" | c(Int,Int,Int)

    rule <k> k => a ...</k> <store> M:Map[a <- 2]</store>
    rule <k> a => b ...</k> <store> M:Map[a <- 2]</store>
    //rule <k> b => X ...</k> <store>... a |-> X:K ...</store>
endmodule
