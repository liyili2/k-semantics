//commutativity pattern matching in set fails. Should allow A -> 3, B -> 2
module TEST2-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST2
    imports TEST2-SYNTAX

    configuration <T> <k> $PGM:Pgm </k> </T>

    syntax KItem ::= tuple(K, K, K) | aSet(Set)

    rule k => aSet(SetItem(tuple(3,3,3)) SetItem(tuple(5,6,7)) SetItem(tuple(1,2,3)) SetItem(tuple(3,2,2)) SetItem(tuple(2,2,1)))
    rule aSet(SetItem(tuple(A:K, B:K, 2)) S:Set) => .K

endmodule
