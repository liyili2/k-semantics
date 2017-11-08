//commutativity pattern matching in set fails. Should allow A -> 2, B -> 2, C -> 3, D -> 3 
module TEST1-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST1
    imports TEST1-SYNTAX

    configuration <T> <k> $PGM:Pgm </k> </T>

    syntax KItem ::= tuple(K, K, K) | aSet(Set)

    rule k => aSet(SetItem(tuple(2,2,1)) SetItem(tuple(3,3,3)) SetItem(tuple(5,6,7)) SetItem(tuple(1,2,3)) SetItem(tuple(3,2,2)) )
    rule aSet(SetItem(tuple(A:K, B:K, 1)) SetItem(tuple(C:K, C:K, D:K)) S:Set) => .K

endmodule
