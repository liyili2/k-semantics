//Interestingly, K passes this file but it rejects test13a.k
//The only difference is in the macro rule, we have ListItem(a(2)) in test13 and ListItem(A:K) in test13a
//These should be rejected both because macro rules are only dealing with KItems
module TEST13-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST13
    imports TEST13-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int)
    syntax KItem ::= b(Int)
   
    //rule k => a(2)
    rule k => ListItem(a(2))
    rule ListItem(a(2)) => b(2) [macro]

endmodule
