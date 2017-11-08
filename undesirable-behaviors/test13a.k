//13A
module TEST13A-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST13A
    imports TEST13A-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int)
    syntax KItem ::= b(Int)
   
    rule k => ListItem(a(2))
    rule ListItem(A:K) => b(2) [macro]

endmodule
