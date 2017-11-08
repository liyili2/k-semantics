//current K implementations do not reject this function. It is actually a very
//easy type checking on the rules of a function to check if all patterns and expressions of
//a set of function rules are the right type. In this case, a(Int) should have List type.
//should be rejected by kompile
module TEST11-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST11
    imports TEST11-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax List ::= a(Int) [function]
    syntax KItem ::= b(Int)
   
    rule k => b(2)
    rule b(A:Int) => a(2)
    rule a(1) => 1
    rule a(2) => ListItem(2)
    rule a(3) => 3

endmodule
