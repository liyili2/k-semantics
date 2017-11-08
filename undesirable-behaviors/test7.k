//This can actually be handled by kompile. The compilation step should detect that a function rule cannot be 
//written in a cell structure, but current K implementation stop the program
// when they found a function item without giving any hints why this is not OK.
//should be rejected by kompile.
module TEST7-SYNTAX

    syntax Pgm ::= "k"

endmodule

module TEST7
    imports TEST7-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function]

    rule <k> k => a(5) ...</k>
    rule <k> a(I:Int) => .K ...</k>

endmodule
