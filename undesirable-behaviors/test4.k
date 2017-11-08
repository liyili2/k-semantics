//List definition should not be extendable with new normal construct
//should be rejected by kompile.
module TEST4-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST4
    imports TEST4-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax List ::= "a"

    rule <k> k => ListItem(1) ...</k>
         <stack>... .List => a </stack>

endmodule
