//K definition should not be extendable with new normal construct
//should be rejected by kompile.
module TEST5-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST5
    imports TEST5-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax K ::= "a"

    rule <k> k => a ...</k>

endmodule
