//In K 3.6, Bag definition should not be extendable with new normal construct
//should be rejected by kompile.
module TEST6-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST6
    imports TEST6-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax Bag ::= "a"

    rule <k> k => .K ...</k>
endmodule
