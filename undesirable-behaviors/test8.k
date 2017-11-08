//Both K 3.6 and K 4.0 has a problem with the specification. In K 4.0, the definition causes
// K to clash even if we add the multiplicity="*"
//in the k cell that is exactly the same as the tutoring of kool-untyped.k.
//In K 3.6, it can compiled and run even without multiplicity="*" but defining the key word multiplicity="*" or multiplicity="?"
//should be the only way to remove a cell from a program state.
//when k cell is featured with multiplicity="*", the kompile should compile the definition and run it just fine.
//when k cell is not featured with multiplicity="*", kompile should reject the definition.
module TEST8-SYNTAX

    syntax Pgm ::= "k"

endmodule

module TEST8
    imports TEST8-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int)

    rule <k> k => a(5) ...</k><stack> .List => ListItem(k) </stack>
    rule <k> a(I:Int) => . ...</k><stack>... .List => ListItem(k) </stack>
    rule (<k> .K </k>) => .Bag
endmodule
