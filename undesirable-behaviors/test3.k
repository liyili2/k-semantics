//K cell should be a list of K, but ListItem and SetItem have sorts List and Set. Should be rejected to move.
//should have result <T> <k> k </k></T>
module TEST3-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST3
    imports TEST3-SYNTAX

    configuration <T> <k> $PGM:Pgm </k></T>

    rule k => ListItem(1)
    rule ListItem(A:K) => SetItem(A:K)


endmodule
