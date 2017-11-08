//This deifnition triggers infinite rewrites in kompile but test15a does not.
//They both have b(2) in the expression side that is the the same as the pattern side.
//If one triggers infinite rewrites, the other should do so also.
module TEST15-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST15
    imports TEST15-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= Int
    syntax KItem ::= a(KItem)
    syntax KItem ::= b(KItem)
   
    rule k => a(2) ~> b(1) ~> b(2) ~> b(3)
    rule b(2)  => a(b(2)) [macro]

endmodule
