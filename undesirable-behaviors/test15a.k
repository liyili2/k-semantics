//test15a
module TEST15A-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST15A
    imports TEST15A-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= Int
    syntax KItem ::= a(KItem)
    syntax KItem ::= b(KItem)
   
    rule k => a(2) ~> b(1) ~> b(2) ~> b(3)
    rule b(2)  => b(2) [macro]

endmodule
