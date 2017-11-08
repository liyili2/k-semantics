//K 3.6 accepts this definition while K 4.0 clashes. The macro defines
//a rule to rewrite anything to b(2) in the whole deifnition rules and program state.
//If it passes, the result should be b(2) => b(2) infinitely. but the result of 
//K 3.6 gives true.
//should be rejected by kompile the best. If not, then rewrite b(2) to b(2)
module TEST12-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST12
    imports TEST12-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int)
    syntax KItem ::= b(Int)
   
    rule k => a(2)
    rule A:K => b(2) [macro]

endmodule
