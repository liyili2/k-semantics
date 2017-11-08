//Both K 3.6 and K 4.0 runs this program but two function rules for a same
//function label are attributed as owise rules. It should have as many as
//one owise attribute rule for each function label.
//should be rejected by kompile
module TEST9-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST9
    imports TEST9-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function]

    rule k => a(10)
    rule a(1) => 1
    rule a(2) => 2
    rule a(3) => 3 [owise]
    rule a(A:Int) => A +Int 1 [owise]
endmodule
