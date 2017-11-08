//From this example, we can see several things. First, macro rules are not only executed once 
//in this example as what K team claims in the documentation, but 
//in other examples, macro rules only execute once. It has an inconsistency here. 
//Second, K 3.6 actually allows macro rules to rewrite the pattern of a function rule, so that
//a function rule will become non function rule anymore. K 4.0 does not allow, but
//it treats macro rules as function rules, so macro rules have chance to apply in the real evaluation.
//the correct behavior should be rejecting this definition since there is a macro rule
// in the definition to rewrite a function label.
//By comparing this definition with TEST24A and TEST24B, one will see more clear.
module TEST24C-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST24C
    imports TEST24C-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function]
    syntax KItem ::= b(Int) | c(Int) | "good" | d(K)
   
    rule k => c(2)
    rule c(A:Int) => d(a(A))
    rule a(1) => 1
    rule a(2) => 2
    rule a(3) => 3
    rule a(A:Int) => good [owise]

    rule d(a(2)) => d(b(2))   [macro]

endmodule
