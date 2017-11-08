//From this example, we can see several things. First, K identifies the macro rule
//as both a macro rule and a function rule for function label a, and it rewrites
//the a(2) => 2 ===> b(2) => 2, and keep a(2) => b(2) as the functoin rule.
//From test24c.k, we can see clearly this is the case.
//Second, K 3.6 actually allows macro rules to rewrite the pattern of a function rule, so that
//a function rule will become non function rule anymore, but do not identify the 
//macro rule as the function rule for label a. 
//the correct behavior should be rejecting this definition since there is a macro rule
// in the definition to rewrite a function label.
//By comparing this definition with TEST24A, TEST24B and TEST24C, one will see more clear.
module TEST24-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST24
    imports TEST24-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function]
    syntax KItem ::= b(Int) | c(Int) | "good"
   
    rule k => c(2)
    rule c(A:Int) => a(A)
    rule a(1) => 1
    rule a(2) => 2
    rule a(3) => 3
    rule a(A:Int) => good [owise]

    rule a(2) => b(2)   [macro]

endmodule
