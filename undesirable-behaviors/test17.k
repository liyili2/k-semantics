//this example shows that the user defined list in K is still no associative and
//may not be identity. This definition will not even parse in K 4.0
//When I change the label inside the rule in line 21 to kLabel format as in test17a.k
//it can parse and compile but it cannot reduce the a(1,2,3,4,5) to .K.
//If K 4.0 really has associative and identity pattern matching for user defined list,
//this will work.
module TEST17-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST17
    imports TEST17-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= Int
    syntax KItem ::= a(K)
    syntax KItem ::= b(K)
   
    syntax Ints ::= List{Int,","}
    rule k => a(1,2,3,4,5)
    rule a(I:Ints,5) => .K

endmodule
