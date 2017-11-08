//By comparing TEST25 and TEST25A, we can see that the bracket construct has problem in K.
//When we define Pgm = { Ints }. Othar than the construct, we should introduce a
//subsort relation between Pgm and Ints. Even if we get rid of the bracket, 
//the subsort relation remains. So when k transition to {1,2,3}, it will transition to b({1,2,3}) further.
//The correct behavior should be either rejecting the definition and asking users to 
//define Pgm = Ints | { Pgm } or help users to generate this. Our K semantics did the former one. 
module TEST25-SYNTAX

    syntax Pgm ::= "k" | "a" | "{" Ints "}" [bracket]
    syntax Ints ::= List{Int,","}

endmodule

module TEST25
    imports TEST25-SYNTAX

    syntax KItem ::= b(Pgm)
    rule k => {1,2,3}
    rule A:Pgm => b(A)

endmodule
