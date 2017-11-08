//test25a.k
module TEST25A-SYNTAX

    syntax Pgm ::= "k" | "a" | "{" Ints "}" [bracket]
    syntax Ints ::= List{Int,","}

endmodule

module TEST25A
    imports TEST25A-SYNTAX

    syntax KItem ::= b(Pgm)
    rule k => {1,2,3}
    rule A:Pgm => b(A)

endmodule
