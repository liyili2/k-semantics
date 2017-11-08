//This has different behavior in K 4.0 and K 3.6
//In K 4.0, it runs fine, which means that K can have partial functions.
//In K 3.6, the result will stuck at b(4) in the k cell because it will try to evaluate
//all sub terms of the condition (this time a(4) and 2),
//clean up all appreance of function labels, and then start evalauting the above level.
//if a function fails, it returns None instead of False for the condition.
//In our world, this will fail too.
module TEST10-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST10
    imports TEST10-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= a(Int) [function] | b(Int)
   
    rule k => b(4)
    rule b(A:Int) => .K when a(A) =/=K 2
    rule a(1) => 1
    rule a(2) => 2
    rule a(3) => 3
endmodule
