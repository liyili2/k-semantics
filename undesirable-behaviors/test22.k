//This definition cannot be compiled by K 4.0
//The correct result is that, it should compile and remove all store cells
// that contain 3 at the end of a tuple.
module TEST22-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST22
    imports TEST22-SYNTAX

    configuration <T> <k> $PGM:Pgm </k> <store multiplicity="*"> .K </store> </T>

    syntax KItem ::= tuple(K, K, K) | "a" | "b"

    rule <k> k => b </k> 
         (.Bag => <store> tuple(3,3,3) </store> <store> tuple(1,2,3) </store>
             <store> tuple(5,6,7) </store> <store> tuple(3,2,2) </store>
             <store> tuple(2,2,1) </store>)
    rule <store> tuple(A:K, B:K, 3) </store> => .Bag

endmodule
