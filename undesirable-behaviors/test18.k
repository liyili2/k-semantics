//K 3.6 does not support this non-linear pattern. K 4.0 is supposed to support it,
//but when the definition is compiled, running a program gets an
//undesirable result with c(1,1,1) still in the set.
//The result should remove the c(1,1,1) from the set completely.
module TEST18-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST18
    imports TEST18-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><store> .Set </store></T>

    syntax KItem ::= Int
    syntax KItem ::= "a"
    syntax KItem ::= "b" | c(Int,Int,Int)

    rule k => c(1,1,1) ~> c(1,1,2) ~> c(1,1,1) ~> c(2,1,3) ~> c(1,2,1)
              ~> c(2,1,3)

    rule <k> A:KItem => .K ...</k> <store> S:Set => S SetItem(A) </store>
         when A =/=K k andBool (A =/=K b) andBool (A =/=K a)
    rule <k> .K => b </k> <store> S:Set SetItem(c(A:Int, A:Int, A:Int)) => S </store>

endmodule
