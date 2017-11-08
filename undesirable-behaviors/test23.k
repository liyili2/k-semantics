//The cell structure in K 4.0 is hard to manipulate. 
//We tests most cell structures in K 3.6
//Once we have a cell structure that contains three nested cells having
//multiplicity="*", the file can be compiled, but krun will not execute
//programs. The exact rule makes the cell structures fail is unclear.
//Correct behavior: Either rejecting the structure in the kompile or
//allowing it to execute. Our interpreter allows it to execute.
module TEST23-SYNTAX

    syntax Pgm ::= "k" 

endmodule

module TEST23
    imports TEST23-SYNTAX

    configuration <T multiplicity="*"> <k> $PGM:Pgm </k>
          <store multiplicity="*"> <next> 0 </next> 
       <types multiplicity="*"> .K </types></store> </T>

    syntax KItem ::= tuple(K, K, K) | "a" | "b" | "c" | "d"

    rule <k> k => a </k> (.Bag => <store>... .Bag ...</store>)
    rule <k> a => b </k>  (.Bag => <types> 0 </types>)

endmodule
