//current K implementation is unable to deal with this case. but it should be fine since 
//the macro rules work on a KItem to another KItem, even if the argument of the KItem is a built-in list.
//correct behavior is that K should run the program and output
//a(istItem(2) ListItem(3))
//              ~> a(ListItem(2) ListItem(3)) in the k cell.
module TEST16-SYNTAX

    syntax Pgm ::= "k" | Int

endmodule

module TEST16
    imports TEST16-SYNTAX

    configuration <T> <k> $PGM:Pgm </k><stack> .List </stack></T>

    syntax KItem ::= Int
    syntax KItem ::= a(List)
    syntax KItem ::= b(List)
   
    rule k => a(ListItem(1) ListItem(2) ListItem(3) ListItem(1))
              ~> a(ListItem(1) ListItem(2) ListItem(3) ListItem(1))
    rule a(ListItem(2) ListItem(3) ListItem(1) A:List) => b(A)
    rule a(A:List ListItem(1)) => a(ListItem(2) ListItem(3) A) [macro]

endmodule
