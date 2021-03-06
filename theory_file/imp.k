// Copyright (c) 2014-2016 K Team. All Rights Reserved.

module IMP-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict, function]
                 > "spawn" Block              [strict]
                 > Id "=" AExp                [klabel('assign)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [strict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict]
                 | "while" "(" BExp ")" Block [strict]
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}              [strict(1)]

  syntax AExp      ::= Token{[\@][a-zA-Z0-9\_]*}          [function, token]
endmodule


module IMP
  imports IMP-SYNTAX

  syntax BlockOrStmtType ::= "block" | "stmt"
  syntax PrintableType  ::= "int" | "string"
  syntax Type ::= PrintableType | "bool" | BlockOrStmtType

  syntax KResult ::= Type

  configuration <T color="yellow">
                  <k color="green"> $PGM:Stmts </k>
                  <tenv color="LightSkyBlue"> .Map </tenv>
                </T>

  rule @1 => 1
  rule @2 => 2

// AExp
  rule _:Int => int
  rule _:String => string
  rule <k>   X:Id => T ...</k> <tenv>... X |-> T ...</tenv>
  rule <k> ++X:Id => int ...</k> <tenv>... X |-> int ...</tenv>
  rule read() => int

  syntax AExp ::= Type
  rule int / int => int
  rule int + int => int
  rule string + string => string

  rule spawn block => int
  //rule <k> X = T => T ...</k> <tenv>... X |-> T ...</tenv>

// BExp
  syntax BExp ::= Type
  rule _:Bool => bool
  rule int <= int => bool
  rule ! bool => bool
  rule bool && bool => bool

// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <tenv> Rho </tenv>
  rule <k> _:BlockOrStmtType ~> Rho => block ...</k>
       <tenv> _ => Rho </tenv>

// Stmt
  rule int; => stmt

  syntax Block ::= Type
  rule if (bool) block else block => stmt
  rule while (bool) block => stmt

  rule <k> int (X:Id,Xs:Ids => Xs); ...</k> <tenv> M:Map => M [ X <- int ] </tenv>
  rule int .Ids; => stmt

  context print(HOLE:AExp, _);
  rule print(_:PrintableType,AEs => AEs);
  rule print(.AExps); => stmt

  rule halt; => stmt

  rule join int; => stmt

// Stmts
  rule .Stmts => stmt
  rule _:BlockOrStmtType Ss => Ss
endmodule
