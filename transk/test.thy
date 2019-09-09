theory test
imports Main
begin

datatype reg = Eps | Sym char | Alt reg reg | Seq reg reg | Rep reg

function search where
"search a [] = False"
| "search a (b#l) = (if a = b then True else search a l)"
by pat_completeness auto

termination by lexicographic_order

function regMatch :: "reg \<Rightarrow> string \<Rightarrow> bool"
   and regSplit :: "reg \<Rightarrow> reg \<Rightarrow> string \<Rightarrow>
                  string \<Rightarrow> bool"
   and regPart :: "reg \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
"regMatch a s = (case a of Eps \<Rightarrow> s = [] 
     | Sym x \<Rightarrow> s = [x]
      | Alt x y \<Rightarrow> regMatch x s \<or> regMatch y s
   | Seq x y \<Rightarrow> regSplit x y [] s
   | Rep x \<Rightarrow> (case s of [] \<Rightarrow> True | b#bl \<Rightarrow> regPart x [b] bl))"
| "regPart x a [] = regMatch x a"
| "regPart x a (s#l) = (if regMatch x a then regMatch (Rep x) (s#l) else regPart x (a@[s]) l)"
| "regSplit x y s [] = False"
| "regSplit x y s (a#al) = (if regMatch x s then regMatch y (a#al) else regSplit x y (s@[a]) al)"
by pat_completeness auto

termination sorry


inductive abc where
rule1 : "regMatch a b \<Longrightarrow> abc (a,b) True"
|  rule2 : "\<not> regMatch a b \<Longrightarrow> abc (a,b) False"

code_pred abc .

export_code abc
  in OCaml
  module_name oneStepEval file "oneStepEval.ml"

end