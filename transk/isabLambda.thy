theory isabLambda
imports Main
begin

(* basic isabelle syntax *)
datatype ('tyVar, 'tyConst) isaType =
   TyVar 'tyVar
 | TyConst "'tyConst" "('tyVar, 'tyConst) isaType list"

datatype ('tyVar, 'iVar, 'cVar) isaTerm =
   VarTm 'tyVar 'iVar | Const 'tyVar 'cVar
 | App "('tyVar, 'iVar, 'cVar) isaTerm" "('tyVar, 'iVar, 'cVar) isaTerm"
 | Lambda 'iVar 'tyVar "('tyVar, 'iVar, 'cVar) isaTerm"

fun lookup :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option" where
"lookup a [] = None"
| "lookup a ((x,y)#l) = (if a = x then Some y else lookup a l)"

fun update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
"update a b [] = [(a,b)]"
| "update a b ((x,y)#l) = (if a = x then ((x,b)#l) else update a b l)"

primrec insertToList :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insertToList a [] = [a]"
| "insertToList a (b#l) = (if a = b then b#l else b#(insertToList a l))"

primrec insertAllToList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insertAllToList [] S = S"
| "insertAllToList (a#l) S = insertAllToList l (insertToList a S)"

primrec toMonoType :: "('tyVar, 'tyConst) isaType
             \<Rightarrow> ('tyVar list * ('tyVar, 'tyConst) isaType)"
  and toMonoTypeInList :: "('tyVar, 'tyConst) isaType list
             \<Rightarrow> ('tyVar list * ('tyVar, 'tyConst) isaType list)" where
"toMonoType (TyVar a) = ([a], TyVar a)"
| "toMonoType (TyConst t l) = (case toMonoTypeInList l of (vl, terms) \<Rightarrow> 
      (vl, TyConst t terms))"
| "toMonoTypeInList [] = ([], [])"
| "toMonoTypeInList (a#l) = (case toMonoType a of (S, t) \<Rightarrow> (case toMonoTypeInList l of
      (aS, T) \<Rightarrow> (insertAllToList S aS, t#T)))"

primrec deleteVarFromList :: "'iVar \<Rightarrow> 'iVar list \<Rightarrow> 'iVar list" where
"deleteVarFromList a [] = []"
| "deleteVarFromList a (x#l) = (if x = a then deleteVarFromList a l else x#(deleteVarFromList a l))"

primrec getFreeVarsInTerm :: "('tyVar, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar list" where
"getFreeVarsInTerm (VarTm t x) = [x]"
| "getFreeVarsInTerm (Const t x) = []"
| "getFreeVarsInTerm (App u v) = insertAllToList (getFreeVarsInTerm u) (getFreeVarsInTerm v)"
| "getFreeVarsInTerm (Lambda x t e) = deleteVarFromList x (getFreeVarsInTerm e)"

primrec substInType :: "('tyVar, 'tyConst) isaType \<Rightarrow> 'tyVar \<Rightarrow> ('tyVar, 'tyConst) isaType
            \<Rightarrow> ('tyVar, 'tyConst) isaType"
  and substInTypeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> 'tyVar \<Rightarrow> ('tyVar, 'tyConst) isaType
            \<Rightarrow> ('tyVar, 'tyConst) isaType list" where
"substInType (TyVar a) x b = (if x = a then b else (TyVar a))"
| "substInType (TyConst x l) a b = TyConst x (substInTypeInList l a b)"
| "substInTypeInList [] a b = []"
| "substInTypeInList (x#l) a b = (substInType x a b)#(substInTypeInList l a b)"

fun substTypeByMap :: "('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar, 'tyConst) isaType" where
"substTypeByMap a [] = a"
| "substTypeByMap a ((x,y)#l) = substTypeByMap (substInType a x y) l"

fun substInMap :: "('tyVar * ('tyVar, 'tyConst) isaType) list \<Rightarrow> 'tyVar
  \<Rightarrow> ('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list" where
"substInMap [] x a = [(x,a)]"
| "substInMap ((x,y)#l) a b = ((x,substInType y a b)#(substInMap l a b))"

primrec occurInTerm :: "('tyVar, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar \<Rightarrow> bool" where
"occurInTerm (VarTm t x) a = (x = a)"
| "occurInTerm (Const t x) a = False"
| "occurInTerm (App u v) a = (occurInTerm u a \<or> occurInTerm v a)"
| "occurInTerm (Lambda x t e) a = (if a = x then False else occurInTerm e a)"

primrec occurInType :: "('tyVar, 'tyConst) isaType \<Rightarrow> 'tyVar \<Rightarrow> bool"
   and occurInTypeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> 'tyVar \<Rightarrow> bool" where
"occurInType (TyVar a) x = (if a = x then True else False)"
| "occurInType (TyConst a l) x = occurInTypeInList l x"
| "occurInTypeInList [] x = False"
| "occurInTypeInList (a#l) x = ((occurInType a x) \<or> (occurInTypeInList l x))"

fun orientInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
          \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list" where
"orientInList [] = []"
| "orientInList ((x,y)#l) = (case y of (TyVar a) \<Rightarrow> (case x of (TyConst b l')
            \<Rightarrow> (y,x)#(orientInList l)
        | TyVar b \<Rightarrow> (x,y)#(orientInList l)) | (TyConst a l') \<Rightarrow> (x,y)#(orientInList l))"

fun deleteInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
          \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list" where
"deleteInList [] = []"
| "deleteInList ((x,y)#l) = (if x = y then deleteInList l else (x,y)#(deleteInList l))"

fun decomposeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> ('tyVar, 'tyConst) isaType list
           \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list option" where
"decomposeInList [] [] = Some []"
| "decomposeInList (a#l) (x#l') = (case decomposeInList l l' of None \<Rightarrow> None
           | Some la \<Rightarrow> Some ((a,x)#la))"
| "decomposeInList a b = None"

function unifyInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
        \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"unifyInList [] = Some []"
| "unifyInList ((x,y)#l) = (case x of TyVar a \<Rightarrow> if occurInType y a then None
          else (case unifyInList l of None \<Rightarrow> None | Some m \<Rightarrow> Some (substInMap m a y))
   | TyConst a n \<Rightarrow> (case y of TyVar b \<Rightarrow> None
      | TyConst b n' \<Rightarrow> if a = b then (case decomposeInList n n' of None \<Rightarrow> None
         | Some na \<Rightarrow> unifyInList (l@(orientInList (deleteInList na)))) else None))"
by pat_completeness auto

fun joinMapAux :: "('tyVar * ('tyVar, 'tyConst) isaType) list \<Rightarrow> 'tyVar
     \<Rightarrow> ('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"joinMapAux [] a b = Some [(a,b)]"
| "joinMapAux ((x,y)#l) a b = (if x = a then (case unifyInList (orientInList [(y,b)])
        of None \<Rightarrow> None | Some m \<Rightarrow> Some ((x,substTypeByMap y m)#l))
      else (case joinMapAux l a b of None \<Rightarrow> None
          | Some la \<Rightarrow> Some ((x,y)#la)))"
 
fun joinMap :: "('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"joinMap [] S = Some S"
| "joinMap ((x,y)#l) S = (case joinMapAux S x y of None \<Rightarrow> None
       | Some m \<Rightarrow> joinMap l m)"

fun getTypeMap :: "('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar, 'tyConst) isaType
    \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option"
  and  getTypeMapInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> ('tyVar, 'tyConst) isaType list
    \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"getTypeMap (TyVar x) b = Some [(x,b)]"
| "getTypeMap (TyConst t l) b = (case b of TyVar y \<Rightarrow> None
       | (TyConst t' l') \<Rightarrow> if t = t' then getTypeMapInList l l' else None)"
| "getTypeMapInList [] [] = Some []"
| "getTypeMapInList (a#l) (b#l') = (case getTypeMap a b of None \<Rightarrow> None
        | Some m1 \<Rightarrow> (case getTypeMapInList l l' of None \<Rightarrow> None
        | Some m2 \<Rightarrow> joinMap m1 m2))"
| "getTypeMapInList a g = None"

locale ITheory =
 fixes TypeConsts :: "'tyConst set" 
 and Types :: "('tyVar, 'tyConst) isaType set"
 and TmConsts :: "'cVar set"
 and typeIds :: "'tyVar set"
 and tmIds :: "'iVar set"
 and Terms :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm set"
 and FunType :: "'tyConst"
 and freshLambdaVar :: "'iVar list \<Rightarrow> 'iVar"
 assumes funTypeRule : "\<forall> a b . a \<in> Types \<and> a = TyConst FunType b \<longrightarrow> (length b = 2)"
 and freshLambdaVarRule : "\<forall> S . freshLambdaVar S \<in> set S"
context ITheory begin

primrec typeCheckInTerm :: "('iVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
      \<Rightarrow> ('cVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
    \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
            \<Rightarrow> (('iVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
      * ('tyVar list * ('tyVar, 'tyConst) isaType)) option" where
"typeCheckInTerm S M (VarTm t x) = (case lookup x S of None \<Rightarrow>
        Some (update x (toMonoType t) S, toMonoType t)
          | Some (binds, t') \<Rightarrow> (case unifyInList (orientInList [(t,t')]) of None \<Rightarrow> None
         | Some tm \<Rightarrow> (case toMonoType (substTypeByMap t tm) of ta 
      \<Rightarrow> Some (update x ta S, ta))))"
| "typeCheckInTerm S M (Const t c) = (case lookup c M of None \<Rightarrow> None
        | Some (binds, t') \<Rightarrow> (case unifyInList (orientInList [(t,t')]) of None \<Rightarrow> None
      | Some tm \<Rightarrow> (case toMonoType (substTypeByMap t tm) of ta \<Rightarrow> 
     Some (S, ta))))"
| "typeCheckInTerm S M (App a b) = (case typeCheckInTerm S M a of
    Some (S', binds, TyConst tc [lt,rt])
      \<Rightarrow> if tc = FunType then (case typeCheckInTerm S' M b of None \<Rightarrow> None
        | Some (Sa, binds, lt') \<Rightarrow>
      (case unifyInList (orientInList [(lt,lt')]) of None \<Rightarrow> None
             | Some tm \<Rightarrow> Some (Sa, toMonoType (substTypeByMap rt tm)))) else None
      | _ \<Rightarrow> None)"
| "typeCheckInTerm S M (Lambda x t e) =
       (case typeCheckInTerm (update x (toMonoType t) S) M e of None \<Rightarrow> None
      | Some (S',binds, t') \<Rightarrow> Some (S, toMonoType (TyConst FunType [t, t'])))"

primrec substInTermByVar :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar \<Rightarrow> 'iVar
      \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm" where
"substInTermByVar (VarTm t x) a b = (if a = x then VarTm t b else VarTm t x)"
| "substInTermByVar (Const t x) a b = (Const t x)"
| "substInTermByVar (App u v) a b = App (substInTermByVar u a b) (substInTermByVar v a b)"
| "substInTermByVar (Lambda x t e) a b = (if x = a then Lambda x t e
     else Lambda x t (substInTermByVar e a b))"

function substInTerm :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar
     \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
      \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm" where
"substInTerm (VarTm t x) y b = (if x = y then b else (VarTm t x))"
| "substInTerm (Const t x) y b = Const t x"
| "substInTerm (App u v) y b = App (substInTerm u y b) (substInTerm v y b)"
| "substInTerm (Lambda x t e) y b = (if y = x then
  Lambda x t e else if occurInTerm b x then
    (case freshLambdaVar (y#((getFreeVarsInTerm e)@(getFreeVarsInTerm b))) of newVar
      \<Rightarrow> Lambda newVar t (substInTerm (substInTermByVar e x newVar) y b))
            else Lambda x t (substInTerm e y b))"
by pat_completeness auto

inductive LambdaInduct :: "('cVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
   \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
    \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> bool" where
unitRule : "typeCheckInTerm [] M (App (Lambda x t e) e') = Some v
                     \<Longrightarrow> LambdaInduct M (App (Lambda x t e) e') (substInTerm e x e')"

end

end