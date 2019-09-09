theory kToIsab
imports Main Real List k isabInIsab
begin

fun getAllCellNames :: "('a, 'b, 'c, 'd) suB list
         \<Rightarrow> 'b list"
  and  getAllCellNamesAux :: "('a, 'b, 'c, 'd) suBigKWithBag
         \<Rightarrow> 'b list" where
"getAllCellNames [] = []"
| "getAllCellNames (b#l) = (case b of IdB x \<Rightarrow> getAllCellNames l
      | ItemB x y z \<Rightarrow> (case (getAllCellNamesAux z) of l' \<Rightarrow>
   if x \<in> set l' then l' else x#l'))"
| "getAllCellNamesAux (SUBag x) = getAllCellNames x"
| "getAllCellNamesAux x = []"

datatype 'a tree = Trunk 'a "'a tree list"

locale KToIsabelleSyntaxTranslation = KTheory
   where SortNames = "SortNames :: 'upVar set" (* sort names *)
  and ProgVars = "ProgVars :: 'var set" (* prog vars *)
  and TermNames = "TermNames :: 'svar set" (* klabel names *)
  and AcapNames = "AcapNames :: 'acapvar set" (* module names *)
  and k = "k :: 'var"
  and AInt = "AInt :: 'upVar"
  and Bool = "Bool :: 'upVar"
  and String = "String :: 'upVar"
  and Float = "Float :: 'upVar"
  and Id = "Id :: 'upVar"
  and K = "K :: 'upVar"
  and KItem = "KItem :: 'upVar"
  and KLabel = "KLabel :: 'upVar"
  and KResult = "KResult :: 'upVar"
  and KList = "KList :: 'upVar"
  and List = "List :: 'upVar"
  and Set = "Set :: 'upVar"
  and Map = "Map :: 'upVar"
  and Bag = "Bag :: 'upVar"
  and BuiltinSorts = "BuiltinSorts :: 'upVar list"
  and AllSubsorts = "AllSubsorts :: ('upVar * 'upVar) list"
  and IRTerms = "IRTerms :: ('upVar, 'var, 'svar, 'metaVar metaVar) kItem set"
  and Programs = "Programs :: 'var program set"
  and Theory = "Theory :: ('upVar, 'var, 'svar, 'acapvar, 'metaVar metaVar) kFile"
  and UnitLabel = "UnitLabel :: 'upVar \<Rightarrow> 'svar"
  and isValidRedex = "isValidRedex :: 'var theConstant \<Rightarrow> string \<Rightarrow> bool"
  and syntaxOrder = "syntaxOrder :: ('upVar, 'var, 'svar) kSyntax list
                             \<Rightarrow> ('upVar, 'var, 'svar) kSyntax list"
  and symbolsToKLabel = "symbolsToKLabel :: 'upVar symbol nelist \<Rightarrow> 'svar"
  and progToKItem = "progToKItem :: 'var program
                          \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) kItem"
  and constToLabel = "constToLabel :: 'var theConstant \<Rightarrow> 'svar"
  and labelToConst = "labelToConst :: 'svar \<Rightarrow> 'var theConstant option"
  and isConst = "isConst :: 'svar \<Rightarrow> bool"
  and freshVar = "freshVar :: 'metaVar metaVar list \<Rightarrow> 'metaVar"
  and sort = "sort :: 'svar"
  and getKLabel = "getKLabel :: 'svar"
  and isKResult = "isKResult :: 'svar"
  and andBool = "andBool :: 'svar"
  and notBool = "notBool :: 'svar"
  and ProgramConfigurations =
           "ProgramConfigurations :: ('upVar, 'var, 'svar, 'metaVar metaVar) suB list set"
  and UserInputPrograms = "UserInputPrograms :: ('metaVar *
                      ('upVar, 'var, 'svar, 'metaVar metaVar) subsFactor) list set"
 +  KInIsabelleSyntax where 
      Types = "Types :: 'tVar kType isabType set" 
  and Constructs = "Constructs :: ('cVar, 'tVar kType isabType, 'var) kConstr set" (* constructor names *)
  and IsabVars = "IsabVars :: 'iVar set" (* isabelle variables *)
  and IVarOne = "IVarOne :: 'iVar"
  and IVarTwo = "IVarTwo :: 'iVar"
  and IVarThree = "IVarThree :: 'iVar"
  and freshCVar = "freshCVar :: ('cVar, 'tVar kType isabType, 'var) kConstr list
                         \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr"
  and freshIVar = "freshIVar :: 'iVar list \<Rightarrow> 'iVar"
  and renameCVar = "renameCVar :: ('cVar, 'tVar kType isabType, 'var) kConstr
             \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr list \<Rightarrow>
             ('cVar, 'tVar kType isabType, 'var) kConstr"
  and Builtins = "Builtins :: ('cVar, 'tVar kType isabType, 'var) kConstr list" (* built-in function set *)
  and CellNames = "ProgVars :: 'var set" (* set of cell names *)
  and UserConstrs = "UserConstrs :: 'cVar set"
  and KTokenNames = "KTokenNames :: 'kTVar set"
  and translateType = "translateType :: 'upVar \<Rightarrow> 'tVar kType"
  and translateLabel = "translateLabel :: 'svar \<Rightarrow> 'cVar"
  and translateVar = "translateVar :: 'metaVar metaVar \<Rightarrow> 'iVar"
  and translateSyntaxSet = "translateSyntaxSet :: 'svar set \<Rightarrow> ('cVar * 'tVar list) list option"
  for SortNames ProgVars TermNames AcapNames k AInt Bool String Float Id K KItem KLabel
    KResult KList List Set Map Bag BuiltinSorts AllSubsorts IRTerms Programs
    Theory UnitLabel isValidRedex syntaxOrder symbolsToKLabel progToKItem constToLabel
    labelToConst isConst freshVar sort getKLabel isKResult andBool notBool ProgramConfigurations
   UserInputPrograms Types Constructs IsabVars IVarOne IVarTwo IVarThree freshCVar freshIVar renameCVar
    Builtins UserConstrs KTokenNames translateType translateLabel translateVar
    translateSyntaxSet +
 assumes translateLabelRule : "\<forall> a \<in> TermNames . translateLabel a \<in> UserConstrs"
 and translateTypeRule : "\<forall> a \<in> SortNames . OtherType (translateType a) \<in> Types"
 and builtinSVarRule : "k \<in> ProgVars"
 and builtinSortRule : "{AInt, Bool, String, Float, Id, K, KItem, KLabel,
           KResult, KList, List, Set, Map, Bag} \<subseteq> SortNames"
 and builtinLabelRule : "{sort, getKLabel, isKResult, andBool, notBool} \<subseteq> TermNames"
context KToIsabelleSyntaxTranslation begin

definition translatePatternType :: "'upVar \<Rightarrow> 'tVar kType isabType" where
"translatePatternType x = (if x = Bool then BoolIsab
  else if x = K then OtherType SingleKIsab else if x = KItem then OtherType KItemIsab
   else if x = KLabel then OtherType KLabelIsab else if x = KResult then OtherType KResultIsab
   else if x = KList then OtherType SingleKListIsab else if x = List then OtherType SingleListIsab
  else if x = Set then OtherType SingleSetIsab else if x = Map then OtherType SingleMapIsab
  else if x = Bag then OtherType SingleBagIsab else OtherType (translateType x))"

definition translateRightType :: "'upVar \<Rightarrow> 'tVar kType isabType" where
"translateRightType x = (if x = Bool then BoolIsab
  else if x = K then (IsabList (OtherType SingleKIsab)) else if x = KItem then OtherType KItemIsab
   else if x = KLabel then OtherType KLabelIsab else if x = KResult then OtherType KResultIsab
   else if x = KList then (IsabList (OtherType SingleKListIsab))
     else if x = List then (IsabList (OtherType SingleListIsab))
  else if x = Set then (IsabList (OtherType SingleSetIsab))
        else if x = Map then (IsabList (OtherType SingleMapIsab))
  else if x = Bag then (IsabList (OtherType SingleBagIsab)) else OtherType (translateType x))"

primrec translateTypes :: "'upVar list \<Rightarrow> 'tVar kType isabType list" where
"translateTypes [] = []"
| "translateTypes (b#l) = (translateRightType b)#(translateTypes l)"

fun translateSyntax :: "('upVar * 'upVar list * 'svar KItemSyntax *
           ('var,'svar) synAttrib list * bool) list \<Rightarrow>
      ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list option" where
"translateSyntax [] = Some []"
| "translateSyntax ((ty, tyl, SingleTon label, stl, b)#l) =
  (case translateSyntax l of None \<Rightarrow> None
     | Some syntaxl \<Rightarrow>
 (case getStrictInAttributes stl of None \<Rightarrow> if Seqstrict \<in> set stl then
     Some (addSyntaxToList (translatePatternType ty)
    (UserConstr (translateLabel label), translateTypes tyl, Some KSeqStrict, b) syntaxl)
      else Some (addSyntaxToList (translatePatternType ty)
    (UserConstr (translateLabel label), translateTypes tyl, None, b) syntaxl)
   | Some nl \<Rightarrow> Some (addSyntaxToList (translatePatternType ty)
   (UserConstr (translateLabel label), translateTypes tyl,
                   Some (KStrict nl), b) syntaxl)))"
| "translateSyntax ((ty, tyl, SetTon labels, stl, b)#l) =
   (if tyl = [] then (case translateSyntax l of None \<Rightarrow> None
      | Some syntaxl \<Rightarrow> 
     (case translateSyntaxSet labels of None \<Rightarrow> None
      | Some labels' \<Rightarrow> 
     Some (addSyntaxSetToList (translatePatternType ty) labels' b syntaxl))) else None)"

definition AllCellNames :: "'var list option" where
"AllCellNames = (case configurationTest of None \<Rightarrow> None
   | Some confi \<Rightarrow> Some (getAllCellNames confi))"

fun getAllUserTypes :: "('upVar * 'upVar list * 'svar KItemSyntax *
           ('var,'svar) synAttrib list * bool) list \<Rightarrow> 'tVar kType isabType list" where
"getAllUserTypes [] = []"
| "getAllUserTypes ((ty, b)#l) = translateRightType ty # getAllUserTypes l"

fun genCellNameType :: "'var list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
  * 'tVar kType isabType list * isabelleStricts option * bool) list" where
"genCellNameType [] = []"
|"genCellNameType (b#l) = ((CellNameConstr b), [], None, False)#(genCellNameType l)"

fun genKItemConstrs :: "'tVar kType isabType list \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr *
          'tVar kType isabType list * isabelleStricts option * bool) list" where
"genKItemConstrs [] = []"
| "genKItemConstrs (x#l) = (if x \<in> extendableFunctionBuiltinTypes Un nonExtendableBuiltinTypes
      Un {OtherType KItemIsab} then genKItemConstrs l else
        ((KItemConstr x), [x], Some (KStrict [1]), False)#genKItemConstrs l)"

fun generateHoleConstrs :: "('tVar kType isabType *
    (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list) list \<Rightarrow>
          ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * isabelleStricts option * bool) list) list " where
"generateHoleConstrs [] = []"
| "generateHoleConstrs ((x,y)#l) =
 (if x \<in> extendableFunctionBuiltinTypes \<union> nonExtendableBuiltinTypes \<union> {OtherType KResultIsab}
    then (x,y)#generateHoleConstrs l
     else (x,((HoleConstr x),[],None,False)#y)#(generateHoleConstrs l))"

definition userSyntaxInIsabTest :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list option" where
"userSyntaxInIsabTest = (case syntaxSetToKItemTest of None \<Rightarrow> None
       | Some l \<Rightarrow> (case translateSyntax l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some (generateHoleConstrs l')))"

primrec genSubtypeSyntaxAux :: "'upVar \<Rightarrow> 'upVar list \<Rightarrow>
       ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * isabelleStricts option * bool)) list" where
"genSubtypeSyntaxAux a [] = []"
| "genSubtypeSyntaxAux a (b#l) = (translatePatternType a,
       (SubsortConstr (translateRightType a) (translateRightType b),
          [translatePatternType b], Some (KStrict [1]), False))#genSubtypeSyntaxAux a l"

fun genSubtypeLabels :: "('upVar * 'upVar list) list \<Rightarrow>
     ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
         * 'tVar kType isabType list * isabelleStricts option * bool)) list" where
"genSubtypeLabels [] = []"
| "genSubtypeLabels ((a,b)#l) = (genSubtypeSyntaxAux a b)@genSubtypeLabels l"

definition builtinConstrs :: "('tVar kType isabType *
    (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list) list" where
"builtinConstrs = (case userSyntaxInIsabTest of None \<Rightarrow> []
    | Some synl \<Rightarrow> (case AllCellNames of None \<Rightarrow> []
       | Some l \<Rightarrow> [(OtherType CellNameType, genCellNameType l),
      (OtherType KItemIsab, genKItemConstrs (keys synl)), (OtherType CellType,
          [(Cell, [OtherType CellNameType, OtherType CellConType], None, False)]),
   (OtherType SingleKIsab, [(KItemAsK, [OtherType KItemIsab], None, False)]),
   (OtherType SingleListIsab, [(KAsList, [(IsabList (OtherType SingleKIsab))], None, False)]),
   (OtherType SingleSetIsab, [(KAsSet, [(IsabList (OtherType SingleKIsab))], None, False)]),
  (OtherType SingleMapIsab, [(KAsMap, [(IsabList (OtherType SingleKIsab)),
     (IsabList (OtherType SingleKIsab))], None, False)]),(OtherType CellConType,
       [(KCellIsab, [IsabList (OtherType SingleKIsab)], None, False),
   (ListCellIsab, [IsabList (OtherType SingleListIsab)], None, False),
   (SetCellIsab, [IsabList (OtherType SingleSetIsab)], None, False),
   (MapCellIsab, [IsabList (OtherType SingleMapIsab)], None, False),
   (BagCellIsab, [IsabList (OtherType SingleBagIsab)], None, False)]),
  (OtherType SingleBagIsab, [(SingleCellAsBag, [OtherType CellType], None, False),
  (OptionCellAsBag, [IsabOption (OtherType CellType)], None, False),
   (StarCellAsBag, [OtherType CellNameType, IsabList (OtherType CellConType)], None, False)]),
   (OtherType SingleKListIsab, [(CellAsKList, [OtherType CellConType], None, False),
      (KLabelAsKList, [OtherType KLabelIsab], None, False)])]))"

fun getSetTonLabels :: "('upVar * 'upVar list * 'svar KItemSyntax *
           ('var,'svar) synAttrib list * bool) list \<Rightarrow> ('tVar kType isabType,
            ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm option" where
"getSetTonLabels [] = Some IsabEmptyList"
| "getSetTonLabels ((ty, tyl, SingleTon label, stl, b)#l) = getSetTonLabels l"
| "getSetTonLabels ((ty, tyl, SetTon labels, stl, b)#l) = 
    (if tyl = [] then (case getSetTonLabels l of None \<Rightarrow> None
      | Some syntaxl \<Rightarrow> 
     (case translateSyntaxSet labels of None \<Rightarrow> None
      | Some labels' \<Rightarrow>  Some (foldl (\<lambda> acc (x,y) .
            IsabListCon (getToken (UserConstr x)) acc) syntaxl labels'))) else None)"

definition setTonLabels :: "('tVar kType isabType,
            ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"setTonLabels = (case syntaxSetToKItemTest of None \<Rightarrow> IsabEmptyList
          | Some l \<Rightarrow> (case getSetTonLabels l of None \<Rightarrow> IsabEmptyList | Some l' \<Rightarrow> l'))"

(* get all klabels for all user types and holes *)
fun generateKLabelsAux :: "('upVar * 'upVar list * 'svar KItemSyntax *
           ('var,'svar) synAttrib list * bool) list \<Rightarrow>
          (('cVar, 'tVar kType isabType, 'var) kConstr *
                     'tVar kType isabType list * isabelleStricts option * bool) list" where
"generateKLabelsAux [] = []"
| "generateKLabelsAux ((ty,tyl,SingleTon label,d,e)#l) =
            ((KLabelConstr (UserConstr (translateLabel label))),
         [], None, False)#(generateKLabelsAux l)"
| "generateKLabelsAux ((ty,tyl,SetTon labels,d,e)#l) =
   (case translateSyntaxSet labels of None \<Rightarrow> generateKLabelsAux l
     | Some labels' \<Rightarrow> (map (\<lambda> (a,b) . (KLabelConstr (UserConstr a),
       (map (\<lambda> x . OtherType (OtherKType x)) b), None, False)) labels')
       @(generateKLabelsAux l))"

fun genHoleKLabels :: "('tVar kType isabType *
    (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list) list
       \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr *
                     'tVar kType isabType list * isabelleStricts option * bool) list" where
"genHoleKLabels [] = []"
| "genHoleKLabels ((x,y)#l) = (if x \<in> extendableFunctionBuiltinTypes \<union> nonExtendableBuiltinTypes
      \<union> {OtherType KResultIsab} then genHoleKLabels l
      else (KLabelConstr (HoleConstr x), [], None, False)#genHoleKLabels l)"

(* form subsort transtive closure of K def *)
function formTransClAux :: "'upVar \<Rightarrow> 'upVar list
         \<Rightarrow> ('upVar * 'upVar list) list \<Rightarrow> 'upVar list \<Rightarrow> 'upVar list" where
"formTransClAux x [] G acc = acc"
| "formTransClAux x (y#l) G acc = (if y \<in> set acc \<or> y = x then formTransClAux x l G acc
       else (case lookup y G of None \<Rightarrow> formTransClAux x l G acc
                 | Some l' \<Rightarrow> formTransClAux x l G (formTransClAux x l' G (y#acc))))"
by pat_completeness auto

fun formTransCl :: "('upVar * 'upVar list) list \<Rightarrow> ('upVar * 'upVar list) list
                \<Rightarrow> ('upVar * 'upVar list) list" where
"formTransCl [] G = []"
| "formTransCl ((x,yl)#l) G = (x,formTransClAux x yl G [])#(formTransCl l G)"

definition subsortTransCl :: "('upVar * 'upVar list) list" where
"subsortTransCl = formTransCl subsortGraph subsortGraph"

(* information about subsort constructors for each type of K def in Isabelle *)
definition allSubsortInfo :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * isabelleStricts option * bool)) list" where
"allSubsortInfo = genSubtypeLabels subsortGraph"

primrec getRidBuiltinSorts :: "'upVar list \<Rightarrow> 'upVar list" where
"getRidBuiltinSorts [] = []"
| "getRidBuiltinSorts (a#l) = (if a \<in> set BuiltinSorts then getRidBuiltinSorts l 
            else a#getRidBuiltinSorts l)"

definition allSubsortableSorts :: "'upVar list" where
"allSubsortableSorts = [KResult, KItem]@(getRidBuiltinSorts
                       (getAllSorts (getAllSyntaxInKFile Theory)))"
(* defining cast function where Cast Term in A to B such that B < A*)

fun insertIntoGraph :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b list) list
     \<Rightarrow> ('a * 'b list) list" where
"insertIntoGraph a b [] = [(a,[b])]"
| "insertIntoGraph a b ((x,y)#l) = (if a = x then ((x,b#y)#l) else (x,y)#insertIntoGraph a b l)"

fun formIsabSubsortGraph :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
 * 'tVar kType isabType list * isabelleStricts option * bool)) list \<Rightarrow>
     ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"formIsabSubsortGraph [] = []"
| "formIsabSubsortGraph ((x,y)#l) = insertIntoGraph x y (formIsabSubsortGraph l)"

(* image of subsort constructor in KLabel class *)
definition isabSubsortGraph :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"isabSubsortGraph = formIsabSubsortGraph (genSubtypeLabels subsortGraph)"

definition subtypeLabelSet :: "('cVar, 'tVar kType isabType, 'var) kConstr list" where
"subtypeLabelSet = (case genSubtypeLabels subsortGraph of sl \<Rightarrow> 
        map (\<lambda> (a,b,c) . KLabelConstr b) sl)"

definition allGeneratedKLabels :: "(('cVar, 'tVar kType isabType, 'var) kConstr *
                     'tVar kType isabType list * isabelleStricts option * bool) list" where
"allGeneratedKLabels = (case syntaxSetToKItemTest of None \<Rightarrow> []
          | Some l \<Rightarrow> (case userSyntaxInIsabTest of None \<Rightarrow> []
      | Some la \<Rightarrow> (map (\<lambda> (a,b) . (KLabelConstr a, b)) (genKItemConstrs (keys la)))@
         (case subtypeLabelSet of subl \<Rightarrow> (map (\<lambda> a . (a,[],None,False)) subl))
      @(genHoleKLabels la)@(generateKLabelsAux l)))"

fun joinMapAux :: "'a \<Rightarrow> 'b list \<Rightarrow> ('a * 'b list) list \<Rightarrow> ('a * 'b list) list" where
"joinMapAux a b [] = [(a,b)]"
| "joinMapAux a b ((x,y)#l) = (if a = x then ((x,b@y)#l) else (x,y)#joinMapAux a b l)"

fun joinMap :: "('a * 'b list) list \<Rightarrow> ('a * 'b list) list \<Rightarrow> ('a * 'b list) list" where
"joinMap [] l = l"
| "joinMap ((x,y)#l) S = joinMap l (joinMapAux x y S)"

primrec genCastConstrsAux :: "'upVar \<Rightarrow> 'upVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list" where
"genCastConstrsAux a [] = []"
| "genCastConstrsAux a (b#l) = (CastConstr (translateRightType b) (translateRightType a),
         [(translateRightType b)], None, True)#(genCastConstrsAux a l)"

primrec genCastConstrs :: "'upVar list \<Rightarrow> 'upVar list \<Rightarrow> ('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"genCastConstrs [] S = []"
| "genCastConstrs (a#l) S = (translateRightType a, genCastConstrsAux a S)#(genCastConstrs l S)"

definition genCastConstrsDef :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"genCastConstrsDef = genCastConstrs allSubsortableSorts allSubsortableSorts"

fun genKLabelForCastAux :: "(('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list
   \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list" where
"genKLabelForCastAux [] = []"
| "genKLabelForCastAux ((a,b)#l) = (KLabelConstr a, [], None, False)#(genKLabelForCastAux l)"

fun genKLabelForCast :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list
   \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list" where
"genKLabelForCast [] = []"
| "genKLabelForCast ((a,b)#l) = (genKLabelForCastAux b)@(genKLabelForCast l)"

definition allGenCastConstrs :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"allGenCastConstrs = (OtherType KLabelIsab, genKLabelForCast genCastConstrsDef)
                  #genCastConstrsDef"

definition userSyntaxWithKLabelAndBuiltinsTest :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list option" where
"userSyntaxWithKLabelAndBuiltinsTest = (case userSyntaxInIsabTest of None \<Rightarrow> None
    | Some l \<Rightarrow> Some (joinMap allGenCastConstrs (joinMap
    (map (\<lambda> (x,y) . (x,[y])) (genSubtypeLabels subsortGraph))
     (joinMap (map (\<lambda> (x,y) . if x = OtherType KLabelIsab
            then (x,allGeneratedKLabels@y) else (x,y)) l) builtinConstrs))))"

(* print out klabel generation function *)

(*define getKLabel function *)
primrec formTermsFromTypes :: "'tVar kType isabType list \<Rightarrow> 'iVar list \<Rightarrow> 
        ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list"
where
"formTermsFromTypes [] S = []"
| "formTermsFromTypes (t#l) S = (case freshIVar S of newVar \<Rightarrow>
        VarTerm t newVar#formTermsFromTypes l (newVar#S))"

fun generateConstrs :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow>
          ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr *
    'tVar kType isabType list * isabelleStricts option * bool) list) list " where
"generateConstrs [] = []"
| "generateConstrs ((x,y)#l) = (if x \<in> nonExtendableBuiltinTypes then
          (x,y)#generateConstrs l else (x,((LabelFormConstr x),
           [OtherType KLabelIsab,IsabList (OtherType SingleKListIsab)],None,False)#y)
           #(generateConstrs l))"

definition userDataTest :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list option" where
"userDataTest = (case userSyntaxWithKLabelAndBuiltinsTest of None \<Rightarrow> None
    | Some l \<Rightarrow> Some (generateConstrs l))"

definition lookupUserDataSet :: "'tVar kType isabType \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list option" where
"lookupUserDataSet t = (case userDataTest of None \<Rightarrow> None
      | Some l \<Rightarrow> lookup t l)"

fun getAllUserSorts :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
  * 'tVar kType isabType list * isabelleStricts option * bool) list) list
   \<Rightarrow> 'tVar kType isabType list" where
"getAllUserSorts [] = []"
| "getAllUserSorts ((a,b)#l) = (if a \<in> extendableBuiltinTypes Un nonExtendableBuiltinTypes
        then getAllUserSorts l else  a#getAllUserSorts l)"

definition allUserTypes :: "'tVar kType isabType list" where
"allUserTypes = (case userDataTest of None \<Rightarrow> []
            | Some l \<Rightarrow> getAllUserSorts l)"

(* function headers :: (('cVar, 'tVar kType isabType, 'var) kConstr * ' tVar list * 'tVar kType isabType) list *)
(* function body :: (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * 'term) list *)

primrec formTermFromList :: "('cVar, 'tVar kType isabType, 'var) kConstr list \<Rightarrow>
  ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"formTermFromList [] = IsabEmptyList"
| "formTermFromList (x#l) = IsabListCon (Term (OtherType KLabelIsab) x []) (formTermFromList l)"

definition subtypeLabelIsabSet :: "('tVar kType isabType,
        ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"subtypeLabelIsabSet = formTermFromList subtypeLabelSet"

(* get klabel functions *)
fun genKLabelFunKLabelBodyAux :: "(('cVar, 'tVar kType isabType, 'var) kConstr *
                     'tVar kType isabType list * isabelleStricts option * bool) list
   \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
    * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list"
 where
"genKLabelFunKLabelBodyAux [] = []"
| "genKLabelFunKLabelBodyAux ((c,tyl,atl)#l) = (case (formTermsFromTypes tyl []) of terms \<Rightarrow>
       (Term (OtherType KLabelIsab) c terms, Term (OtherType KLabelIsab) c terms)
    #genKLabelFunKLabelBodyAux l)"

fun genKLabelFunAllTypeCastList :: "'tVar kType isabType \<Rightarrow>
      (('cVar, 'tVar kType isabType, 'var) kConstr *
                     'tVar kType isabType list * isabelleStricts option * bool) list
   \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
    * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list"
 where
"genKLabelFunAllTypeCastList t [] = []"
| "genKLabelFunAllTypeCastList t ((c,tyl,atl)#l) =
   (case (formTermsFromTypes tyl [IVarOne]) of terms \<Rightarrow>
    (case c of LabelFormConstr ty \<Rightarrow> 
      (Term t c terms, hd terms)#genKLabelFunKLabelBodyAux l
     | _ \<Rightarrow>
       (Term t c terms, CaseList  (AppFun Membership
      [getToken c, setTonLabels]) [(IsabTrue ,Term (OtherType KLabelIsab) (KLabelConstr c) terms),
       (IsabFalse ,Term (OtherType KLabelIsab) (KLabelConstr c) [])])
    #genKLabelFunKLabelBodyAux l))"

definition genKLabelFunKLabelBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType,
              ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"genKLabelFunKLabelBody = (BuiltInFunConstr GetKLabelFun
                (OtherType KLabelIsab), [IVarOne],
     CaseList (VarTerm (OtherType KLabelIsab) IVarOne)
    (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> (case lookup (OtherType KLabelIsab) l of None \<Rightarrow> []
     | Some l' \<Rightarrow> (foldl (\<lambda> acc x . if x \<in> set allGeneratedKLabels then
        (genKLabelFunKLabelBodyAux [x])@acc
       else (genKLabelFunAllTypeCastList (OtherType KLabelIsab) [x])@acc) [] l'))))"

(* klabel generation for all types in a thoery *)

fun genKLabelFunHeaders :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow>
                       (('cVar, 'tVar kType isabType, 'var) kConstr *
                       'tVar kType isabType list * 'tVar kType isabType) list" where
"genKLabelFunHeaders [] = []"
| "genKLabelFunHeaders ((t,y)#l) = (if t \<notin> ((extendableFunctionBuiltinTypes
      Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab, OtherType SingleKIsab,
       OtherType SingleListIsab, OtherType SingleSetIsab, OtherType SingleMapIsab}) then
     (BuiltInFunConstr GetKLabelFun t,[t],OtherType KLabelIsab)
        #genKLabelFunHeaders l else genKLabelFunHeaders l)"

definition genKLabelFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr *
                       'tVar kType isabType list * 'tVar kType isabType) list" where
"genKLabelFunHeadersDef = (case userSyntaxWithKLabelAndBuiltinsTest of None \<Rightarrow> []
     | Some l \<Rightarrow> genKLabelFunHeaders l)"

fun genKLabelFunBodies :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list
    \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType,
      ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"genKLabelFunBodies [] = []"
| "genKLabelFunBodies ((t,y)#l) = (if t \<notin> (extendableFunctionBuiltinTypes
 Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab, OtherType SingleKIsab,
       OtherType SingleListIsab, OtherType SingleSetIsab, OtherType SingleMapIsab}
    then (BuiltInFunConstr GetKLabelFun t, [IVarOne], 
   CaseList (VarTerm t IVarOne) (genKLabelFunAllTypeCastList t y))#genKLabelFunBodies l
      else genKLabelFunBodies l)"

definition KLabelFunBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType,
      ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"KLabelFunBodies = (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> genKLabelFunKLabelBody#genKLabelFunBodies l)"

(*
fun checkNoBuiltinTypes :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr * nat *
                 'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow> bool" where
"checkNoBuiltinTypes [] = True"
| "checkNoBuiltinTypes ((x,y)#l) =
    (if x \<in> nonExtendableBuiltinTypes then False else checkNoBuiltinTypes l)"

definition BuiltinConstrs :: "('cVar, 'tVar kType isabType, 'var) kConstr set" where
"BuiltinConstrs = {QuestionFeature, StarFeature, ListItemIsab, SetItemIsab,
       CellIsab, KItemAsK, MapItemIsab} Un {x . \<exists> d . x = KLabelConstr d}
      Un {x . \<exists> d . x = LabelFormConstr d} Un {x . \<exists> d . x = HoleConstr d}
     Un {x . \<exists> d e . x = BuiltInFunConstr d e} Un {x . \<exists> d . x = KItemConstr d}
   Un {x . \<exists> d . x = CellNameConstr d}"

fun noBuiltinConstrsAux :: "(('cVar, 'tVar kType isabType, 'var) kConstr * nat *
                 'tVar kType isabType list * isabelleStricts option * bool) list \<Rightarrow> bool" where
"noBuiltinConstrsAux [] = True"
| "noBuiltinConstrsAux ((x,y)#l) = (case x of x' \<Rightarrow>
      if x' \<in> BuiltinConstrs then False else noBuiltinConstrsAux l)"

fun noBuiltinConstrs :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr * nat *
                 'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow> bool" where
"noBuiltinConstrs [] = True"
| "noBuiltinConstrs ((x,y)#l) = (noBuiltinConstrsAux y \<and> noBuiltinConstrs l)"

definition userDataTest :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr * nat *
                 'tVar kType isabType list * isabelleStricts option * bool) list) list option" where
"userDataTest = (case syntaxSetToKItemTest of None \<Rightarrow> None
         | Some thy \<Rightarrow> (case (translateSyntax thy) of None \<Rightarrow> None
        | Some thy' \<Rightarrow> if checkNoBuiltinTypes thy'
        \<and> noBuiltinConstrs thy' then Some thy' else None))"
*)

fun toKListFunHeaders :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow>
           (('cVar, 'tVar kType isabType, 'var) kConstr
         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"toKListFunHeaders [] = []"
| "toKListFunHeaders ((t,y)#l) = (if t \<in> (extendableFunctionBuiltinTypes
       Un nonExtendableBuiltinTypes Un {OtherType KItemIsab})
            - {OtherType SingleKListIsab, IsabList (OtherType SingleKListIsab)}
   then (BuiltInFunConstr ToKItemFun t,[t],IsabList (OtherType SingleKListIsab))
                               #toKListFunHeaders l else toKListFunHeaders l)"

definition toKListFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"toKListFunHeadersDef = (case userDataTest of None \<Rightarrow> []
         | Some l \<Rightarrow> toKListFunHeaders l)"

definition toKListFunBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
          * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm) list" where
"toKListFunBodies = [(BuiltInFunConstr ToKListFun (IsabList (OtherType SingleKIsab)),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) KCellIsab [VarTerm
            (IsabList (OtherType SingleKIsab)) IVarOne]]) IsabEmptyList),
        (BuiltInFunConstr ToKListFun (IsabList (OtherType SingleListIsab)),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) ListCellIsab [VarTerm
            (IsabList (OtherType SingleKListIsab)) IVarOne]]) IsabEmptyList),
        (BuiltInFunConstr ToKListFun (IsabList (OtherType SingleSetIsab)),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) SetCellIsab [VarTerm
            (IsabList (OtherType SingleSetIsab)) IVarOne]]) IsabEmptyList),
        (BuiltInFunConstr ToKListFun (IsabList (OtherType SingleMapIsab)),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) MapCellIsab [VarTerm
            (IsabList (OtherType SingleMapIsab)) IVarOne]]) IsabEmptyList),
       (BuiltInFunConstr ToKListFun (IsabList (OtherType SingleBagIsab)),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) BagCellIsab [VarTerm
            (IsabList (OtherType SingleBagIsab)) IVarOne]]) IsabEmptyList),
        (BuiltInFunConstr ToKListFun (OtherType KItemIsab),
              [IVarOne], IsabListCon (Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellConType) KCellIsab [IsabListCon
           (Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab)
        IVarOne]) IsabEmptyList]]) IsabEmptyList)]"

fun toKItemFunHeaders :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list \<Rightarrow>
           (('cVar, 'tVar kType isabType, 'var) kConstr
         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"toKItemFunHeaders [] = []"
| "toKItemFunHeaders ((t,y)#l) = (if t \<in> extendableFunctionBuiltinTypes
    Un nonExtendableBuiltinTypes
   then toKItemFunHeaders l else(BuiltInFunConstr ToKItemFun t,[t],t)
                               #toKItemFunHeaders l)"

definition toKItemFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"toKItemFunHeadersDef = (case userDataTest of None \<Rightarrow> []
         | Some l \<Rightarrow> toKItemFunHeaders l)"

primrec toKItemFunPatTypes :: "'tVar kType isabType list \<Rightarrow> 'iVar list \<Rightarrow> ('tVar kType isabType,
       ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list" where
"toKItemFunPatTypes [] S = []"
| "toKItemFunPatTypes (t#l) S = (case freshIVar S of newVar \<Rightarrow>
   (case (toKItemFunPatTypes l (newVar#S)) of l' \<Rightarrow>
          (VarTerm t newVar)#l'))"

fun toKItemKListFunExpTypes :: "'tVar kType isabType list \<Rightarrow>
      ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
     \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"toKItemKListFunExpTypes al [] = IsabEmptyList"
| "toKItemKListFunExpTypes [] el = IsabEmptyList"
| "toKItemKListFunExpTypes (t#al) (e#el) = (case t of IsabList (OtherType SingleKListIsab) \<Rightarrow>
     IsabListAt e (toKItemKListFunExpTypes al el)
   | OtherType KLabelIsab \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (OtherType KLabelIsab)) [e]) (toKItemKListFunExpTypes al el)
   | (IsabList (OtherType SingleListIsab)) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (IsabList (OtherType SingleListIsab))) [e]) (toKItemKListFunExpTypes al el)
   | (IsabList (OtherType SingleSetIsab)) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (IsabList (OtherType SingleSetIsab))) [e]) (toKItemKListFunExpTypes al el)
   | (IsabList (OtherType SingleMapIsab)) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (IsabList (OtherType SingleMapIsab))) [e]) (toKItemKListFunExpTypes al el)
   | (IsabList (OtherType SingleBagIsab)) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (IsabList (OtherType SingleBagIsab))) [e]) (toKItemKListFunExpTypes al el)
   | (IsabList (OtherType SingleKIsab)) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (IsabList (OtherType SingleKIsab))) [e]) (toKItemKListFunExpTypes al el)
   | (OtherType KItemIsab) \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr
        ToKListFun (OtherType KItemIsab)) [e]) (toKItemKListFunExpTypes al el)
   | _ \<Rightarrow> IsabListAt (AppFun (BuiltInFunConstr ToKListFun (OtherType KItemIsab))
             [Term (OtherType KItemIsab) (KItemConstr t)
        [AppFun (BuiltInFunConstr ToKItemFun t) [e]]]) (toKItemKListFunExpTypes al el))"

fun toKItemFunAux :: "'tVar kType isabType \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * isabelleStricts option * bool) list  \<Rightarrow> 'iVar list
  \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
 * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"toKItemFunAux t [] S = []"
| "toKItemFunAux t ((a,b,c,d)#l) S = (case toKItemFunPatTypes b S of terms \<Rightarrow>
       (case toKItemFunAux t l S of l' \<Rightarrow>
     (if a = LabelFormConstr t then (Term t a terms, Term t a terms)#l' else 
     (Term t a terms, Term t (LabelFormConstr t) [AppFun (BuiltInFunConstr GetKLabelFun t)
             [Term t a terms],toKItemKListFunExpTypes b terms])#l')))"

primrec toKItemFunBodies :: "'tVar kType isabType list \<Rightarrow> (('cVar, 'tVar kType isabType,
         'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"toKItemFunBodies [] = []"
| "toKItemFunBodies (t#l) = (if t \<in> extendableFunctionBuiltinTypes
    Un nonExtendableBuiltinTypes then toKItemFunBodies l
   else (case lookupUserDataSet t of None \<Rightarrow> toKItemFunBodies l
       | Some sl \<Rightarrow> (case toKItemFunAux t sl [IVarOne] of cl \<Rightarrow>
   (BuiltInFunConstr ToKItemFun t,
       [IVarOne], CaseList (VarTerm t IVarOne) cl))#toKItemFunBodies l))"

definition toKItemFunBodiesDef :: "(('cVar, 'tVar kType isabType,
         'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"toKItemFunBodiesDef = (case userDataTest of None \<Rightarrow> []
         | Some l \<Rightarrow> toKItemFunBodies (keys l))"

fun toKItemFunKabelBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * isabelleStricts option * bool) list
    \<Rightarrow> 'iVar list \<Rightarrow>
       (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
 * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"toKItemFunKabelBodies [] S = []"
| "toKItemFunKabelBodies ((a,b,c)#l) S = (case (formTermsFromTypes b S) of terms \<Rightarrow>
      (if (a,b,c) \<in> set allGeneratedKLabels then
        (Term (OtherType KLabelIsab) a terms,
        Term (OtherType KLabelIsab) (LabelFormConstr (OtherType KLabelIsab))
              [Term (OtherType KLabelIsab) a terms, IsabEmptyList])#toKItemFunKabelBodies l S
      else (Term (OtherType KLabelIsab) a terms, toKItemKListFunExpTypes b terms)
           #toKItemFunKabelBodies l S))"

definition toKItemFunKabelBodiesDef :: "(('cVar, 'tVar kType isabType,
         'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"toKItemFunKabelBodiesDef = (case userDataTest of None \<Rightarrow> []
   | Some l \<Rightarrow> (case lookup (OtherType KLabelIsab) l of None \<Rightarrow> []
    | Some la \<Rightarrow> case toKItemFunKabelBodies la [IVarOne] of cl \<Rightarrow>
        [(BuiltInFunConstr ToKItemFun (OtherType KLabelIsab), [IVarOne],
          CaseList (VarTerm (OtherType KLabelIsab) IVarOne) cl)]))"

(*
definition toSingleKListFunHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"toSingleKListFunHeaders = (BuiltInFunConstr ToKItemFun (OtherType SingleKListIsab),
              [OtherType KItemIsab], IsabList (OtherType SingleKListIsab))"

definition toSingleKListFunBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
           * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
        'iVar) isabTerm)" where
"toSingleKListFunBodies = (BuiltInFunConstr ToKItemFun (OtherType SingleKListIsab),
              [IVarOne], Term (OtherType SingleKListIsab)
         CellAsKList [Term (OtherType CellType) KCellIsab
          [IsabListCon (Term (OtherType SingleKListIsab)
           KItemAsK [VarTerm (OtherType KItemIsab) IVarOne]) IsabEmptyList]])"
*)

primrec genKItemKListFunHeaders :: "'tVar kType isabType list
                 \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                   * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genKItemKListFunHeaders [] = []"
| "genKItemKListFunHeaders (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) - - {OtherType KLabelIsab, OtherType SingleKIsab,
       OtherType SingleListIsab, OtherType SingleSetIsab, OtherType SingleMapIsab}
      then genKItemKListFunHeaders l else
        (BuiltInFunConstr GetKListFun t,[t],IsabList (OtherType SingleKListIsab))
        #genKItemKListFunHeaders l)"

definition getKListFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
                   * 'tVar kType isabType list * 'tVar kType isabType) list" where
"getKListFunHeadersDef = (case userDataTest of None \<Rightarrow> []
        | Some l \<Rightarrow> genKItemKListFunHeaders (keys l))"

primrec genKItemKListFunBodies :: "'tVar kType isabType list \<Rightarrow> (('cVar, 'tVar kType isabType,
                 'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"genKItemKListFunBodies [] = []"
| "genKItemKListFunBodies (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab} then 
      (BuiltInFunConstr GetKListFun t, [IVarOne],
       CaseList (AppFun (BuiltInFunConstr ToKItemFun t) [VarTerm t IVarOne])
          [(Term t (LabelFormConstr t) [VarTerm (OtherType KLabelIsab) IVarTwo,
                     VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree],
          VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)])
        #genKItemKListFunBodies l else genKItemKListFunBodies l)"

definition getKListFunBodiesDef :: "(('cVar, 'tVar kType isabType,
     'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"getKListFunBodiesDef = (case userDataTest of None \<Rightarrow> []
        | Some l \<Rightarrow> genKItemKListFunBodies (keys l))"

fun getKListFunBuiltinTypeBodies :: "'tVar kType isabType \<Rightarrow>
   (('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * isabelleStricts option * bool) list \<Rightarrow> 'iVar list \<Rightarrow>
   (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm *
    ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"getKListFunBuiltinTypeBodies t [] S = []"
| "getKListFunBuiltinTypeBodies t ((a,b,c)#l) S = (case (formTermsFromTypes b S) of terms \<Rightarrow>
   (Term t a terms, toKItemKListFunExpTypes b terms)#getKListFunBuiltinTypeBodies t l S)"

definition getKListFunBuiltinTypeBodiesDef :: "(('cVar, 'tVar kType isabType,
     'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm) list" where
"getKListFunBuiltinTypeBodiesDef = (case userDataTest of None \<Rightarrow> []
   | Some l \<Rightarrow> (case lookup (OtherType SingleKIsab) l of None \<Rightarrow> []
          | Some la \<Rightarrow> [(BuiltInFunConstr GetKListFun (OtherType SingleKIsab),[IVarOne],
   CaseList (VarTerm (OtherType SingleKIsab) IVarOne)
  (getKListFunBuiltinTypeBodies (OtherType SingleKIsab) la [IVarOne]))])
  @(case lookup (OtherType SingleListIsab) l of None \<Rightarrow> []
          | Some la \<Rightarrow> [(BuiltInFunConstr GetKListFun (OtherType SingleListIsab),[IVarOne],
   CaseList (VarTerm (OtherType SingleListIsab) IVarOne)
  (getKListFunBuiltinTypeBodies (OtherType SingleListIsab) la [IVarOne]))])
  @(case lookup (OtherType SingleSetIsab) l of None \<Rightarrow> []
          | Some la \<Rightarrow> [(BuiltInFunConstr GetKListFun (OtherType SingleSetIsab),[IVarOne],
   CaseList (VarTerm (OtherType SingleSetIsab) IVarOne)
  (getKListFunBuiltinTypeBodies (OtherType SingleSetIsab) la [IVarOne]))])
  @(case lookup (OtherType SingleMapIsab) l of None \<Rightarrow> []
          | Some la \<Rightarrow> [(BuiltInFunConstr GetKListFun (OtherType SingleMapIsab),[IVarOne],
   CaseList (VarTerm (OtherType SingleMapIsab) IVarOne)
  (getKListFunBuiltinTypeBodies (OtherType SingleMapIsab) la [IVarOne]))]))"

definition getCoreKLabelFunKListHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"getCoreKLabelFunKListHeader = (BuiltInFunConstr GetCoreKLabelFun (IsabList (OtherType
  SingleKListIsab)), [IsabList (OtherType SingleKListIsab)], IsabOption (OtherType KLabelIsab))"

definition getCoreKLabelFunKListBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm)" where
"getCoreKLabelFunKListBody = (BuiltInFunConstr GetCoreKLabelFun (IsabList (OtherType SingleKListIsab)),
     [IVarOne], CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarOne) [((IsabListCon
    (Term (OtherType SingleKListIsab) CellAsKList [Term (OtherType CellConType) KCellIsab
       [IsabListCon (Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab) IVarTwo])
  IsabEmptyList]]) IsabEmptyList), AppFun (BuiltInFunConstr GetCoreKLabelFun (OtherType KItemIsab))
       [IsabSome (VarTerm  (OtherType KItemIsab) IVarTwo)]), (CaseOwise, IsabNone)])"

primrec getCoreKLabelFunHeaders :: "'tVar kType isabType list \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
       * 'tVar kType isabType) list" where
"getCoreKLabelFunHeaders [] = []"
| "getCoreKLabelFunHeaders (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab} then getCoreKLabelFunHeaders l
   else (BuiltInFunConstr GetCoreKLabelFun t,[t],
         IsabOption (OtherType KLabelIsab))#getCoreKLabelFunHeaders l)"

definition getCoreKLabelFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType) list" where
"getCoreKLabelFunHeadersDef = (case userDataTest of None \<Rightarrow> []
        | Some l \<Rightarrow> getCoreKLabelFunHeaders (keys l))"

definition getCoreKLabelFunKLabelBody ::
    "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType,
         ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"getCoreKLabelFunKLabelBody = (BuiltInFunConstr GetCoreKLabelFun (OtherType KLabelIsab), [IVarOne],
    IsabSome (AppFun (BuiltInFunConstr GetKLabelFun (OtherType KLabelIsab))
       [VarTerm (OtherType KLabelIsab) IVarOne]))"

primrec getCoreKLabelFunBodies :: "'tVar kType isabType list \<Rightarrow>
           (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType,
         ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"getCoreKLabelFunBodies [] = []"
| "getCoreKLabelFunBodies (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) then
     (BuiltInFunConstr GetCoreKLabelFun t, [IVarOne],
       (CaseList (VarTerm t IVarOne) [(Term t (LabelFormConstr t)
        [(VarTerm (OtherType KLabelIsab) IVarTwo),
     (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)],
      CaseList (AppFun Membership [VarTerm (OtherType KLabelIsab) IVarTwo, subtypeLabelIsabSet])
     [(IsabTrue, AppFun (BuiltInFunConstr GetCoreKLabelFun (IsabList (OtherType SingleKListIsab)))
      [(VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)]),
         (IsabFalse, IsabSome (VarTerm (OtherType KLabelIsab) IVarTwo))]), (CaseOwise,
        CaseList (AppFun (BuiltInFunConstr ToKItemFun t) [VarTerm t IVarOne])
        [(Term t (LabelFormConstr t) [(VarTerm (OtherType KLabelIsab) IVarTwo),
           (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)],
      CaseList (AppFun Membership [VarTerm (OtherType KLabelIsab) IVarTwo, subtypeLabelIsabSet])
     [(IsabTrue, AppFun (BuiltInFunConstr GetCoreKLabelFun (IsabList (OtherType SingleKListIsab)))
      [(VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)]), (IsabFalse,
        IsabSome (VarTerm (OtherType KLabelIsab) IVarTwo))]), (CaseOwise, IsabNone)])]))
     #getCoreKLabelFunBodies l else getCoreKLabelFunBodies l)"

definition getCoreKLabelFunBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType,
         ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"getCoreKLabelFunBodiesDef = (case userDataTest of None \<Rightarrow> []
     | Some l \<Rightarrow> getCoreKLabelFunBodies (keys l))"

definition getCoreKListFunKListHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"getCoreKListFunKListHeader = (BuiltInFunConstr GetCoreKListFun (IsabList
 (OtherType SingleKListIsab)), [(IsabList (OtherType SingleKListIsab))],
               IsabOption (IsabList (OtherType SingleKListIsab)))"

definition getCoreKListFunKListBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"getCoreKListFunKListBody = (BuiltInFunConstr GetCoreKListFun (IsabList (OtherType SingleKListIsab)),
     [IVarOne], CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarOne) [((IsabListCon
  (Term (OtherType SingleKListIsab) CellAsKList
      [Term (OtherType CellConType) KCellIsab [IsabListCon  (Term (OtherType SingleKIsab)
       KItemAsK [VarTerm (OtherType KItemIsab) IVarTwo]) IsabEmptyList]]) IsabEmptyList),
       AppFun (BuiltInFunConstr GetCoreKListFun (OtherType KItemIsab))
       [VarTerm (OtherType KItemIsab) IVarTwo]), (CaseOwise, IsabNone)])"

primrec getCoreKListFunHeaders :: "'tVar kType isabType list
             \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
             * 'tVar kType isabType list * 'tVar kType isabType) list" where
"getCoreKListFunHeaders [] = []"
| "getCoreKListFunHeaders (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab} then
    (BuiltInFunConstr GetCoreKListFun t,[t],
         IsabOption (IsabList (OtherType SingleKListIsab)))#getCoreKListFunHeaders l
     else getCoreKListFunHeaders l)"

definition getCoreKListFunHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
             * 'tVar kType isabType list * 'tVar kType isabType) list" where
"getCoreKListFunHeadersDef = (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> getCoreKListFunHeaders (keys l))"

definition getCoreKListFunKLabelBody ::
    "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType,
       ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"getCoreKListFunKLabelBody = (BuiltInFunConstr GetCoreKListFun (OtherType KLabelIsab), [IVarOne],
    IsabSome (AppFun (BuiltInFunConstr GetKListFun (OtherType KLabelIsab))
       [VarTerm (OtherType KLabelIsab) IVarOne]))"

primrec getCoreKListFunBodies :: "'tVar kType isabType list \<Rightarrow>
        (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType,
       ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"getCoreKListFunBodies [] = []"
| "getCoreKListFunBodies (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) then
    (BuiltInFunConstr GetCoreKListFun t, [IVarOne],
       (CaseList (VarTerm t IVarOne) [(Term t (LabelFormConstr t)
        [(VarTerm (OtherType KLabelIsab) IVarTwo),
           (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)],
      CaseList (AppFun Membership [VarTerm (OtherType KLabelIsab) IVarTwo, subtypeLabelIsabSet])
     [(IsabTrue, AppFun (BuiltInFunConstr GetCoreKListFun (IsabList (OtherType SingleKListIsab)))
      [(VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)]),
         (IsabFalse, IsabSome (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree))]),
   (CaseOwise, CaseList (AppFun (BuiltInFunConstr ToKItemFun t)
           [VarTerm t IVarOne]) [(Term t (LabelFormConstr t)
        [(VarTerm (OtherType KLabelIsab) IVarTwo),
           (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)],
      CaseList (AppFun Membership [VarTerm (OtherType KLabelIsab) IVarTwo, subtypeLabelIsabSet])
     [(IsabTrue, AppFun (BuiltInFunConstr GetCoreKListFun (IsabList (OtherType SingleKListIsab)))
      [(VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree)]),
         (IsabFalse, IsabSome (VarTerm (IsabList (OtherType SingleKListIsab)) IVarThree))]),
   (CaseOwise, IsabNone)])]))#getCoreKListFunBodies l else getCoreKListFunBodies l)"

definition getCoreKListFunBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'iVar list * ('tVar kType isabType,
       ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"getCoreKListFunBodiesDef = (case userDataTest of None \<Rightarrow> []
        | Some l \<Rightarrow> (getCoreKListFunBodies (keys l)))"

(* family of congruence functions on syntactic equivalence of two terms *)
primrec congruenceHeaders :: "'tVar kType isabType list \<Rightarrow>
             (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * 'tVar kType isabType) list" where
"congruenceHeaders [] = []"
| "congruenceHeaders (t#l) = (BuiltInFunConstr Congruence t, [t, t], BoolIsab)#congruenceHeaders l"

definition congruenceHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
  * 'tVar kType isabType list * 'tVar kType isabType) list" where
"congruenceHeadersDef = (case userDataTest of None \<Rightarrow> []
        | Some l \<Rightarrow> (congruenceHeaders (keys l)))"

primrec congruenceBodies :: "'tVar kType isabType list \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"congruenceBodies [] = []"
| "congruenceBodies (t#l) = (if t \<in> (extendableFunctionBuiltinTypes
  Un nonExtendableBuiltinTypes) - {OtherType KLabelIsab} then
    (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
    (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
    (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
    (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
 (BuiltInFunConstr Congruence t, [IVarOne, IVarTwo],
   (IsabAnd
      (CaseList (AppFun (BuiltInFunConstr GetCoreKLabelFun t) [VarTerm t IVarOne])
     [(IsabNone,IsabFalse), (IsabSome (VarTerm (OtherType KLabelIsab) newVar),
     CaseList (AppFun (BuiltInFunConstr GetCoreKLabelFun t) [VarTerm t IVarTwo])
     [(IsabNone, IsabFalse), (IsabSome (VarTerm (OtherType KLabelIsab) newVara), 
    IsabEqual (VarTerm (OtherType KLabelIsab) newVar) (VarTerm (OtherType KLabelIsab) newVara))])])
   (CaseList (AppFun (BuiltInFunConstr GetCoreKListFun t) [VarTerm t IVarOne])
     [(IsabNone,IsabFalse), (IsabSome (VarTerm (IsabList (OtherType SingleKListIsab)) newVarb),
     CaseList (AppFun (BuiltInFunConstr GetCoreKListFun t) [VarTerm t IVarTwo])
     [(IsabNone, IsabFalse), (IsabSome (VarTerm (IsabList (OtherType SingleKListIsab)) newVarc), 
  IsabEqual (VarTerm (IsabList (OtherType SingleKListIsab)) newVarb)
        (VarTerm (IsabList (OtherType SingleKListIsab)) newVarc))])])))#congruenceBodies l))))
   else congruenceBodies l)"

definition congruenceBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'iVar list * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"congruenceBodiesDef = (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> congruenceBodies (keys l))"

definition congruenceKListHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceKListHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)),
   [(IsabList (OtherType SingleKListIsab)), (IsabList (OtherType SingleKListIsab))], BoolIsab)"

definition congruenceKListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"congruenceKListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarOne)
    [(IsabEmptyList, CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarTwo)
    [(IsabEmptyList, IsabTrue), (CaseOwise, IsabFalse)]),
     (IsabListCon (VarTerm (OtherType SingleKListIsab) newVar)
               (VarTerm (IsabList (OtherType SingleKListIsab)) newVara),
       CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarTwo)
    [(IsabEmptyList, IsabFalse), (IsabListCon (VarTerm (OtherType SingleKListIsab) newVarb)
       (VarTerm (IsabList (OtherType SingleKListIsab)) newVarc),
        IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType SingleKListIsab))
    [(VarTerm (OtherType SingleKListIsab) newVar), (VarTerm (OtherType SingleKListIsab) newVarb)])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)))
               [(VarTerm (IsabList (OtherType SingleKListIsab)) newVara),
       (VarTerm (IsabList (OtherType SingleKListIsab)) newVarc)]))])])))))"

definition congruenceSingleKListHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleKListHeaders = (BuiltInFunConstr Congruence (OtherType SingleKListIsab),
   [(OtherType SingleKListIsab), (OtherType SingleKListIsab)], BoolIsab)"

definition congruenceSingleKListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm)" where
"congruenceSingleKListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleKListIsab), [IVarOne, IVarTwo],
   CaseList (VarTerm (OtherType SingleKListIsab) IVarOne)
     [(Term (OtherType SingleKListIsab) CellAsKList [VarTerm (OtherType CellConType) newVar],
      CaseList (VarTerm (OtherType SingleKListIsab) IVarTwo)
     [(Term (OtherType SingleKListIsab) CellAsKList [VarTerm (OtherType CellConType) newVara],
   AppFun (BuiltInFunConstr Congruence (OtherType CellConType))
    [VarTerm (OtherType CellConType) newVar,
       VarTerm (OtherType CellConType) newVara]), (CaseOwise, IsabFalse)]),
      (Term (OtherType SingleKListIsab) KLabelAsKList
      [VarTerm (OtherType KLabelIsab) newVar],CaseList (VarTerm (OtherType SingleKListIsab) IVarTwo)
     [(Term (OtherType SingleKListIsab) KLabelAsKList [VarTerm (OtherType KLabelIsab) newVara],
  AppFun (BuiltInFunConstr Congruence (OtherType KLabelIsab)) [VarTerm (OtherType KLabelIsab) newVar,
       VarTerm (OtherType KLabelIsab) newVara]), (CaseOwise, IsabFalse)])])))"

definition congruenceCellConTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
          * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceCellConTypeHeaders = (BuiltInFunConstr Congruence (OtherType CellConType),
   [(OtherType CellConType), (OtherType CellConType)], BoolIsab)"

definition congruenceCellConTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"congruenceCellConTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
   (BuiltInFunConstr Congruence (OtherType CellConType), [IVarOne, IVarTwo],
      CaseList (VarTerm (OtherType CellConType) IVarOne)
       [(Term (OtherType CellConType) KCellIsab [VarTerm (IsabList (OtherType SingleKIsab)) newVar],
        CaseList (VarTerm (OtherType CellConType) IVarTwo) [(Term (OtherType CellConType) KCellIsab
    [VarTerm (IsabList (OtherType SingleKIsab)) newVara],  AppFun (BuiltInFunConstr Congruence
    (IsabList (OtherType SingleKIsab))) [VarTerm (IsabList (OtherType SingleKIsab)) newVar,
         VarTerm (IsabList (OtherType SingleKIsab)) newVara]), (CaseOwise, IsabFalse)]),
  (Term (OtherType CellConType) ListCellIsab [VarTerm (IsabList (OtherType SingleListIsab)) newVar],
        CaseList (VarTerm (OtherType CellConType) IVarTwo) [(Term (OtherType CellConType) ListCellIsab
    [VarTerm (IsabList (OtherType SingleListIsab)) newVara],  AppFun (BuiltInFunConstr Congruence
    (IsabList (OtherType SingleListIsab))) [VarTerm (IsabList (OtherType SingleListIsab)) newVar,
         VarTerm (IsabList (OtherType SingleListIsab)) newVara]), (CaseOwise, IsabFalse)]),
    (Term (OtherType CellConType) SetCellIsab [VarTerm (IsabList (OtherType SingleSetIsab)) newVar],
        CaseList (VarTerm (OtherType CellConType) IVarTwo) [(Term (OtherType CellConType) SetCellIsab
    [VarTerm (IsabList (OtherType SingleSetIsab)) newVara],  AppFun (BuiltInFunConstr Congruence
    (IsabList (OtherType SingleSetIsab))) [VarTerm (IsabList (OtherType SingleSetIsab)) newVar,
         VarTerm (IsabList (OtherType SingleSetIsab)) newVara]), (CaseOwise, IsabFalse)]),
   (Term (OtherType CellConType) MapCellIsab [VarTerm (IsabList (OtherType SingleMapIsab)) newVar],
        CaseList (VarTerm (OtherType CellConType) IVarTwo) [(Term (OtherType CellConType) MapCellIsab
    [VarTerm (IsabList (OtherType SingleMapIsab)) newVara],  AppFun (BuiltInFunConstr Congruence
    (IsabList (OtherType SingleMapIsab))) [VarTerm (IsabList (OtherType SingleMapIsab)) newVar,
         VarTerm (IsabList (OtherType SingleMapIsab)) newVara]), (CaseOwise, IsabFalse)]),
    (Term (OtherType CellConType) BagCellIsab [VarTerm (IsabList (OtherType SingleBagIsab)) newVar],
        CaseList (VarTerm (OtherType CellConType) IVarTwo) [(Term (OtherType CellConType) BagCellIsab
    [VarTerm (IsabList (OtherType SingleBagIsab)) newVara],  AppFun (BuiltInFunConstr Congruence
    (IsabList (OtherType SingleBagIsab))) [VarTerm (IsabList (OtherType SingleBagIsab)) newVar,
         VarTerm (IsabList (OtherType SingleBagIsab)) newVara]), (CaseOwise, IsabFalse)])])))"
                                
definition congruenceKHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceKHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)),
   [IsabList (OtherType SingleKIsab), IsabList (OtherType SingleKIsab)], BoolIsab)"

definition congruenceKBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"congruenceKBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleKIsab)) IVarOne)
    [(IsabEmptyList, CaseList (VarTerm (IsabList (OtherType SingleKIsab)) IVarTwo)
    [(IsabEmptyList, IsabTrue), (CaseOwise, IsabFalse)]),
     (IsabListCon (VarTerm (OtherType SingleKIsab) newVar)
        (VarTerm (IsabList (OtherType SingleKIsab)) newVara),
       CaseList (VarTerm (IsabList (OtherType SingleKIsab)) IVarTwo)
    [(IsabEmptyList, IsabFalse), (IsabListCon (VarTerm (OtherType SingleKIsab) newVarb)
       (VarTerm (IsabList (OtherType SingleKIsab)) newVarc),
        IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType SingleKIsab))
           [(VarTerm (OtherType SingleKIsab) newVar), (VarTerm (OtherType SingleKIsab) newVarb)])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)))
               [(VarTerm (IsabList (OtherType SingleKIsab)) newVara),
       (VarTerm (IsabList (OtherType SingleKIsab)) newVarc)]))])])))))"

definition congruenceSingleKHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleKHeaders = (BuiltInFunConstr Congruence (OtherType SingleKIsab),
   [(OtherType SingleKIsab), (OtherType SingleKIsab)], BoolIsab)"

definition congruenceSingleKBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"congruenceSingleKBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleKIsab), [IVarOne, IVarTwo],
    CaseList (VarTerm (OtherType SingleKIsab) IVarOne)
      [(Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab) newVar],
      CaseList (VarTerm (OtherType SingleKIsab) IVarTwo)
      [(Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab) newVara],
  AppFun (BuiltInFunConstr Congruence (OtherType KItemIsab))
        [VarTerm (OtherType KItemIsab) newVar, VarTerm (OtherType KItemIsab) newVara]),
  (CaseOwise, IsabFalse)]), (CaseOwise, CaseList (VarTerm (OtherType SingleKIsab) IVarTwo)
      [(Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab) newVara], IsabFalse),
 (CaseOwise, IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType KLabelIsab))
      [(AppFun (BuiltInFunConstr GetKLabelFun (OtherType SingleKIsab))
        [VarTerm (OtherType SingleKIsab) IVarOne]),
         (AppFun (BuiltInFunConstr GetKLabelFun (OtherType SingleKIsab))
      [VarTerm (OtherType SingleKIsab) IVarTwo])])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)))
            [(AppFun (BuiltInFunConstr GetKListFun (OtherType SingleKIsab))
      [VarTerm (OtherType SingleKIsab) IVarOne]),
          (AppFun (BuiltInFunConstr GetKListFun (OtherType SingleKIsab))
     [VarTerm (OtherType SingleKIsab) IVarTwo])])
      )])])))" 

definition congruenceListHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceListHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleListIsab)),
   [IsabList (OtherType SingleListIsab), IsabList (OtherType SingleListIsab)], BoolIsab)"

definition congruenceListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
     'var) kConstr, 'iVar) isabTerm)" where
"congruenceListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleListIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleListIsab)) IVarOne)
    [(IsabEmptyList, CaseList (VarTerm (IsabList (OtherType SingleListIsab)) IVarTwo)
    [(IsabEmptyList, IsabTrue), (CaseOwise, IsabFalse)]),
     (IsabListCon (VarTerm (OtherType SingleListIsab) newVar) (VarTerm
        (IsabList (OtherType SingleListIsab)) newVara),
       CaseList (VarTerm (IsabList (OtherType SingleListIsab)) IVarTwo)
    [(IsabEmptyList, IsabFalse),  (IsabListCon (VarTerm (OtherType SingleListIsab) newVarb)
       (VarTerm (IsabList (OtherType SingleListIsab)) newVarc),
        IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType SingleListIsab))
     [(VarTerm (OtherType SingleListIsab) newVar),
        (VarTerm (OtherType SingleListIsab) newVarb)])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleListIsab)))
               [(VarTerm (IsabList (OtherType SingleListIsab)) newVara),
       (VarTerm (IsabList (OtherType SingleListIsab)) newVarc)]))])])))))"

definition congruenceSingleListHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
             * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleListHeaders = (BuiltInFunConstr Congruence (OtherType SingleListIsab),
   [(OtherType SingleListIsab), (OtherType SingleListIsab)], BoolIsab)"

definition congruenceSingleListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"congruenceSingleListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleListIsab), [IVarOne, IVarTwo],
    CaseList (VarTerm (OtherType SingleListIsab) IVarOne)
      [(Term (OtherType SingleListIsab) KAsList [VarTerm (IsabList (OtherType SingleKIsab)) newVar],
             CaseList (VarTerm (OtherType SingleListIsab) IVarTwo)
      [(Term (OtherType SingleListIsab) KAsList [VarTerm (IsabList (OtherType SingleKIsab)) newVara],
        AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)))
       [VarTerm (IsabList (OtherType SingleKIsab)) newVar,
       VarTerm (IsabList (OtherType SingleKIsab)) newVara]), (CaseOwise, IsabFalse)]),
     (CaseOwise, CaseList (VarTerm (OtherType SingleListIsab) IVarTwo)
    [(Term (OtherType SingleListIsab) KAsList [VarTerm (IsabList (OtherType SingleKIsab)) newVara],
     IsabFalse), (CaseOwise, IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType KLabelIsab))
      [(AppFun (BuiltInFunConstr GetKLabelFun
    (OtherType SingleListIsab)) [VarTerm (OtherType SingleListIsab) IVarOne]),
         (AppFun (BuiltInFunConstr GetKLabelFun (OtherType SingleListIsab))
     [VarTerm (OtherType SingleListIsab) IVarTwo])])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)))
          [(AppFun (BuiltInFunConstr GetKListFun (OtherType SingleListIsab))
   [VarTerm (OtherType SingleListIsab) IVarOne]), (AppFun (BuiltInFunConstr GetKListFun
  (OtherType SingleListIsab)) [VarTerm (OtherType SingleListIsab) IVarTwo])]))])])))"

definition kMembershipInSetHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"kMembershipInSetHeader = (BuiltInFunConstr KMembership (OtherType SingleSetIsab),
   [(OtherType SingleSetIsab), IsabList (OtherType SingleSetIsab)], BoolIsab)"

definition kMembershipInSetBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"kMembershipInSetBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr KMembership (OtherType SingleSetIsab),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleSetIsab)) IVarTwo) [(IsabEmptyList, IsabFalse),
     (IsabListCon (VarTerm (OtherType SingleSetIsab) newVar)
     (VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
       IsabOr (AppFun (BuiltInFunConstr Congruence (OtherType SingleSetIsab))
        [(VarTerm (OtherType SingleSetIsab) IVarOne), (VarTerm (OtherType SingleSetIsab) newVar)])
        (AppFun (BuiltInFunConstr KMembership (IsabList (OtherType SingleSetIsab)))
        [(VarTerm (OtherType SingleSetIsab) IVarOne),
              (VarTerm (IsabList (OtherType SingleSetIsab)) newVara)]))])))"

definition kSubsetInSetHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"kSubsetInSetHeader = (BuiltInFunConstr KSubset (IsabList (OtherType SingleSetIsab)),
   [IsabList (OtherType SingleSetIsab), IsabList (OtherType SingleSetIsab)], BoolIsab)"

definition kSubsetInSetBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
          * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"kSubsetInSetBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr KSubset (IsabList (OtherType SingleSetIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleSetIsab)) IVarOne)  [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleSetIsab) newVar)
    (VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
       IsabAnd (AppFun (BuiltInFunConstr KMembership (OtherType SingleSetIsab))
        [(VarTerm (OtherType SingleSetIsab) newVar),
           (VarTerm (IsabList (OtherType SingleSetIsab)) IVarTwo)])
        (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleSetIsab)))
        [(VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
              (VarTerm (IsabList (OtherType SingleSetIsab)) IVarTwo)]))])))"

definition congruenceSetHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSetHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleSetIsab)),
   [IsabList (OtherType SingleSetIsab), IsabList (OtherType SingleSetIsab)], BoolIsab)"

definition congruenceSetBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"congruenceSetBodies = 
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleSetIsab)),[IVarOne, IVarTwo],
    IsabAnd (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleSetIsab)))
       [VarTerm (IsabList (OtherType SingleSetIsab)) IVarOne,
       VarTerm (IsabList (OtherType SingleSetIsab)) IVarTwo])
    (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleSetIsab)))
       [VarTerm (IsabList (OtherType SingleSetIsab)) IVarTwo,
    VarTerm (IsabList (OtherType SingleSetIsab)) IVarOne]))"

definition congruenceSingleSetHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleSetHeaders = (BuiltInFunConstr Congruence (OtherType SingleSetIsab),
   [(OtherType SingleSetIsab), (OtherType SingleSetIsab)], BoolIsab)"

definition congruenceSingleSetBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"congruenceSingleSetBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleSetIsab), [IVarOne, IVarTwo],
    CaseList (VarTerm (OtherType SingleSetIsab) IVarOne)
      [(Term (OtherType SingleSetIsab) KAsSet [VarTerm (IsabList (OtherType SingleKIsab)) newVar],
             CaseList (VarTerm (OtherType SingleSetIsab) IVarTwo)
      [(Term (OtherType SingleSetIsab) KAsSet [VarTerm (IsabList (OtherType SingleKIsab)) newVara],
        AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)))
       [VarTerm (IsabList (OtherType SingleKIsab)) newVar,
     VarTerm (IsabList (OtherType SingleKIsab)) newVara]), (CaseOwise, IsabFalse)]),
     (CaseOwise, CaseList (VarTerm (OtherType SingleSetIsab) IVarTwo)
      [(Term (OtherType SingleSetIsab) KAsSet [VarTerm (IsabList (OtherType SingleKIsab)) newVara],
    IsabFalse), (CaseOwise, IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType KLabelIsab))
      [(AppFun (BuiltInFunConstr GetKLabelFun
    (OtherType SingleSetIsab)) [VarTerm (OtherType SingleSetIsab) IVarOne]),
         (AppFun (BuiltInFunConstr GetKLabelFun (OtherType SingleSetIsab))
     [VarTerm (OtherType SingleSetIsab) IVarTwo])])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)))
          [(AppFun (BuiltInFunConstr GetKListFun (OtherType SingleSetIsab))
              [VarTerm (OtherType SingleSetIsab) IVarOne]),
   (AppFun (BuiltInFunConstr GetKListFun (OtherType SingleSetIsab))
          [VarTerm (OtherType SingleSetIsab) IVarTwo])]))])])))"

definition kMembershipInMapHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
           * 'tVar kType isabType list * 'tVar kType isabType)" where
"kMembershipInMapHeader = (BuiltInFunConstr KMembership (OtherType SingleMapIsab),
   [(OtherType SingleMapIsab), IsabList (OtherType SingleMapIsab)], BoolIsab)"

definition kMembershipInMapBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
          * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"kMembershipInMapBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr KMembership (OtherType SingleMapIsab), [IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo) [(IsabEmptyList, IsabFalse),
     (IsabListCon (VarTerm (OtherType SingleMapIsab) newVar)
       (VarTerm (IsabList (OtherType SingleMapIsab)) newVara),
       IsabOr (AppFun (BuiltInFunConstr Congruence (OtherType SingleMapIsab))
        [(VarTerm (OtherType SingleMapIsab) IVarOne), (VarTerm (OtherType SingleMapIsab) newVar)])
        (AppFun (BuiltInFunConstr KMembership (IsabList (OtherType SingleMapIsab)))
        [(VarTerm (OtherType SingleMapIsab) IVarOne),
              (VarTerm (IsabList (OtherType SingleMapIsab)) newVara)]))])))"

definition kSubsetInMapHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"kSubsetInMapHeader = (BuiltInFunConstr KSubset (IsabList (OtherType SingleMapIsab)),
   [IsabList (OtherType SingleMapIsab), IsabList (OtherType SingleMapIsab)], BoolIsab)"

definition kSubsetInMapBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"kSubsetInMapBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr KSubset (IsabList (OtherType SingleMapIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleMapIsab)) IVarOne) [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleMapIsab) newVar)
        (VarTerm (IsabList (OtherType SingleMapIsab)) newVara),
       IsabAnd (AppFun (BuiltInFunConstr KMembership (OtherType SingleMapIsab))
        [(VarTerm (OtherType SingleMapIsab) newVar),
         (VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo)])
        (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleMapIsab)))
        [(VarTerm (IsabList (OtherType SingleMapIsab)) newVara),
              (VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo)]))])))"

definition congruenceMapHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceMapHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleMapIsab)),
   [IsabList (OtherType SingleMapIsab), IsabList (OtherType SingleMapIsab)], BoolIsab)"

definition congruenceMapBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"congruenceMapBodies = 
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleMapIsab)),[IVarOne, IVarTwo],
    IsabAnd (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleMapIsab)))
       [VarTerm (IsabList (OtherType SingleMapIsab)) IVarOne,
       VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo])
    (AppFun (BuiltInFunConstr KSubset (IsabList (OtherType SingleMapIsab)))
       [VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo,
    VarTerm (IsabList (OtherType SingleMapIsab)) IVarOne]))"

definition congruenceSingleMapHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleMapHeaders = (BuiltInFunConstr Congruence (OtherType SingleMapIsab),
   [(OtherType SingleMapIsab), (OtherType SingleMapIsab)], BoolIsab)"

definition congruenceSingleMapBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"congruenceSingleMapBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleMapIsab), [IVarOne, IVarTwo],
    CaseList (VarTerm (OtherType SingleMapIsab) IVarOne)
      [(Term (OtherType SingleMapIsab) KAsMap [VarTerm (IsabList (OtherType SingleKIsab)) newVar,
     VarTerm (IsabList (OtherType SingleKIsab)) newVara],
             CaseList (VarTerm (OtherType SingleMapIsab) IVarTwo)
      [(Term (OtherType SingleMapIsab) KAsMap [VarTerm (IsabList (OtherType SingleKIsab)) newVarb,
       VarTerm (IsabList (OtherType SingleKIsab)) newVarc],
        IsabAnd (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)))
       [VarTerm (IsabList (OtherType SingleKIsab)) newVar,
        VarTerm (IsabList (OtherType SingleKIsab)) newVarb])
       (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKIsab)))
       [VarTerm (IsabList (OtherType SingleKIsab)) newVara,
     VarTerm (IsabList (OtherType SingleKIsab)) newVarc])), (CaseOwise, IsabFalse)]),
     (CaseOwise, CaseList (VarTerm (OtherType SingleMapIsab) IVarTwo)
      [(Term (OtherType SingleMapIsab) KAsMap [VarTerm (IsabList (OtherType SingleKIsab)) newVara,
           VarTerm (IsabList (OtherType SingleKIsab)) newVarb], IsabFalse),
     (CaseOwise, IsabAnd (AppFun (BuiltInFunConstr Congruence (OtherType KLabelIsab))
      [(AppFun (BuiltInFunConstr GetKLabelFun
    (OtherType SingleMapIsab)) [VarTerm (OtherType SingleMapIsab) IVarOne]),
         (AppFun (BuiltInFunConstr GetKLabelFun (OtherType SingleMapIsab))
     [VarTerm (OtherType SingleMapIsab) IVarTwo])])
      (AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleKListIsab)))
          [(AppFun (BuiltInFunConstr GetKListFun (OtherType SingleMapIsab))
              [VarTerm (OtherType SingleMapIsab) IVarOne]),
        (AppFun (BuiltInFunConstr GetKListFun (OtherType SingleMapIsab))
      [VarTerm (OtherType SingleMapIsab) IVarTwo])]))])])))))"

definition congruenceCellTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceCellTypeHeaders = (BuiltInFunConstr Congruence (OtherType CellType),
   [(OtherType CellType), (OtherType CellType)], BoolIsab)"

definition congruenceCellTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm)" where
"congruenceCellTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar,newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar,newVara,newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType CellType), [IVarOne, IVarTwo],
   CaseList (VarTerm (OtherType CellType) IVarOne) [(Term (OtherType CellType) Cell
      [VarTerm (OtherType CellNameType) newVar, VarTerm (OtherType CellConType) newVara],
   CaseList (VarTerm (OtherType CellType) IVarTwo)
     [(Term (OtherType CellType) Cell
       [VarTerm (OtherType CellNameType) newVarb, VarTerm (OtherType CellConType) newVarc],
   IsabAnd (IsabEqual (VarTerm (OtherType CellNameType) newVar)
      (VarTerm (OtherType CellNameType) newVarb))
        (AppFun (BuiltInFunConstr Congruence (OtherType CellConType))
          [VarTerm (OtherType CellConType) newVara,
       VarTerm (OtherType CellConType) newVarc]))])])))))"

definition kMembershipInCellHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
            * 'tVar kType isabType list * 'tVar kType isabType)" where
"kMembershipInCellHeader = (BuiltInFunConstr KMembership (OtherType CellType),
   [(OtherType CellType), IsabList (OtherType CellType)],
   IsabOption (IsabList (OtherType CellType)))"

definition kMembershipInCellBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"kMembershipInCellBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara,newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr KMembership (OtherType CellType), [IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType CellType)) IVarTwo) [(IsabEmptyList, IsabNone),
     (IsabListCon (VarTerm (OtherType CellType) newVar)
         (VarTerm (IsabList (OtherType CellType)) newVara),
      CaseList (AppFun (BuiltInFunConstr Congruence (OtherType CellType))
               [VarTerm (OtherType CellType) IVarOne,
  VarTerm (OtherType CellType) newVar]) [(IsabTrue,
                   IsabSome (VarTerm (IsabList (OtherType CellType)) newVara)),
    (IsabFalse, CaseList (AppFun (BuiltInFunConstr KMembership (OtherType CellType))
     [VarTerm (OtherType CellType) IVarOne,
        (VarTerm (IsabList (OtherType CellType)) newVara)]) [(IsabNone, IsabNone),
      (IsabSome (VarTerm (IsabList (OtherType CellType)) newVarc),
     IsabSome (IsabListCon (VarTerm (OtherType CellType) newVar)
        (VarTerm (IsabList (OtherType CellType)) newVarc)))])])])))))"

definition congruenceCellConListTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceCellConListTypeHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType CellConType)),
   [(IsabList (OtherType CellConType)), (IsabList (OtherType CellConType))], BoolIsab)"

definition congruenceCellConListTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm)" where
"congruenceCellConListTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar,newVara] of newVarb \<Rightarrow>
  (BuiltInFunConstr Congruence (IsabList (OtherType CellConType)), [IVarOne, IVarTwo],
   CaseList (VarTerm (IsabList (OtherType CellConType)) IVarOne) [(IsabEmptyList,
   CaseList (VarTerm (IsabList (OtherType CellConType)) IVarTwo) [(IsabEmptyList, IsabTrue),
    (CaseOwise, IsabFalse)]), (IsabListCon (VarTerm (OtherType CellConType) newVar)
    (VarTerm (IsabList (OtherType CellConType)) newVara),
    CaseList (AppFun (BuiltInFunConstr KMembership (OtherType CellConType))
     [(VarTerm (OtherType CellConType) newVar),
       VarTerm (IsabList (OtherType CellConType)) IVarTwo]) [(IsabNone, IsabFalse),
   (IsabSome (VarTerm (IsabList (OtherType CellConType)) newVarb), AppFun (BuiltInFunConstr Congruence
      (IsabList (OtherType CellConType))) [(VarTerm (IsabList (OtherType CellConType)) newVara),
     (VarTerm (IsabList (OtherType CellConType)) newVarb)])])]))))"

definition congruenceSingleBagTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceSingleBagTypeHeaders = (BuiltInFunConstr Congruence (OtherType SingleBagIsab),
   [(OtherType SingleBagIsab), (OtherType SingleBagIsab)], BoolIsab)"

definition congruenceSingleBagTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
         * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm)" where
"congruenceSingleBagTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr Congruence (OtherType SingleBagIsab), [IVarOne, IVarTwo],
   CaseList (VarTerm (OtherType SingleBagIsab) IVarOne) [(Term (OtherType SingleBagIsab)
     SingleCellAsBag [VarTerm (OtherType CellType) newVar],
            CaseList (VarTerm (OtherType CellType) IVarTwo)
   [(Term (OtherType SingleBagIsab)  SingleCellAsBag [VarTerm (OtherType CellType) newVara],
     (AppFun (BuiltInFunConstr Congruence (OtherType CellType))
       [VarTerm (OtherType CellType) newVar, VarTerm (OtherType CellType) newVara])),
      (CaseOwise, IsabFalse)]), (Term (OtherType SingleBagIsab) OptionCellAsBag [IsabNone],
       CaseList (VarTerm (OtherType CellType) IVarTwo) [(Term (OtherType SingleBagIsab)
       OptionCellAsBag [IsabNone], IsabTrue), (CaseOwise, IsabFalse)]),
 (Term (OtherType SingleBagIsab) OptionCellAsBag [IsabSome (VarTerm (OtherType CellType) newVar)],
  CaseList (VarTerm (OtherType CellType) IVarTwo) [(Term (OtherType SingleBagIsab) OptionCellAsBag
      [IsabSome (VarTerm (OtherType CellType) newVara)], (AppFun (BuiltInFunConstr Congruence
      (OtherType CellType)) [VarTerm (OtherType CellType) newVar,
         VarTerm (OtherType CellType) newVara])), (CaseOwise, IsabFalse)]),
   (Term (OtherType SingleBagIsab) StarCellAsBag
            [(VarTerm (IsabList (OtherType CellNameType)) newVar),
    (VarTerm (IsabList (OtherType CellConType)) newVara)],
    CaseList (VarTerm (OtherType CellType) IVarTwo) [(Term (OtherType SingleBagIsab) StarCellAsBag
       [(VarTerm (IsabList (OtherType CellNameType)) newVarb),
     (VarTerm (IsabList (OtherType CellConType)) newVarc)], IsabAnd 
     (IsabEqual (VarTerm (IsabList (OtherType CellNameType)) newVar)
       (VarTerm (IsabList (OtherType CellNameType)) newVarb)) (AppFun (BuiltInFunConstr Congruence
      (IsabList (OtherType CellConType))) [VarTerm (IsabList (OtherType CellConType)) newVar,
         VarTerm (IsabList (OtherType CellConType)) newVarc])), (CaseOwise, IsabFalse)])])))))"

definition kMembershipInBagHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
            * 'tVar kType isabType list * 'tVar kType isabType)" where
"kMembershipInBagHeader = (BuiltInFunConstr KMembership (OtherType SingleBagIsab),
   [(OtherType SingleBagIsab), IsabList (OtherType SingleBagIsab)],
   IsabOption (IsabList (OtherType SingleBagIsab)))"

definition kMembershipInBagBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"kMembershipInBagBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara,newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr KMembership (OtherType SingleBagIsab), [IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo) [(IsabEmptyList, IsabNone),
     (IsabListCon (VarTerm (OtherType SingleBagIsab) newVar)
         (VarTerm (IsabList (OtherType SingleBagIsab)) newVara),
      CaseList (AppFun (BuiltInFunConstr Congruence (OtherType SingleBagIsab))
               [VarTerm (OtherType SingleBagIsab) IVarOne,
  VarTerm (OtherType SingleBagIsab) newVar]) [(IsabTrue,
                   IsabSome (VarTerm (IsabList (OtherType SingleBagIsab)) newVara)),
    (IsabFalse, CaseList (AppFun (BuiltInFunConstr KMembership (OtherType SingleBagIsab))
     [VarTerm (OtherType SingleBagIsab) IVarOne,
        (VarTerm (IsabList (OtherType SingleBagIsab)) newVara)]) [(IsabNone, IsabNone),
      (IsabSome (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc),
     IsabSome (IsabListCon (VarTerm (OtherType SingleBagIsab) newVar)
        (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc)))])])])))))"

definition congruenceBagHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
          * 'tVar kType isabType list * 'tVar kType isabType)" where
"congruenceBagHeaders = (BuiltInFunConstr Congruence (IsabList (OtherType SingleBagIsab)),
   [IsabList (OtherType SingleBagIsab), IsabList (OtherType SingleBagIsab)], BoolIsab)"

definition congruenceBagBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm)" where
"congruenceBagBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (BuiltInFunConstr Congruence (IsabList (OtherType SingleBagIsab)),[IVarOne, IVarTwo],
    CaseList (VarTerm (IsabList (OtherType SingleBagIsab)) IVarOne)
     [(IsabEmptyList, CaseList (VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo)
     [(IsabEmptyList, IsabTrue), (CaseOwise, IsabFalse)]),
    (IsabListCon (VarTerm (OtherType SingleBagIsab) newVar)
            (VarTerm (IsabList (OtherType SingleBagIsab)) newVara),
        CaseList (AppFun (BuiltInFunConstr KMembership (OtherType SingleBagIsab))
       [(VarTerm (OtherType SingleBagIsab) newVar),
            (VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo)])
   [(IsabNone, IsabFalse), (IsabSome (VarTerm (IsabList (OtherType SingleBagIsab)) newVarb),
          AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleBagIsab)))
      [VarTerm (IsabList (OtherType SingleBagIsab)) newVara,
          VarTerm (IsabList (OtherType SingleBagIsab)) newVarb])])]))))"

(* define family checking normal form functions. Mainly testing if a map satisfying idempotency
    realtion and a bag data type satisfying all names being distinct.*)
primrec isNormalFormHeaders :: "'tVar kType isabType list
        \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
    * 'tVar kType isabType) list" where
"isNormalFormHeaders [] = []"
| "isNormalFormHeaders (t#l) = (if t \<in> {IsabList (OtherType SingleBagIsab),
     OtherType CellConType, (OtherType CellNameType), OtherType CellType, OtherType SingleBagIsab,
     IsabList (OtherType CellConType)} then congruenceHeaders l
       else (BuiltInFunConstr IsNormalForm t, [t], BoolIsab)#congruenceHeaders l)"

definition isNormalFormHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
    * 'tVar kType isabType list * 'tVar kType isabType) list" where
"isNormalFormHeadersDef = (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> isNormalFormHeaders (keys l))"

primrec IsNormalFormPatTypes :: "'tVar kType isabType list \<Rightarrow> 'iVar list
       \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
     * 'iVar list)" where
"IsNormalFormPatTypes [] S = ([], S)"
| "IsNormalFormPatTypes (t#l) S = (case freshIVar S of newVar \<Rightarrow>
   (case (IsNormalFormPatTypes l (newVar#S)) of (l', S') \<Rightarrow>
          ((VarTerm t newVar)#l', S')))"

fun IsNormalFormExpTypes :: "'tVar kType isabType list \<Rightarrow> ('tVar kType isabType,
          ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
   \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"IsNormalFormExpTypes al [] = IsabTrue"
| "IsNormalFormExpTypes [] el = IsabTrue"
| "IsNormalFormExpTypes (t#al) (e#el) = IsabAnd (AppFun
         (BuiltInFunConstr IsNormalForm t) [e]) (IsNormalFormExpTypes al el)"

fun IsNormalFormAux :: "'tVar kType isabType \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
   * 'tVar kType isabType list * isabelleStricts option * bool) list  \<Rightarrow> 'iVar list \<Rightarrow>
      ((('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
          * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar)
       isabTerm) list * 'iVar list)" where
"IsNormalFormAux t [] S = ([], S)"
| "IsNormalFormAux t ((a,c,d)#l) S = (case IsNormalFormPatTypes c S of (terms, S') \<Rightarrow>
     (case IsNormalFormExpTypes c terms of term' \<Rightarrow>
       (case IsNormalFormAux t l S' of (l', Sa) \<Rightarrow>
         ((Term t a terms, term')#l', Sa))))"

primrec IsNormalFormBodies :: "'tVar kType isabType list
           \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
             * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var)
    kConstr, 'iVar) isabTerm) list" where
"IsNormalFormBodies [] = []"
| "IsNormalFormBodies (t#l) = (if t \<in> {IsabList (OtherType SingleKListIsab),
   IsabList (OtherType SingleBagIsab), IsabList (OtherType SingleListIsab),
   IsabList (OtherType SingleSetIsab), IsabList (OtherType SingleMapIsab), OtherType CellConType,
    (OtherType CellNameType), OtherType CellType, OtherType SingleBagIsab,
     IsabList (OtherType CellConType), (OtherType SingleKListIsab)} then
       toKItemFunBodies l else (case lookupUserDataSet t of None \<Rightarrow> IsNormalFormBodies l
       | Some sl \<Rightarrow> (case IsNormalFormAux t sl [IVarOne] of (cl, S') \<Rightarrow>
   (BuiltInFunConstr IsNormalForm t,
       [IVarOne], CaseList (VarTerm t IVarOne) cl))#toKItemFunBodies l))"

definition IsNormalFormBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
             * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var)
    kConstr, 'iVar) isabTerm) list" where
"IsNormalFormBodiesDef = (case userDataTest of None \<Rightarrow> []
      | Some l \<Rightarrow> IsNormalFormBodies (keys l))"

definition IsNormalFormKListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
            * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormKListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleKListIsab)),[IVarOne],
  CaseList (VarTerm (IsabList (OtherType SingleKListIsab)) IVarOne)
    [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleKListIsab) newVar)
      (VarTerm (IsabList (OtherType SingleKListIsab)) newVara),
  IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleKListIsab))
     [VarTerm (OtherType SingleKListIsab) newVar])
     (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleKListIsab)))
     [VarTerm (IsabList (OtherType SingleKListIsab)) newVara]))])))"

definition IsNormalFormSingleKListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
            * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormSingleKListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (OtherType SingleKListIsab),[IVarOne],
  CaseList (VarTerm (OtherType SingleKListIsab) IVarOne)
    [(Term (OtherType SingleKListIsab) CellAsKList [VarTerm (OtherType CellConType) newVar],
      CaseList (AppFun (BuiltInFunConstr IsNormalForm (OtherType CellConType))
          [VarTerm (OtherType CellConType) newVar]) [(IsabNone, IsabFalse),
     (IsabSome (VarTerm (OtherType CellNameType) newVara), IsabTrue)]),
     (Term (OtherType SingleKListIsab) KLabelAsKList [VarTerm (OtherType KLabelIsab) newVar],
      (AppFun (BuiltInFunConstr IsNormalForm (OtherType KLabelIsab))
          [VarTerm (OtherType KLabelIsab) newVar]))])))"

definition IsNormalFormKBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"IsNormalFormKBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleKIsab)),[IVarOne],
  CaseList (VarTerm (IsabList (OtherType SingleKIsab)) IVarOne)
    [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleKIsab) newVar)
        (VarTerm (IsabList (OtherType SingleKIsab)) newVara),
       IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleKIsab))
           [VarTerm (OtherType SingleKIsab) newVar])
        (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleKIsab)))
                   [VarTerm (IsabList (OtherType SingleKIsab)) newVara]))])))"

definition IsNormalFormListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleListIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleListIsab)) IVarOne)
    [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleListIsab) newVar)
       (VarTerm (IsabList (OtherType SingleListIsab)) newVara),
   IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleListIsab))
     [VarTerm (OtherType SingleListIsab) newVar])
        (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleListIsab)))
                   [VarTerm (IsabList (OtherType SingleListIsab)) newVara]))])))"

definition IsNormalFormSetBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm)" where
"IsNormalFormSetBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleSetIsab)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType SingleSetIsab)) IVarOne)
    [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType SingleSetIsab) newVar)
        (VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
  IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleSetIsab))
         [VarTerm (OtherType SingleSetIsab)
       newVar]) (IsabAnd (IsabNot (AppFun (BuiltInFunConstr KMembership (OtherType SingleSetIsab))
        [VarTerm (OtherType SingleSetIsab) newVar,
        VarTerm (IsabList (OtherType SingleSetIsab)) newVara]))
        (AppFun (BuiltInFunConstr IsNormalForm
       (IsabList (OtherType SingleSetIsab)))
          [VarTerm (IsabList (OtherType SingleSetIsab)) newVara])))])))"

definition halfMembershipHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType)" where
"halfMembershipHeader = (HalfMembership,
   [IsabList (OtherType SingleKIsab), IsabList (OtherType SingleMapIsab)], BoolIsab)"

definition halfMembershipBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"halfMembershipBody = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVarb] of newVarc \<Rightarrow>
   (HalfMembership,
   [IVarOne, IVarTwo], CaseList (VarTerm (IsabList (OtherType SingleMapIsab)) IVarTwo)
      [(IsabEmptyList, IsabFalse), (IsabListCon (VarTerm (OtherType SingleSetIsab) newVar)
 (VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
      CaseList (VarTerm (OtherType SingleSetIsab) newVar)
    [(Term (OtherType SingleMapIsab) KAsMap [VarTerm (IsabList (OtherType SingleKIsab)) newVarb,
        VarTerm (IsabList (OtherType SingleKIsab)) newVarc], IsabOr (AppFun (BuiltInFunConstr
        Congruence (IsabList (OtherType SingleKIsab)))
             [VarTerm (IsabList (OtherType SingleKIsab)) IVarOne,
            VarTerm (IsabList (OtherType SingleKIsab)) newVarb]) (AppFun (HalfMembership)
        [VarTerm (IsabList (OtherType SingleKIsab)) IVarOne,
     (VarTerm (IsabList (OtherType SingleSetIsab)) newVara)])),
       (CaseOwise, AppFun HalfMembership [VarTerm (OtherType SingleKIsab) IVarOne,
         VarTerm (IsabList (OtherType SingleSetIsab)) newVara])])])))))"

definition IsNormalFormMapBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm)" where
"IsNormalFormMapBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVara] of newVarb \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar, newVarb] of newVarc \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleMapIsab)),[IVarOne],
    CaseList (VarTerm (IsabList (OtherType SingleMapIsab)) IVarOne)
     [(IsabEmptyList, IsabTrue), (IsabListCon (VarTerm (OtherType SingleMapIsab) newVar)
      (VarTerm (IsabList (OtherType SingleSetIsab)) newVara),
        CaseList (VarTerm (OtherType SingleMapIsab) newVar)
      [(Term (OtherType SingleMapIsab) KAsMap [VarTerm (IsabList (OtherType SingleKIsab)) newVarb, 
          VarTerm (IsabList (OtherType SingleKIsab)) newVarc],
         IsabAnd (AppFun (BuiltInFunConstr IsNormalForm
             (IsabList (OtherType SingleMapIsab)))
        [VarTerm (IsabList (OtherType SingleSetIsab)) newVara])
         (IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleMapIsab))
         [VarTerm (OtherType SingleMapIsab) newVar]) (IsabNot (AppFun (HalfMembership)
   [VarTerm (IsabList (OtherType SingleKIsab)) newVarb,
         VarTerm (IsabList (OtherType SingleSetIsab)) newVara])))),
       (CaseOwise, IsabAnd (AppFun (BuiltInFunConstr IsNormalForm
             (IsabList (OtherType SingleMapIsab)))
       [VarTerm (IsabList (OtherType SingleSetIsab)) newVara])
         (IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleMapIsab))
      [VarTerm (OtherType SingleMapIsab) newVar])
         (IsabNot (AppFun (BuiltInFunConstr KMembership (OtherType SingleMapIsab))
   [VarTerm (OtherType SingleMapIsab) newVar,
      VarTerm (IsabList (OtherType SingleSetIsab)) newVara]))))])])))))"

definition IsNormalFormBagHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'tVar kType isabType list * 'tVar kType isabType)" where
"IsNormalFormBagHeaders = (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleBagIsab)),
   [IsabList (OtherType SingleBagIsab), IsabList (OtherType CellNameType)],
          IsabOption (IsabList (OtherType CellNameType)))"

definition IsNormalFormBagBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormBagBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVara] of newVarb \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleBagIsab)),[IVarOne, IVarTwo],
    CaseList (VarTerm (IsabList (OtherType SingleBagIsab)) IVarOne)
     [(IsabEmptyList, IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)),
    (IsabListCon (VarTerm (OtherType SingleBagIsab) newVar)
      (VarTerm (IsabList (OtherType SingleBagIsab)) newVara),
    CaseList (AppFun (BuiltInFunConstr IsNormalForm (OtherType SingleBagIsab))
     [VarTerm (OtherType SingleBagIsab) newVar,
          (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)]) [(IsabNone, IsabNone),
  (IsabSome (VarTerm (IsabList (OtherType CellNameType)) newVarb),
     (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleBagIsab)))
      [VarTerm (IsabList (OtherType SingleBagIsab)) newVara,
     (VarTerm (IsabList (OtherType CellNameType)) newVarb)]))])]))))"

definition IsNormalFormSingleBagHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"IsNormalFormSingleBagHeaders = (BuiltInFunConstr IsNormalForm (OtherType SingleBagIsab),
   [(OtherType SingleBagIsab), IsabList (OtherType CellNameType)],
    IsabOption (IsabList (OtherType CellNameType)))"

definition IsNormalFormSingleBagBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormSingleBagBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar,newVara] of newVarb \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (OtherType SingleBagIsab), [IVarOne, IVarTwo],
   CaseList (VarTerm (OtherType SingleBagIsab) IVarOne)
    [(Term (OtherType SingleBagIsab) SingleCellAsBag [VarTerm (OtherType CellType) newVara],
      AppFun (BuiltInFunConstr IsNormalForm (OtherType CellType))
    [VarTerm (OtherType CellConType) newVara, VarTerm (IsabList (OtherType CellNameType)) IVarTwo]),
   (Term (OtherType SingleBagIsab) OptionCellAsBag [IsabNone],
      IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)),
   (Term (OtherType SingleBagIsab) OptionCellAsBag [IsabSome (VarTerm (OtherType CellType) newVara)],
      AppFun (BuiltInFunConstr IsNormalForm (OtherType CellType))
   [VarTerm (OtherType CellConType) newVara, VarTerm (IsabList (OtherType CellNameType)) IVarTwo]),
    (Term (OtherType SingleBagIsab) StarCellAsBag
        [VarTerm (OtherType CellNameType) newVara,
           (VarTerm (IsabList (OtherType CellConType)) newVarb)],
     CaseList (AppFun Membership [VarTerm (OtherType CellNameType) newVara,
            (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)]) [(IsabTrue, IsabNone),
    (IsabFalse, AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType CellConType)))
   [VarTerm (IsabList (OtherType CellConType)) newVarb,  (IsabListCon (VarTerm 
  (OtherType CellNameType) newVara) (VarTerm (IsabList (OtherType CellNameType)) IVarTwo))])])]))))"

definition IsNormalFormCellTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"IsNormalFormCellTypeHeaders = (BuiltInFunConstr IsNormalForm (OtherType CellType),
   [(OtherType CellType), IsabList (OtherType CellNameType)],
    IsabOption (IsabList (OtherType CellNameType)))"

definition IsNormalFormCellTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormCellTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (OtherType CellType), [IVarOne, IVarTwo],
      CaseList (VarTerm (OtherType CellType) IVarOne)
    [(Term (OtherType CellType) Cell [VarTerm (OtherType CellNameType) newVar,
    VarTerm (OtherType CellConType) newVara],
      CaseList (AppFun Membership [VarTerm (OtherType CellNameType) newVar,
            (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)]) [(IsabTrue, IsabNone),
    (IsabFalse, AppFun (BuiltInFunConstr IsNormalForm (OtherType CellConType))
   [VarTerm (OtherType CellConType) newVara,  (IsabListCon (VarTerm 
  (OtherType CellNameType) newVar) (VarTerm (IsabList (OtherType CellNameType)) IVarTwo))])])])))"

definition IsNormalFormCellConListHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"IsNormalFormCellConListHeaders = (BuiltInFunConstr IsNormalForm (IsabList (OtherType CellConType)),
   [(IsabList (OtherType CellConType)), IsabList (OtherType CellNameType)],
    IsabOption (IsabList (OtherType CellNameType)))"

definition IsNormalFormCellConListBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormCellConListBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (IsabList (OtherType CellConType)),[IVarOne, IVarTwo],
  CaseList (VarTerm (IsabList (OtherType CellConType)) IVarOne)
    [(IsabEmptyList, IsabTrue),
     (IsabListCon (VarTerm (OtherType CellConType) newVar)
       (VarTerm (IsabList (OtherType CellConType)) newVara),
   IsabAnd (AppFun (BuiltInFunConstr IsNormalForm (OtherType CellConType))
     [VarTerm (OtherType CellConType) newVar])
        (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType CellConType)))
                   [VarTerm (IsabList (OtherType CellConType)) newVara]))])))"

definition IsNormalFormCellConTypeHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * 'tVar kType isabType)" where
"IsNormalFormCellConTypeHeaders = (BuiltInFunConstr IsNormalForm (OtherType CellConType),
   [(OtherType CellConType), IsabList (OtherType CellNameType)],
    IsabOption (IsabList (OtherType CellNameType)))"

definition IsNormalFormCellConTypeBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm)" where
"IsNormalFormCellConTypeBodies = (case freshIVar [IVarOne, IVarTwo] of newVar \<Rightarrow>
  (case freshIVar [IVarOne, IVarTwo, newVar] of newVara \<Rightarrow>
  (BuiltInFunConstr IsNormalForm (OtherType CellConType), [IVarOne, IVarTwo],
      CaseList (VarTerm (OtherType CellConType) IVarOne)
    [(Term (OtherType CellConType) KCellIsab [VarTerm (IsabList (OtherType SingleKIsab)) newVar],
      CaseList (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleKIsab)))
          [VarTerm (IsabList (OtherType SingleKIsab)) newVar]) [(IsabTrue,
    IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)), (IsabFalse, IsabNone)]),
   (Term (OtherType CellConType) ListCellIsab [VarTerm (IsabList (OtherType SingleListIsab)) newVar],
      CaseList (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleListIsab)))
          [VarTerm (IsabList (OtherType SingleListIsab)) newVar]) [(IsabTrue,
    IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)), (IsabFalse, IsabNone)]),
    (Term (OtherType CellConType) SetCellIsab [VarTerm (IsabList (OtherType SingleSetIsab)) newVar],
      CaseList (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleSetIsab)))
          [VarTerm (IsabList (OtherType SingleSetIsab)) newVar]) [(IsabTrue,
    IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)), (IsabFalse, IsabNone)]),
  (Term (OtherType CellConType) MapCellIsab [VarTerm (IsabList (OtherType SingleMapIsab)) newVar],
      CaseList (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleMapIsab)))
          [VarTerm (IsabList (OtherType SingleMapIsab)) newVar]) [(IsabTrue,
    IsabSome (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)), (IsabFalse, IsabNone)]),
  (Term (OtherType CellConType) BagCellIsab [VarTerm (IsabList (OtherType SingleBagIsab)) newVar],
     (AppFun (BuiltInFunConstr IsNormalForm (IsabList (OtherType SingleBagIsab)))
       [VarTerm (IsabList (OtherType SingleBagIsab)) newVar,
            (VarTerm (IsabList (OtherType CellNameType)) IVarTwo)]))])))"

(* cast fun and unify fun *)
definition toIVarList :: "'metaVar metaVar list \<Rightarrow> 'iVar list" where
"toIVarList l = map (\<lambda> x . translateVar x) l"

definition toTyList :: "'upVar list \<Rightarrow> 'tVar kType isabType list" where
"toTyList l = map (\<lambda> x . translateRightType x) l"

primrec castFunHeadersAux :: "'upVar \<Rightarrow> 'upVar list
     \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
     * 'tVar kType isabType) list" where
"castFunHeadersAux a [] = []"
| "castFunHeadersAux a (x#l) = (if a = x then (castFunHeadersAux a l)
    else (CastFun (translateRightType a) (translateRightType x),
          [translateRightType a], IsabOption (translateRightType x))#(castFunHeadersAux a l))"

fun castFunHeadersFun :: "'upVar list \<Rightarrow> 'upVar list
                \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
     * 'tVar kType isabType) list" where
"castFunHeadersFun [] S = []"
| "castFunHeadersFun (x#l) S = (castFunHeadersAux x S)@castFunHeadersFun l S"

definition castFunHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType) list" where
"castFunHeaders = castFunHeadersFun allSubsortableSorts allSubsortableSorts"

primrec formCastTermPairFun :: "'upVar \<Rightarrow> 'upVar \<Rightarrow> 'upVar list
  \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
      * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list"
 where
"formCastTermPairFun a b [] = [(VarTerm (translateRightType a) IVarOne,
   (if a = b then IsabSome (VarTerm (translateRightType a) IVarOne)
    else if subsort a b subsortGraph then
    IsabSome (AppFun (UnifyFun (translateRightType b) (translateRightType a))
            [VarTerm (translateRightType a) IVarOne]) else IsabNone))]"
| "formCastTermPairFun a b (x#l) = (Term (translateRightType a) (SubsortConstr
   (translateRightType a) (translateRightType x)) [VarTerm (translateRightType x) IVarOne],
    if b = x then IsabSome (VarTerm (translateRightType x) IVarOne)
    else (AppFun (CastFun (translateRightType x) (translateRightType b))
         [(VarTerm (translateRightType x) IVarOne)]))
     #formCastTermPairFun a b l"

primrec formCastTermAux :: "'upVar \<Rightarrow> 'upVar list
     \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType
    isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"formCastTermAux a [] = []"
| "formCastTermAux a (x#l) = (if a = x then formCastTermAux a l
    else (case lookup a subsortGraph of None \<Rightarrow>
    (CastFun (translateRightType a) (translateRightType x), [IVarOne], CaseList
     (VarTerm (translateRightType a) IVarOne) (formCastTermPairFun a x []))#formCastTermAux a l
  | Some tyl \<Rightarrow> (CastFun (translateRightType a) (translateRightType x),
          [IVarOne], CaseList (VarTerm (translateRightType a) IVarOne)
      (formCastTermPairFun a x tyl))#formCastTermAux a l))"

primrec formCastTerm :: "'upVar list \<Rightarrow> 'upVar list
     \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType
    isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"formCastTerm [] S = []"
| "formCastTerm (x#l) S = (formCastTermAux x S)@(formCastTerm l S)"

definition formCastBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list *
 ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"formCastBodies = formCastTerm allSubsortableSorts allSubsortableSorts"

primrec formCastKHeaderFun :: "'upVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType) list" where
"formCastKHeaderFun [] = []"
| "formCastKHeaderFun (x#l) = (CastFun (translateRightType K) (translateRightType x),
          [(translateRightType K)], IsabOption (translateRightType x))#formCastKHeaderFun l"

definition formCastKHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType) list" where
"formCastKHeaders = formCastKHeaderFun allSubsortableSorts"

primrec formCastKBodiesFun :: "'upVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
   * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
    'var) kConstr, 'iVar) isabTerm) list" where
"formCastKBodiesFun [] = []"
| "formCastKBodiesFun (x#l) = (CastFun (translateRightType K) (translateRightType x),
   [IVarOne], CaseList (VarTerm (translateRightType K) IVarOne)
   [(IsabListCon (Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab) IVarTwo])
     IsabEmptyList, AppFun (CastFun (OtherType KItemIsab) (translateRightType x))
       [VarTerm (OtherType KItemIsab) IVarTwo]),
    (VarTerm (translateRightType K) IVarTwo, IsabNone)])#formCastKBodiesFun l"

definition formCastKBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
   * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
    'var) kConstr, 'iVar) isabTerm) list" where
"formCastKBodies = formCastKBodiesFun allSubsortableSorts"

(* giving two terms A B, where A < B, gnereating sort B term from a sort A term by inserting Constrs*)

primrec unifyFunHeadersAux :: "'upVar \<Rightarrow> 'upVar list
     \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
     * 'tVar kType isabType) list" where
"unifyFunHeadersAux a [] = []"
| "unifyFunHeadersAux a (x#l) = (UnifyFun (translateRightType a) (translateRightType x),
          [translateRightType x], (translateRightType a))#unifyFunHeadersAux a l"

fun unifyFunHeadersFun :: "('upVar * 'upVar list) list
                \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
     * 'tVar kType isabType) list" where
"unifyFunHeadersFun [] = []"
| "unifyFunHeadersFun ((x,y)#l) = (if x \<noteq> K then 
        (unifyFunHeadersAux x y)@unifyFunHeadersFun l
    else unifyFunHeadersFun l)"

definition unifyFunHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
     * 'tVar kType isabType list * 'tVar kType isabType) list" where
"unifyFunHeaders = unifyFunHeadersFun subsortTransCl"

function formTermWithTypeFun :: "'tVar kType isabType \<Rightarrow> 'tVar kType isabType \<Rightarrow>
   (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
         *  isabelleStricts option * bool) list \<Rightarrow>
 ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list *
     isabelleStricts option * bool) list) list \<Rightarrow> 'tVar kType isabType list
    \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
  \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm option" where
"formTermWithTypeFun a b [] G acc T = None"
| "formTermWithTypeFun a b (x#l) G acc T = (if a = b then Some T
     else (case x of (u,[ty],w) \<Rightarrow> if ty \<in> set acc
   then formTermWithTypeFun a b l G acc T else (case lookup ty G of None \<Rightarrow> None
       | Some newl \<Rightarrow> (case formTermWithTypeFun ty b newl G (ty#acc) T of
     None \<Rightarrow> None | Some T' \<Rightarrow>
      Some (Term a (SubsortConstr a ty) [T'])))))"
by pat_completeness auto

(* A > B term B*)
definition formTermWithType :: "'tVar kType isabType \<Rightarrow> 'tVar kType isabType \<Rightarrow>
      ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
                 \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm option" where
"formTermWithType a b T = (case lookup a isabSubsortGraph of None \<Rightarrow> None
         | Some l \<Rightarrow> formTermWithTypeFun a b l isabSubsortGraph [a] T)"

definition unifyFunBodiesFunAux :: "'tVar kType isabType \<Rightarrow> 'tVar kType isabType list
                \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list  * ('tVar kType
    isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list option" where
"unifyFunBodiesFunAux x l = (foldl (\<lambda> acc y . (case acc of None \<Rightarrow> None
     | Some l' \<Rightarrow> (case formTermWithType x y (VarTerm y IVarOne) of None 
         \<Rightarrow> None | Some t' \<Rightarrow> Some (l'@[(UnifyFun x y, [IVarOne], t')])))) (Some []) l)"

definition unifyFunBodiesFun :: "('upVar * 'upVar list) list
                \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list * ('tVar kType
    isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list option" where
"unifyFunBodiesFun l = foldl (\<lambda> acc (x,y). if x = K then acc else
     (case acc of None \<Rightarrow> None | Some la \<Rightarrow>
       (case (unifyFunBodiesFunAux (translateRightType x) (translateTypes y)) of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some (la@l')))) (Some []) l"

definition unifyFunBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
   * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
   'iVar) isabTerm) list" where
"unifyFunBodiesDef = (case unifyFunBodiesFun subsortGraph of None \<Rightarrow> []
                  | Some l \<Rightarrow> l)"

definition unifyFunKHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"unifyFunKHeader = (UnifyFun (IsabList (OtherType SingleKIsab)) (OtherType KItemIsab),
          [(OtherType KItemIsab)], (IsabList (OtherType SingleKIsab)))"

definition unifyFunKBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list
   * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"unifyFunKBody = (UnifyFun (IsabList (OtherType SingleKIsab)) (OtherType KItemIsab), [IVarOne],
        IsabListCon (Term (OtherType SingleKIsab) KItemAsK [VarTerm (OtherType KItemIsab)
     IVarOne]) IsabEmptyList)"

primrec formKListTermByTerms :: "('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
   \<Rightarrow> ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
    \<Rightarrow> ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm option" where
"formKListTermByTerms [] t = Some t"
| "formKListTermByTerms (a#l) t = (case a of (VarTerm ty x) \<Rightarrow> 
     (case formKListTermByTerms l t of None \<Rightarrow> None
        | Some l' \<Rightarrow> 
         Some (IsabListCon (AppFun (BuiltInFunConstr ToKItemFun (OtherType SingleKListIsab))
                      [AppFun (UnifyFun ty (OtherType KItemIsab)) [a]]) l'))
    | _ \<Rightarrow> None)"

primrec formTermListByTypes :: "'upVar list \<Rightarrow> 'iVar list
    \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm list * 'iVar list)" where
"formTermListByTypes [] S= ([],S)"
| "formTermListByTypes (t#tyl) S = (case freshIVar S of newVar \<Rightarrow>
    (case formTermListByTypes tyl (newVar#S) of (terml, S') \<Rightarrow>
             ((VarTerm (translateRightType t) newVar)#terml, S')))"

fun typeCheckTermsByTypes :: "'upVar list \<Rightarrow> ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list \<Rightarrow> bool" where
"typeCheckTermsByTypes [] [] = True"
| "typeCheckTermsByTypes (ty#tyl) (t#l) = (case t of (VarTerm ty' x) \<Rightarrow>
        if (translateRightType ty) = ty' then typeCheckTermsByTypes tyl l else False
     | _ \<Rightarrow> False)"
| "typeCheckTermsByTypes A B = False"

fun typeCheckSUTermsByTypes :: "'upVar list \<Rightarrow> ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list \<Rightarrow> 'upVar list option" where
"typeCheckSUTermsByTypes T [] = Some T"
| "typeCheckSUTermsByTypes [] S = None"
| "typeCheckSUTermsByTypes (ty#tyl) (t#l) = (case t of (VarTerm ty' x) \<Rightarrow>
      if (translateRightType ty) = ty' then typeCheckSUTermsByTypes tyl l else None
     | _ \<Rightarrow> None)"

primrec transToTermInIRKLabel :: "('svar, 'metaVar metaVar) irKLabel
   \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"transToTermInIRKLabel (IRKLabel s) = Term (OtherType KLabelIsab) (UserConstr (translateLabel s)) []"
| "transToTermInIRKLabel (IRIdKLabel x) = VarTerm (OtherType KLabelIsab) (translateVar x)"

function transToTermInIRType :: "('upVar, 'var, 'svar, 'metaVar metaVar) irKItem
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRKItem :: "('upVar, 'var, 'svar, 'metaVar metaVar) irKItem
    \<Rightarrow> 'iVar list  \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
       'var) kConstr, 'iVar) isabTerm list) list
        \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
      'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
  ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInNoneIRKList :: "('upVar, 'var, 'svar, 'metaVar metaVar) irKList
     \<Rightarrow> 'iVar list  \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
         'var) kConstr, 'iVar) isabTerm list) list
          \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
  ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRKList :: "('upVar, 'var, 'svar, 'metaVar metaVar) irKList
    \<Rightarrow> 'upVar list \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
               \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
     'iVar) isabTerm list * 'iVar list * ('iVar * ('tVar kType isabType,
      ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRLeftKList :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBigKWithLabel list
    \<Rightarrow> 'upVar list \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
      'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
               \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
          'iVar) isabTerm list * 'upVar list * 
                                 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRK :: "('upVar, 'var, 'svar, 'metaVar metaVar) irK 
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
      'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
                \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
     ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInNoneIRK :: "('upVar, 'var, 'svar, 'metaVar metaVar) irK 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
         'var) kConstr, 'iVar) isabTerm list) list
         \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
      ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRList :: "('upVar, 'var, 'svar, 'metaVar metaVar) irList 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
         'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
     ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRSet :: "('upVar, 'var, 'svar, 'metaVar metaVar) irSet 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
          'var) kConstr, 'iVar) isabTerm list) list
        \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
      ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRMap :: "('upVar, 'var, 'svar, 'metaVar metaVar) irMap 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
         'var) kConstr, 'iVar) isabTerm list) list
           \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRBigKWithBag :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBigKWithBag 
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
          'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInNoneIRBigKWithBag :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBigKWithBag 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType,
     ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
          'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInNoneIRBigKWithLabel :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBigKWithLabel
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
        'var) kConstr, 'iVar) isabTerm list) list
               \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
          'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
     ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRBigKWithLabel :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBigKWithLabel
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
         \<Rightarrow>  (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option"
    and transToTermInIRBag :: "('upVar, 'var, 'svar, 'metaVar metaVar) irBag 
    \<Rightarrow> 'iVar list  \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType,
      'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
             (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
       'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
    ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option" where
"transToTermInIRType (IRKItem l r ty) t S M = (case getIRKLabel l of None \<Rightarrow>
   (case ((transToTermInIRKLabel l),(transToTermInNoneIRKList r S M)) of
    (l', Some (r', S', M')) \<Rightarrow> if t = ty then
         Some ((Term (translateRightType t) (LabelFormConstr (translateRightType t))
             (l'#r'#[])), S', M')
       else if subsort t ty subsortGraph then
        Some (Term (translateRightType t) (CastConstr (translateRightType ty) (translateRightType t))
       [Term (translateRightType ty) (LabelFormConstr (translateRightType ty))
             (l'#r'#[])], S', M')
      else if subsort ty t subsortGraph then Some
           (Term (translateRightType t) (CastConstr (translateRightType ty) (translateRightType t))
     [Term (translateRightType ty) (LabelFormConstr (translateRightType ty))
            (l'#r'#[])], S', M') else None
      | _ \<Rightarrow> None)
   | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None
   | Some ty' \<Rightarrow> (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case (transToTermInIRKList r tyl S M) of
      None \<Rightarrow> None | Some (r', S', M') \<Rightarrow>
      if ty' = t then Some ( Term (translateRightType ty')
           (UserConstr (translateLabel s)) r', S', M')
      else if subsort ty' t subsortGraph then Some (Term (translateRightType t)
            (CastConstr (translateRightType ty') (translateRightType t))
        [Term (translateRightType ty') (UserConstr (translateLabel s)) r'], S', M')
      else None))))"
| "transToTermInIRType (IRIdKItem a b) t S M = (if t = b then
          Some (VarTerm (translateRightType t) (translateVar a), S, M)
  else if subsort t b subsortGraph then 
     Some (Term (translateRightType t) (CastConstr (translateRightType b) (translateRightType t))
                     [VarTerm (translateRightType b) (translateVar a)], S, M)
         else if subsort b t subsortGraph then
          Some (Term (translateRightType t) (CastConstr (translateRightType b)
             (translateRightType t)) [VarTerm (translateRightType b) (translateVar a)], S, M)
         else None)"
| "transToTermInIRType (IRHOLE a) t S M = (if t = a then
     Some (Term (translateRightType t)
                                (HoleConstr (translateRightType t)) [], S, M)
   else if subsort t a subsortGraph then
      Some (Term (translateRightType t) (CastConstr (translateRightType a) (translateRightType t))
        [Term (translateRightType a) (HoleConstr (translateRightType a)) []], S, M)
        else if subsort a t subsortGraph then
            Some (Term (translateRightType t) (CastConstr (translateRightType a) (translateRightType t))
        [Term (translateRightType a) (HoleConstr (translateRightType a)) []], S, M) else None)"
| "transToTermInIRKItem (IRKItem l r ty) S M = (case getIRKLabel l of None \<Rightarrow>
   (case ((transToTermInIRKLabel l),(transToTermInNoneIRKList r S M)) of
    (l', Some (r', S', M')) \<Rightarrow> if ty = KItem then
           Some (Term (translateRightType ty)
            (LabelFormConstr (translateRightType ty)) (l'#r'#[]), S', M')
     else if subsort ty KItem subsortGraph then
          Some (Term (OtherType KItemIsab) (CastConstr (translateRightType ty) (OtherType KItemIsab))
      [Term (translateRightType ty) (LabelFormConstr (translateRightType ty)) (l'#r'#[])], S', M')
         else if ty = K then Some (Term (OtherType KItemIsab) (CastConstr (translateRightType K)
              (OtherType KItemIsab)) [Term (OtherType KItemIsab)
                (LabelFormConstr (OtherType KItemIsab)) (l'#r'#[])], S, M)
       else None | _ \<Rightarrow> None)
   | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None
   | Some ty' \<Rightarrow> (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case (transToTermInIRKList r tyl S M) of
      None \<Rightarrow> None | Some (r', S', M') \<Rightarrow>
       if ty' = KItem then Some (Term (translateRightType ty')
     (UserConstr (translateLabel s)) r', S', M')
      else if subsort ty' KItem subsortGraph then
      Some (Term (OtherType KItemIsab) (CastConstr (translateRightType ty') (OtherType KItemIsab))
         [Term (translateRightType ty') (UserConstr (translateLabel s)) r'], S', M') else None))))"
| "transToTermInIRKItem (IRIdKItem a b) S M = (if b = KItem then
      Some (VarTerm (OtherType KItemIsab) (translateVar a), S, M)
       else if subsort b KItem subsortGraph then
        Some (Term (OtherType KItemIsab) (CastConstr (translateRightType b) (OtherType KItemIsab) )
          [VarTerm (translateRightType b) (translateVar a)], S, M)
        else if b = K then Some (Term (OtherType KItemIsab) (CastConstr (translateRightType K)
      (OtherType KItemIsab)) [VarTerm (OtherType KItemIsab) (translateVar a)], S, M) else None)"
| "transToTermInIRKItem (IRHOLE a) S M = (if a = KItem then Some (Term (OtherType KItemIsab)
         (HoleConstr (OtherType KItemIsab)) [], S, M)
          else if subsort a KItem subsortGraph then
             Some (Term (OtherType KItemIsab) (CastConstr (translateRightType a) (OtherType KItemIsab))
           [Term (translateRightType a) (HoleConstr (translateRightType a)) []], S, M)
            else None)"
| "transToTermInNoneIRKList (KListPat ll x rl) S M = (case ll of [] \<Rightarrow>
        (case x of None \<Rightarrow> (case rl of [] \<Rightarrow>
               Some (IsabEmptyList, S, M)
          | (ra#rl') \<Rightarrow> (case transToTermInNoneIRKList (KListPat [] None rl') S M
          of None \<Rightarrow> None | Some (rla, S', M') \<Rightarrow>
           (case transToTermInNoneIRBigKWithLabel ra S' M' of None \<Rightarrow> None
               | Some (ra', Sa, Ma) \<Rightarrow> Some (IsabListCon ra' rla, Sa, Ma))))
       | Some var \<Rightarrow> (case lookup (translateVar var) M of None \<Rightarrow>
            (case transToTermInNoneIRKList (KListPat [] None rl) S M
          of None \<Rightarrow> None | Some (rl', S', M') \<Rightarrow>
           Some (IsabListAt (VarTerm (IsabList (OtherType SingleKListIsab))
                         (translateVar var)) rl', S', M'))
        | Some terml \<Rightarrow> (case transToTermInNoneIRKList (KListPat [] None rl) S M
          of None \<Rightarrow> None | Some (rl', S', M') \<Rightarrow>
       (case formKListTermByTerms terml rl' of None \<Rightarrow> None
           | Some rlTerm \<Rightarrow> Some (rlTerm, S', M')))))
         | (la#ll') \<Rightarrow> (case transToTermInNoneIRKList (KListPat ll' x rl) S M
          of None \<Rightarrow> None | Some (lla, S', M') \<Rightarrow>
           (case transToTermInNoneIRBigKWithLabel la S' M' of None \<Rightarrow> None
               | Some (la', Sa, Ma) \<Rightarrow> Some (IsabListCon la' lla, Sa, Ma))))"
| "transToTermInIRLeftKList [] T S M = (case T of [] \<Rightarrow> Some ([], T, S, M)
              | _ \<Rightarrow> None)"
| "transToTermInIRLeftKList (a#l) T S M = (case T of [] \<Rightarrow> None
        | (ty#tyl) \<Rightarrow> (case transToTermInIRBigKWithLabel a ty S M of
        None \<Rightarrow> None | Some (a',S',M') \<Rightarrow>
       (case transToTermInIRLeftKList l tyl S M of None \<Rightarrow> None
          | Some (l', Ta, Sa, Ma) \<Rightarrow> Some (a'#l', Ta, Sa, Ma))))"
| "transToTermInIRKList (KListPat ll x rl) T S M = (case transToTermInIRLeftKList ll T S M of 
    None \<Rightarrow> None | Some (ll', T', S', M') \<Rightarrow>
          (case transToTermInIRLeftKList (rev rl) (rev T) S' M' of None \<Rightarrow> None
             | Some (rlr, Tr, Sa, Ma) \<Rightarrow> (case x of None \<Rightarrow> 
         if Tr = [] then Some (ll'@(rev rlr), Sa, Ma) else None
        | Some var \<Rightarrow> (case lookup (translateVar var) M of None \<Rightarrow>
        (case formTermListByTypes (rev Tr) Sa of (terml, Sb) \<Rightarrow>
       Some (ll'@terml@(rev rlr), Sb, update (translateVar var) terml Ma))
        | Some terml \<Rightarrow> if typeCheckTermsByTypes (rev Tr) terml then
         Some (ll'@terml@(rev rlr), Sa, Ma) else None))))"
| "transToTermInIRK (KPat l x) ty S M = (if ty = K then
     (case l of [] \<Rightarrow> (case x of None \<Rightarrow> Some (IsabEmptyList, S, M)
     | Some x' \<Rightarrow> Some (VarTerm (IsabList (OtherType SingleKIsab)) (translateVar x'), S, M))
      | (a#al) \<Rightarrow> (case transToTermInIRType a KItem S M of None \<Rightarrow> None
       | Some (a', S', M') \<Rightarrow> (case transToTermInIRK (KPat al x) ty S' M' of None \<Rightarrow> None
       | Some (aa, Sa, Ma) \<Rightarrow> Some (IsabListCon a' aa, Sa, Ma))))
    else if subsort ty KItem subsortGraph then (case x of Some x' \<Rightarrow> None
       | None \<Rightarrow> (case l of [a] \<Rightarrow> transToTermInIRType a ty S M | _ \<Rightarrow> None)) else None)"
| "transToTermInNoneIRK (KPat l x) S M =
   (case l of [] \<Rightarrow> (case x of None \<Rightarrow> Some (IsabEmptyList, S, M)
     | Some x' \<Rightarrow> Some (VarTerm (IsabList (OtherType SingleKIsab)) (translateVar x'), S, M))
      | (a#al) \<Rightarrow> (case transToTermInIRKItem a S M of None \<Rightarrow> None
       | Some (a', S', M') \<Rightarrow> (case transToTermInNoneIRK (KPat al x) S' M' of None \<Rightarrow> None
       | Some (aa, Sa, Ma) \<Rightarrow> Some (IsabListCon a' aa, Sa, Ma))))"
| "transToTermInIRList (ListPat l x r) S M = (case l of [] \<Rightarrow>
        (case x of None \<Rightarrow> (case r of [] \<Rightarrow>
               Some (IsabEmptyList, S, M)
          | (ra#rl') \<Rightarrow> (case transToTermInIRList (ListPat [] None rl') S M
          of None \<Rightarrow> None | Some (rla, S', M') \<Rightarrow>
           (case transToTermInNoneIRK ra S' M' of None \<Rightarrow> None
               | Some (ra', Sa, Ma) \<Rightarrow> Some (IsabListCon ra' rla, Sa, Ma))))
       | Some var \<Rightarrow> (case transToTermInIRList (ListPat [] None r) S M of None \<Rightarrow> None
        | Some (ra,Sa,Ma) \<Rightarrow> Some (IsabListAt (VarTerm (IsabList (OtherType SingleListIsab))
               (translateVar var)) ra, Sa, Ma)))
         | (la#ll') \<Rightarrow> (case transToTermInIRList (ListPat ll' x r) S M
          of None \<Rightarrow> None | Some (lla, S', M') \<Rightarrow>
           (case transToTermInNoneIRK la S' M' of None \<Rightarrow> None
               | Some (la', Sa, Ma) \<Rightarrow> Some (IsabListCon la' lla, Sa, Ma))))"
| "transToTermInIRSet (SetPat l x) S M = (case l of [] \<Rightarrow>
        (case x of None \<Rightarrow> Some (IsabEmptyList, S, M)
       | Some var \<Rightarrow> Some (VarTerm (IsabList (OtherType SingleSetIsab))
               (translateVar var), S, M))
         | (la#ll') \<Rightarrow> (case transToTermInIRSet (SetPat ll' x) S M
          of None \<Rightarrow> None | Some (lla, S', M') \<Rightarrow>
           (case transToTermInNoneIRK la S' M' of None \<Rightarrow> None
               | Some (la', Sa, Ma) \<Rightarrow> Some (IsabListCon la' lla, Sa, Ma))))"
| "transToTermInIRMap (MapPat l x) S M = (case l of [] \<Rightarrow>
        (case x of None \<Rightarrow> Some (IsabEmptyList, S, M)
       | Some var \<Rightarrow> Some (VarTerm (IsabList (OtherType SingleMapIsab))
               (translateVar var), S, M))
         | ((la,ra)#ll') \<Rightarrow> (case transToTermInIRMap (MapPat ll' x) S M
          of None \<Rightarrow> None | Some (lla, S', M') \<Rightarrow>
           (case transToTermInNoneIRK la S' M' of None \<Rightarrow> None
               | Some (la', Sa, Ma) \<Rightarrow> 
     (case transToTermInNoneIRK ra Sa Ma of None \<Rightarrow> None
         | Some (ra',Sb, Mb) \<Rightarrow> Some (IsabListCon (Term (IsabList (OtherType SingleMapIsab))
             KAsMap [la',ra']) lla, Sa, Ma)))))"
| "transToTermInIRBigKWithBag (IRK a) ty S M = (case transToTermInIRK a ty S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) KCellIsab [a'], S', M'))"
| "transToTermInIRBigKWithBag (IRList a) ty S M = (if ty = List then
     (case transToTermInIRList a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) ListCellIsab [a'], S', M'))
    else None)"
| "transToTermInIRBigKWithBag (IRSet a) ty S M = (if ty = Set then
     (case transToTermInIRSet a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) SetCellIsab [a'], S', M'))
    else None)"
| "transToTermInIRBigKWithBag (IRMap a) ty S M = (if ty = Map then
     (case transToTermInIRMap a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) MapCellIsab [a'], S', M'))
    else None)"
| "transToTermInIRBigKWithBag (IRBag a) ty S M = (if ty = Bag then
     (case transToTermInIRBag a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) BagCellIsab [a'], S', M'))
    else None)"
| "transToTermInNoneIRBigKWithBag (IRK a) S M = (case transToTermInNoneIRK a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) KCellIsab [a'], S', M'))"
| "transToTermInNoneIRBigKWithBag (IRList a) S M = (case transToTermInIRList a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) ListCellIsab [a'], S', M'))"
| "transToTermInNoneIRBigKWithBag (IRSet a) S M = (case transToTermInIRSet a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) SetCellIsab [a'], S', M'))"
| "transToTermInNoneIRBigKWithBag (IRMap a) S M = (case transToTermInIRMap a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) MapCellIsab [a'], S', M'))"
| "transToTermInNoneIRBigKWithBag (IRBag a) S M = (case transToTermInIRBag a S M of None \<Rightarrow> None
          | Some (a', S', M') \<Rightarrow> Some (Term (OtherType CellConType) BagCellIsab [a'], S', M'))"
| "transToTermInNoneIRBigKWithLabel (IRBigBag a) S M = (case transToTermInNoneIRBigKWithBag a S M
    of None \<Rightarrow> None | Some (a', S', M') \<Rightarrow> Some (Term (OtherType SingleKListIsab)
      CellAsKList [a'], S', M'))"
| "transToTermInNoneIRBigKWithLabel (IRBigLabel a) S M =
    Some (Term (OtherType SingleKListIsab) KLabelAsKList [transToTermInIRKLabel a], S, M)"
| "transToTermInIRBigKWithLabel (IRBigBag a) ty S M = (if (subsort ty K subsortGraph \<or> ty = List
    \<or> ty = Set \<or> ty = Map \<or> ty = Bag) then (case transToTermInIRBigKWithBag a ty S M
    of None \<Rightarrow> None | Some (a', S', M') \<Rightarrow> Some (Term (OtherType SingleKListIsab)
      CellAsKList [a'], S', M')) else None)"
| "transToTermInIRBigKWithLabel (IRBigLabel a) ty S M = (if ty = KLabel then
    Some (Term (OtherType SingleKListIsab) KLabelAsKList [transToTermInIRKLabel a], S, M)
    else None)"
| "transToTermInIRBag (BagPat l x) S M = (case l of [] \<Rightarrow> (case x of None \<Rightarrow>
          Some (IsabEmptyList, S, M) | Some x' \<Rightarrow> Some (VarTerm (IsabList (OtherType SingleBagIsab))
        (translateVar x'), S, M))
    | (a,b,c)#l' \<Rightarrow> (case transToTermInNoneIRBigKWithBag c S M of None \<Rightarrow> None
     | Some (c', S', M') \<Rightarrow> (case transToTermInIRBag (BagPat l' x) S' M' of None \<Rightarrow> None
     | (Some (la, Sa, Ma)) \<Rightarrow> (if Multiplicity Star \<in> set b then
          Some (IsabListCon (Term (OtherType SingleBagIsab) StarCellAsBag
        [Term (OtherType CellNameType) (CellNameConstr a) [], c']) la, Sa, Ma)
    else if Multiplicity Question \<in> set b then
     Some (IsabListCon (Term (OtherType SingleBagIsab) OptionCellAsBag
        [IsabSome (Term (OtherType CellNameType) (CellNameConstr a) []), c']) la, Sa, Ma)
    else Some (IsabListCon (Term (OtherType SingleBagIsab) SingleCellAsBag
        [(Term (OtherType CellNameType) (CellNameConstr a) []), c']) la, Sa, Ma)))))"
by pat_completeness auto

primrec transToTermInMatchFactor :: "('upVar, 'var, 'svar, 'metaVar metaVar) matchFactor
   \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option" where
"transToTermInMatchFactor (KLabelMatching a) S M = Some (transToTermInIRKLabel a, S,M)"
| "transToTermInMatchFactor (KItemMatching a) S M = transToTermInIRKItem a S M"
| "transToTermInMatchFactor (KListMatching a) S M = transToTermInNoneIRKList a S M"
| "transToTermInMatchFactor (KMatching a) S M = transToTermInNoneIRK a S M"
| "transToTermInMatchFactor (ListMatching a) S M = transToTermInIRList a S M"
| "transToTermInMatchFactor (SetMatching a) S M = transToTermInIRSet a S M"
| "transToTermInMatchFactor (MapMatching a) S M = transToTermInIRMap a S M"
| "transToTermInMatchFactor (BagMatching a) S M = transToTermInIRBag a S M"

primrec transToTermInPat :: "('upVar, 'var, 'svar, 'metaVar metaVar) pat
   \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
             \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
         'iVar) isabTerm * 'iVar list * ('iVar * ('tVar kType isabType,
   ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list) option" where
"transToTermInPat (KLabelFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if ty = KLabel then  (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow>
    Some (Term (OtherType KLabelIsab) (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (KFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if ty = K then  (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow> Some (Term (IsabList (OtherType SingleKIsab))
             (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (KItemFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if subsort ty KItem subsortGraph then (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow> Some (Term (OtherType KItemIsab)
             (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (ListFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if ty = List then (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow> Some (Term (IsabList (OtherType SingleListIsab))
             (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (SetFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if ty = Set then (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow> Some (Term (IsabList (OtherType SingleSetIsab))
             (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (MapFunPat s kl) S M = (case getSort s of None \<Rightarrow> None
     | Some ty \<Rightarrow> if ty = Map then (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S M of None \<Rightarrow> None
        | Some (a', S', M') \<Rightarrow> Some (Term (IsabList (OtherType SingleMapIsab))
             (UserConstr (translateLabel s)) a', S', M'))) else None)"
| "transToTermInPat (NormalPat a) S M = transToTermInMatchFactor a S M"

primrec formTermByList :: "('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
     \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"formTermByList [] = IsabEmptyList"
| "formTermByList (x#l) = IsabListCon x (formTermByList l)"

fun formSUBagTerms :: "('var * key option * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
         \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm option" where
"formSUBagTerms [] = Some IsabEmptyList"
| "formSUBagTerms ((x,y,z)#l) = (case y of None \<Rightarrow> (case z of [z'] \<Rightarrow>
  (case formSUBagTerms l of None \<Rightarrow> None | Some l' \<Rightarrow>
   Some (IsabListCon (Term (OtherType SingleBagIsab) SingleCellAsBag [Term (OtherType CellType)
        Cell [Term (OtherType CellNameType) (CellNameConstr x) [], z']]) l'))
   | _ \<Rightarrow> None)
   | Some Star \<Rightarrow> (case formSUBagTerms l of None \<Rightarrow> None | Some l' \<Rightarrow>
   Some (IsabListCon (Term (OtherType SingleBagIsab) StarCellAsBag [Term (OtherType CellNameType)
        (CellNameConstr x) [], formTermByList z]) l'))
   | Some Question \<Rightarrow> (case z of [z'] \<Rightarrow>
  (case formSUBagTerms l of None \<Rightarrow> None | Some l' \<Rightarrow>
   Some (IsabListCon (Term (OtherType SingleBagIsab) OptionCellAsBag
  [IsabSome (Term (OtherType CellType)
        Cell [Term (OtherType CellNameType) (CellNameConstr x) [], z'])]) l'))
   | _ \<Rightarrow> None))"

fun insertInToCell :: "'var \<Rightarrow> key option \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
            \<Rightarrow> ('var * key option * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
     \<Rightarrow> ('var * key option * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list" where
"insertInToCell a b c [] = [(a,b,[c])]"
| "insertInToCell a b c ((x,y,z)#l) =
    (if a = x then ((x,y,c#z)#l) else (x,y,z)#(insertInToCell a b c l))"

primrec formBagVarTerms :: "'metaVar metaVar list \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm
   \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"formBagVarTerms [] t = t"
| "formBagVarTerms (a#l) t = IsabListAt (VarTerm (IsabList (OtherType SingleBagIsab))
      (translateVar a)) (formBagVarTerms l t)"

(* translate a k term into a isabelle term that is in normal form *)
function transToTermInSUKLabel :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKLabel
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUType :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKItem
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUKItem :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKItem
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInNoneSUKList :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKl list
     \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUKList :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKl list
    \<Rightarrow> 'upVar list \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
     ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
    \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) option"
    and transToTermInSUK :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKFactor list 
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUList :: "('upVar, 'var, 'svar, 'metaVar metaVar) suL list 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUSet :: "('upVar, 'var, 'svar, 'metaVar metaVar) suS list 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUMap :: "('upVar, 'var, 'svar, 'metaVar metaVar) suM list 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUBigKWithBag :: "('upVar, 'var, 'svar, 'metaVar metaVar) suBigKWithBag 
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInNoneSUBigKWithLabel :: "('upVar, 'var, 'svar, 'metaVar metaVar) suBigKWithLabel
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUBigKWithLabel :: "('upVar, 'var, 'svar, 'metaVar metaVar) suBigKWithLabel
    \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
    and transToTermInSUBag :: "('upVar, 'var, 'svar, 'metaVar metaVar) suB list 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list
   \<Rightarrow> 'metaVar metaVar list \<Rightarrow>
     ('var * key option * ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list) list \<Rightarrow>
      (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) option"
 where 
  "transToTermInSUKLabel (SUKLabel a) S M = Some (Term (OtherType KLabelIsab)
    (UserConstr (translateLabel a)) [])"
| "transToTermInSUKLabel (SUKLabelFun a b) S M = (case getSUKLabelMeaning a of None \<Rightarrow>
   (case transToTermInSUKLabel a S M of None \<Rightarrow> None
      | Some (a') \<Rightarrow> (case transToTermInNoneSUKList b S M of None \<Rightarrow> None
      | Some (b') \<Rightarrow> Some (Term (OtherType KLabelIsab)
                      (LabelFormConstr (OtherType KLabelIsab)) [a',b'])))
   | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None | Some ty \<Rightarrow> if ty = KLabel then 
   (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow>
      (case transToTermInSUKList b tyl S M [] of None \<Rightarrow> None 
     | Some (b') \<Rightarrow> Some (Term (OtherType KLabelIsab)
                       (UserConstr (translateLabel s)) b'))) else None))"
| "transToTermInSUKLabel (SUIdKLabel n) S M =
            Some (VarTerm (OtherType KLabelIsab) (translateVar n))"
| "transToTermInSUType (SUKItem l r ty) t S M = (case getSUKLabelMeaning l of None \<Rightarrow>
   (case transToTermInSUKLabel l S M of None \<Rightarrow> None
      | Some (l') \<Rightarrow> (case transToTermInNoneSUKList r S M of None \<Rightarrow> None
      | Some (r') \<Rightarrow> if t = ty then
        (Some (Term (translateRightType t) (LabelFormConstr (translateRightType t))
           [l',r'])) else if subsort t ty subsortGraph then
        (Some (Term (translateRightType t) (CastConstr (translateRightType ty) (translateRightType t))
             [Term (translateRightType ty) (LabelFormConstr (translateRightType ty))
           [l',r']])) else (Some (Term (translateRightType t) (CastConstr
                (translateRightType ty) (translateRightType t)) [Term (translateRightType ty)
         (LabelFormConstr (translateRightType ty)) [l',r']]))))
   | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None
   | Some ty' \<Rightarrow> (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case (transToTermInSUKList r tyl S M []) of
      None \<Rightarrow> None | Some (r') \<Rightarrow>
   if ty' = t then Some (Term (translateRightType ty') (UserConstr (translateLabel s)) r')
      else if subsort ty' t subsortGraph then Some (Term (translateRightType t) (CastConstr
      (translateRightType ty') (translateRightType t))
        [Term (translateRightType ty') (UserConstr (translateLabel s)) r'])
      else if subsort t ty' subsortGraph \<and> isFunctionItem s then
     Some (Term (translateRightType t) (CastConstr
      (translateRightType ty') (translateRightType t))
        [Term (translateRightType ty') (UserConstr (translateLabel s)) r'])
       else None))))"
| "transToTermInSUType (SUIdKItem a b) t S M = (if t = b then
      Some (VarTerm (translateRightType t) (translateVar a))
    else if subsort t b subsortGraph then 
         Some (Term (translateRightType t) (CastConstr (translateRightType b) (translateRightType t))
              [VarTerm (translateRightType t) (translateVar a)])
         else if subsort b t subsortGraph then Some (Term (translateRightType t)
      (CastConstr  (translateRightType b) (translateRightType t))
               [VarTerm (translateRightType b) (translateVar a)])
         else None)"
| "transToTermInSUType (SUHOLE a) t S M = (if t = a then
    Some (Term (translateRightType t) (HoleConstr (translateRightType t)) [])
   else if subsort t a subsortGraph then
   Some (Term (translateRightType t) (CastConstr (translateRightType a) (translateRightType t))
       [Term (translateRightType t) (HoleConstr (translateRightType t)) []])
        else if subsort a t subsortGraph then
            Some (Term (translateRightType t)
                   (CastConstr(translateRightType a) (translateRightType t))
        [Term (translateRightType a) (HoleConstr (translateRightType a)) []]) else None)"
| "transToTermInSUKItem (SUKItem l r ty) S M = (case getSUKLabelMeaning l of None \<Rightarrow>
   (case (transToTermInSUKLabel l S M) of None \<Rightarrow> None | Some (l') \<Rightarrow>
    (case (transToTermInNoneSUKList r S M) of None \<Rightarrow> None
       | Some (r') \<Rightarrow> if ty = KItem then Some (Term (OtherType KItemIsab)
                (LabelFormConstr (OtherType KItemIsab)) (l'#r'#[]))
         else if ty = K then
         Some (Term (OtherType KItemIsab) (CastConstr (translateRightType K) (OtherType KItemIsab))
      [Term (translateRightType K) (LabelFormConstr (translateRightType K)) (l'#r'#[])])
         else if subsort ty KItem subsortGraph then 
          Some (Term (OtherType KItemIsab) (CastConstr (translateRightType ty) (OtherType KItemIsab))
      [Term (translateRightType ty) (LabelFormConstr (translateRightType ty)) (l'#r'#[])])
          else None))
   | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None
   | Some ty' \<Rightarrow> (case getArgSort s of None \<Rightarrow> None
       | Some tyl \<Rightarrow> (case (transToTermInSUKList r tyl S M []) of
      None \<Rightarrow> None | Some (r') \<Rightarrow>
       if ty' = KItem then Some (Term (translateRightType ty')
             (UserConstr (translateLabel s)) r')
      else if subsort ty' KItem subsortGraph then
      Some (Term (OtherType KItemIsab) (CastConstr (translateRightType ty') (OtherType KItemIsab))
            [Term (translateRightType ty') (UserConstr (translateLabel s)) r'])
      else if ty' = K \<and> isFunctionItem s then
        Some (Term (OtherType KItemIsab) (CastConstr (translateRightType ty') (OtherType KItemIsab))
        [Term (translateRightType ty') (UserConstr (translateLabel s)) r']) else None))))"
| "transToTermInSUKItem (SUIdKItem a b) S M = (if b = KItem then
       Some (VarTerm (OtherType KItemIsab) (translateVar a))
    else if b = K then Some (Term (OtherType KItemIsab) (CastConstr (translateRightType K)
     (OtherType KItemIsab)) [VarTerm (translateRightType K) (translateVar a)])
    else if b = KItem then
      Some (VarTerm (translateRightType b) (translateVar a))
    else if subsort b KItem subsortGraph then
        Some (Term (OtherType KItemIsab) (CastConstr (translateRightType b) (OtherType KItemIsab))
          [VarTerm (translateRightType b) (translateVar a)]) else None)"
| "transToTermInSUKItem (SUHOLE a) S M = (if a = KItem then
     Some (Term (OtherType KItemIsab) (HoleConstr (OtherType KItemIsab)) [])
     else if a = KItem then
     Some (Term (translateRightType a) (HoleConstr (translateRightType a)) [])
     else if subsort a KItem subsortGraph then
             Some (Term (OtherType KItemIsab) (CastConstr (translateRightType a) (OtherType KItemIsab))
           [Term (translateRightType a) (HoleConstr (translateRightType a)) []]) else None)"
| "transToTermInNoneSUKList [] S M = Some (IsabEmptyList)"
| "transToTermInNoneSUKList (x#l) S M = (case transToTermInNoneSUKList l S M of None \<Rightarrow> None
        | Some (l') \<Rightarrow> (case x of IdKl v \<Rightarrow> Some (IsabListAt
          (VarTerm (IsabList (OtherType SingleKListIsab)) (translateVar v)) l')
        | ItemKl v \<Rightarrow> (case transToTermInNoneSUBigKWithLabel v S M of None \<Rightarrow> None
         | Some (v') \<Rightarrow> Some (IsabListCon v' l'))))"
| "transToTermInSUKList [] T S M acc = (case T of [] \<Rightarrow> Some (acc) | _ \<Rightarrow> None)"
| "transToTermInSUKList (a#l) T S M acc = (case T of [] \<Rightarrow> None
      | (ty#tyl) \<Rightarrow> (case a of IdKl v \<Rightarrow> (case lookup (translateVar v) M of None \<Rightarrow>
        None | Some terml \<Rightarrow> (case typeCheckSUTermsByTypes T terml of None \<Rightarrow> None
      | Some tyl' \<Rightarrow> transToTermInSUKList l tyl' S M (acc@terml)))
        | ItemKl v \<Rightarrow> (case transToTermInSUBigKWithLabel v ty S M of None \<Rightarrow> None
       | Some (v') \<Rightarrow> transToTermInSUKList l tyl S M (acc@[v']))))"
| "transToTermInSUK [] t S M = (if t = K then Some (IsabEmptyList) else None)"
| "transToTermInSUK (a#l) t S M = (if t = K then
   (case transToTermInSUK l t S M of None \<Rightarrow> None
         | Some (l') \<Rightarrow>
   (case a of IdFactor x \<Rightarrow> Some (IsabListAt (VarTerm (IsabList (OtherType SingleKIsab))
        (translateVar x)) l')
     | ItemFactor x \<Rightarrow> (case transToTermInSUKItem x S M of None \<Rightarrow> None
       | Some (x') \<Rightarrow> Some (IsabListCon x' l'))
    | SUKKItem x y ty \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
        (case transToTermInSUKLabel x S M of None \<Rightarrow> None
           | Some (x') \<Rightarrow> (case transToTermInNoneSUKList y S M of None \<Rightarrow> None
        | Some (y') \<Rightarrow> if ty = K then Some (IsabListAt (Term (translateRightType ty)
     (LabelFormConstr (translateRightType ty)) (x'#y'#[])) l')
    else if subsort ty KItem subsortGraph then
      Some (IsabListAt (Term (translateRightType K) (CastConstr (translateRightType ty)
   (translateRightType K)) [Term (translateRightType ty) (LabelFormConstr (translateRightType ty))
      (x'#y'#[])]) l') else None))
    | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None
        | Some ty' \<Rightarrow> (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow> 
    (case transToTermInSUKList y tyl S M [] of None \<Rightarrow> None
       | Some (y') \<Rightarrow> if ty = ty' then (if ty = K then
       Some (IsabListAt (Term (translateRightType ty) (UserConstr (translateLabel s)) y') l')
     else Some (IsabListAt (Term (translateRightType K) (CastConstr (translateRightType ty')
         (translateRightType K)) [Term (translateRightType ty) (UserConstr (translateLabel s)) y']) l'))
    else if subsort ty ty' subsortGraph then
      (if isFunctionItem s then
    (Some (IsabListAt (Term (translateRightType K) (CastConstr (translateRightType ty')
       (translateRightType K)) [Term (translateRightType ty)
          (CastConstr (translateRightType ty') (translateRightType ty))
             [Term (translateRightType ty') (UserConstr (translateLabel s)) y']]) l'))
   else None) else if subsort ty' ty subsortGraph then 
     Some (IsabListAt (Term (translateRightType K) (CastConstr (translateRightType ty')
     (translateRightType K)) [Term (translateRightType ty') (UserConstr (translateLabel s)) y']) l')
     else None))))))
    else if subsort t KItem subsortGraph then
    (case l of [] \<Rightarrow> (case a of IdFactor x \<Rightarrow> Some (Term (OtherType KItemIsab)
      (CastConstr (translateRightType K)
    (OtherType KItemIsab)) [VarTerm (translateRightType K) (translateVar x)])
    | ItemFactor x \<Rightarrow> (transToTermInSUType x t S M)
    | SUKKItem x y ty \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
        (case transToTermInSUKLabel x S M of None \<Rightarrow> None
           | Some (x') \<Rightarrow> (case transToTermInNoneSUKList y S M of None \<Rightarrow> None
        | Some (y') \<Rightarrow> if ty = K then (if ty = t then
        Some (Term (translateRightType ty)
     (LabelFormConstr (translateRightType ty)) (x'#y'#[]))
    else if subsort t ty subsortGraph then Some (Term (translateRightType t)
     (CastConstr (translateRightType ty) (translateRightType t)) [Term (translateRightType ty)
     (LabelFormConstr (translateRightType ty)) (x'#y'#[])])
    else if subsort ty t subsortGraph then Some (Term (translateRightType t) (CastConstr
    (translateRightType ty) (translateRightType t)) [Term (translateRightType ty)
        (LabelFormConstr (translateRightType ty))
      (x'#y'#[])]) else None) else None))
     | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> None | Some tya \<Rightarrow> 
    (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow> 
     (case transToTermInSUKList y tyl S M [] of None \<Rightarrow> None
        | Some (y') \<Rightarrow> if tya = t then
      Some (Term (translateRightType tya) (UserConstr (translateLabel s)) y')
   else if subsort tya t subsortGraph then
           (if subsort tya ty subsortGraph then
           Some (Term (translateRightType t) (CastConstr (translateRightType tya)
     (translateRightType t)) [Term (translateRightType tya) (UserConstr (translateLabel s)) y'])
     else if subsort ty tya subsortGraph \<and> isFunctionItem s then
      Some (Term (translateRightType t) (CastConstr (translateRightType ty) (translateRightType t))
         [Term (translateRightType ty) (CastConstr (translateRightType tya) (translateRightType ty))
          [Term (translateRightType tya) (UserConstr (translateLabel s)) y']]) else None)
    else if subsort t tya subsortGraph then
     (if isFunctionItem s then (if subsort t ty subsortGraph then
        Some (Term (translateRightType t) (CastConstr (translateRightType tya) (translateRightType t))
          [Term (translateRightType tya) (UserConstr (translateLabel s)) y'])
     else if subsort ty t subsortGraph then
        Some (Term (translateRightType t) (CastConstr (translateRightType ty) (translateRightType t))
         [Term (translateRightType ty) (CastConstr (translateRightType tya) (translateRightType ty))
          [Term (translateRightType tya) (UserConstr (translateLabel s)) y']])
     else None) else None) 
    else None))))) | _ \<Rightarrow> None) else None)"
| "transToTermInSUList [] S M = Some (IsabEmptyList)"
| "transToTermInSUList (a#l) S M = (case transToTermInSUList l S M of None \<Rightarrow> None
      | Some (l') \<Rightarrow> (case a of IdL x \<Rightarrow> Some (IsabListAt (VarTerm (translateRightType List)
            (translateVar x)) l')
     | ItemL x \<Rightarrow> (case transToTermInSUK x K S M of None \<Rightarrow> None | Some (x') \<Rightarrow>
             Some (IsabListCon (Term (OtherType SingleListIsab) KAsList [x']) l'))
     | SUListKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
      (case transToTermInSUKLabel x S M of None \<Rightarrow> None
         | Some (x') \<Rightarrow> (case transToTermInNoneSUKList y S M of None \<Rightarrow> None
    | Some (y') \<Rightarrow> Some (IsabListAt (Term (translateRightType List)
                     (LabelFormConstr (translateRightType List)) [x', y']) l')))
       | Some s \<Rightarrow> (if getSort s = Some List then
       (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow> 
        (case transToTermInSUKList y tyl S M [] of None \<Rightarrow> None
       | Some (y') \<Rightarrow> Some (Term (translateRightType List)
             (UserConstr (translateLabel s)) y'))) else None))))"
| "transToTermInSUSet [] S M = Some (IsabEmptyList)"
| "transToTermInSUSet (a#l) S M = (case transToTermInSUSet l S M of None \<Rightarrow> None
      | Some (l') \<Rightarrow> (case a of IdS x \<Rightarrow> Some (IsabListAt (VarTerm (translateRightType Set)
            (translateVar x)) l')
     | ItemS x \<Rightarrow> (case transToTermInSUK x K S M of None \<Rightarrow> None | Some (x') \<Rightarrow>
             Some (IsabListCon (Term (OtherType SingleSetIsab) KAsSet [x']) l'))
     | SUSetKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
      (case transToTermInSUKLabel x S M of None \<Rightarrow> None
         | Some (x') \<Rightarrow> (case transToTermInNoneSUKList y S M of None \<Rightarrow> None
    | Some (y') \<Rightarrow> Some (Term (translateRightType Set)
                     (LabelFormConstr (translateRightType Set)) [x', y'])))
       | Some s \<Rightarrow> (if getSort s = Some Set then
       (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow> 
        (case transToTermInSUKList y tyl S M [] of None \<Rightarrow> None
       | Some (y') \<Rightarrow> Some (IsabListAt (Term (translateRightType Set)
             (UserConstr (translateLabel s)) y') l'))) else None))))"
| "transToTermInSUMap [] S M = Some (IsabEmptyList)"
| "transToTermInSUMap (a#l) S M = (case transToTermInSUMap l S M of None \<Rightarrow> None
      | Some (l') \<Rightarrow> (case a of IdM x \<Rightarrow> Some (IsabListAt (VarTerm (translateRightType Map)
            (translateVar x)) l')
     | ItemM x y \<Rightarrow> (case transToTermInSUK x K S M of None \<Rightarrow> None | Some (x') \<Rightarrow>
      (case transToTermInSUK y K S M of None \<Rightarrow> None | Some (y') \<Rightarrow>
             Some (IsabListCon (Term (OtherType SingleMapIsab) KAsMap [x', y']) l')))
     | SUMapKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
      (case transToTermInSUKLabel x S M of None \<Rightarrow> None
         | Some (x') \<Rightarrow> (case transToTermInNoneSUKList y S M of None \<Rightarrow> None
    | Some (y') \<Rightarrow> Some (Term (translateRightType Map)
                     (LabelFormConstr (translateRightType Map)) [x', y'])))
       | Some s \<Rightarrow> (if getSort s = Some Map then
       (case getArgSort s of None \<Rightarrow> None | Some tyl \<Rightarrow> 
        (case transToTermInSUKList y tyl S M [] of None \<Rightarrow> None
       | Some (y') \<Rightarrow> Some (IsabListAt (Term (translateRightType Map)
             (UserConstr (translateLabel s)) y') l'))) else None))))"
| "transToTermInSUBigKWithBag (SUK a) t S M = (if subsort t K subsortGraph then
 (case transToTermInSUK a t S M of None \<Rightarrow> None | Some (a') \<Rightarrow> 
     Some (Term (OtherType CellConType) KCellIsab [a'])) else None)"
| "transToTermInSUBigKWithBag (SUList a) t S M = (if t = List then
 (case transToTermInSUList a S M of None \<Rightarrow> None | Some (a') \<Rightarrow> 
     Some (Term (OtherType CellConType) ListCellIsab [a'])) else None)"
| "transToTermInSUBigKWithBag (SUSet a) t S M = (if t = Set then
 (case transToTermInSUSet a S M of None \<Rightarrow> None | Some (a') \<Rightarrow> 
     Some (Term (OtherType CellConType) SetCellIsab [a'])) else None)"
| "transToTermInSUBigKWithBag (SUMap a) t S M = (if t = Map then
 (case transToTermInSUMap a S M of None \<Rightarrow> None | Some (a') \<Rightarrow> 
     Some (Term (OtherType CellConType) MapCellIsab [a'])) else None)"
| "transToTermInSUBigKWithBag (SUBag a) t S M = (if t = Bag then
 (case transToTermInSUBag a S M [] [] of None \<Rightarrow> None | Some (a') \<Rightarrow> 
     Some (Term (OtherType CellConType) BagCellIsab [a'])) else None)"
| "transToTermInNoneSUBigKWithLabel (SUBigBag a) S M =
     (case a of (SUK x) \<Rightarrow> (case transToTermInSUBigKWithBag a K S M of None \<Rightarrow> None
         | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a']))
        | (SUList x) \<Rightarrow> (case transToTermInSUBigKWithBag a List S M of None \<Rightarrow> None
         | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a']))
     | SUSet x \<Rightarrow> (case transToTermInSUBigKWithBag a Set S M of None \<Rightarrow> None
         | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a']))
     | SUMap x \<Rightarrow> (case transToTermInSUBigKWithBag a Map S M of None \<Rightarrow> None
         | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a']))
     | SUBag x \<Rightarrow> (case transToTermInSUBigKWithBag a Bag S M of None \<Rightarrow> None
         | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a'])))"
| "transToTermInNoneSUBigKWithLabel (SUBigLabel a) S M =
       (case transToTermInSUKLabel a S M of None \<Rightarrow> None
        | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) KLabelAsKList [a']))"
| "transToTermInSUBigKWithLabel (SUBigBag a) t S M =
    (case transToTermInSUBigKWithBag a t S M of None \<Rightarrow> None
     | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) CellAsKList [a']))"
| "transToTermInSUBigKWithLabel (SUBigLabel a) t S M =
       (case transToTermInSUKLabel a S M of None \<Rightarrow> None
        | Some (a') \<Rightarrow> Some (Term (OtherType SingleKListIsab) KLabelAsKList [a']))"
| "transToTermInSUBag [] S M varAcc acc = 
        (case formSUBagTerms acc of None \<Rightarrow> None | Some t \<Rightarrow> Some (formBagVarTerms varAcc t))"
| "transToTermInSUBag (a#l) S M varAcc acc = (case a of IdB x
       \<Rightarrow> transToTermInSUBag l S M (varAcc@[x]) acc
     | ItemB x y z \<Rightarrow> (case transToTermInSUBigKWithBag z Bag S M of None \<Rightarrow> None
        | Some (z') \<Rightarrow> if Multiplicity Star \<in> set y then
          transToTermInSUBag l S M varAcc (insertInToCell x (Some Star) z' acc)
     else if Multiplicity Question \<in> set y then
         transToTermInSUBag l S M varAcc (insertInToCell x (Some Question) z' acc)
     else transToTermInSUBag l S M varAcc (insertInToCell x None z' acc)))"
by pat_completeness auto

primrec castInductHeaderAux :: "'upVar \<Rightarrow> 'upVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"castInductHeaderAux a [] = []"
| "castInductHeaderAux a (b#l) = (CaseInduct (translateRightType a) (translateRightType b),
   [IsabState (translateRightType b) (translateRightType b), IsabState (translateRightType b)
      (translateRightType b)], BoolIsab)#castInductHeaderAux a l" 

primrec castInductHeaders :: "'upVar list \<Rightarrow> 'upVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"castInductHeaders [] S = []"
| "castInductHeaders (a#l) S = (castInductHeaderAux a S)@(castInductHeaders l S)" 

definition castInductHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"castInductHeadersDef = castInductHeaders allSubsortableSorts allSubsortableSorts"

fun genFunTermAux :: "(('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list
       \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list" where
"genFunTermAux [] = []"
| "genFunTermAux ((a,b,c,d)#l) = (if d then (Term (OtherType KLabelIsab)
        (KLabelConstr a) [])#genFunTermAux l else genFunTermAux l)"

fun genFunTerms :: "('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr *
            'tVar kType isabType list * isabelleStricts option * bool) list) list
       \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list" where
"genFunTerms [] = []"
| "genFunTerms ((x,y)#l) = (genFunTermAux y)@(genFunTerms l)"

fun formTermListByTerm :: "('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list \<Rightarrow> ('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"formTermListByTerm [] = IsabEmptyList"
| "formTermListByTerm (a#l) = IsabListCon a (formTermListByTerm l)" 

definition funTerms :: "('tVar kType isabType, ('cVar,
        'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm" where
"funTerms = (case userDataTest of None \<Rightarrow> IsabEmptyList
         | Some l \<Rightarrow> formTermListByTerm (genFunTerms l))"

definition genCastInductBody :: "'upVar \<Rightarrow> 'upVar \<Rightarrow> 'iVar list \<Rightarrow>
    ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"genCastInductBody a b S = (case freshIVar S of newVar \<Rightarrow> 
   (case freshIVar (newVar#S) of newVara \<Rightarrow> 
 (case freshIVar (newVara#(newVar#S)) of newVarb \<Rightarrow>
(case freshIVar (newVarb#(newVara#(newVar#S))) of newVarc \<Rightarrow>
(case freshIVar (newVarc#newVarb#(newVara#(newVar#S))) of newVard \<Rightarrow> 
(case freshIVar (newVard#newVarc#newVarb#(newVara#(newVar#S))) of newVare \<Rightarrow>
(case freshIVar (newVare#newVard#newVarc#newVarb#(newVara#(newVar#S))) of newVarf \<Rightarrow>
(case freshIVar (newVarf#newVare#newVard#newVarc#newVarb#(newVara#(newVar#S))) of newVarg \<Rightarrow> 
      ((newVarg#newVarf#newVare#newVard#newVarc#newVarb#(newVara#(newVar#S))),
       [(CaseInduct (translateRightType a) (translateRightType b),newVar,
      [AppFun (FunRuleInduct (translateRightType a))
           [IsabContinue (VarTerm (translateRightType a) newVara),
       IsabContinue (VarTerm (translateRightType a) newVarb)]],IsabContinue
           (Term (translateRightType b) (CastConstr (translateRightType a)
       (translateRightType b)) [VarTerm (translateRightType a) newVara]),
         IsabContinue (Term (translateRightType b) (CastConstr
   (translateRightType a) (translateRightType b)) [(VarTerm (translateRightType a) newVarb)])),
   (CaseInduct (translateRightType a) (translateRightType b),newVarc,
      [AppFun (FunRuleInduct (translateRightType a))
           [IsabContinue (VarTerm (translateRightType a) newVard), IsabBad]],IsabContinue
           (Term (translateRightType b) (CastConstr (translateRightType a)
       (translateRightType b)) [VarTerm (translateRightType a) newVard]), IsabBad),
   (CaseInduct (translateRightType a) (translateRightType b),newVare,
      [AppFun (FunRuleInduct (translateRightType a))
           [IsabContinue (VarTerm (translateRightType a) newVarf),
       IsabGood (VarTerm (translateRightType a) newVarg)]],IsabContinue
           (Term (translateRightType b) (CastConstr (translateRightType a)
       (translateRightType b)) [VarTerm (translateRightType a) newVarf]),
         IsabGood (if a = b then (VarTerm (translateRightType b) newVarg)
        else if subsort a b subsortGraph then AppFun (UnifyFun (translateRightType b)
        (translateRightType a)) [VarTerm (translateRightType a) newVarg]
        else if subsort b a subsortGraph then AppFun The [AppFun (CastFun (translateRightType a)
        (translateRightType b)) [VarTerm (translateRightType a) newVarg]]
        else IsabBad))])))))))))"

primrec castInductBodyAux :: "'upVar \<Rightarrow> 'upVar list \<Rightarrow> 'iVar list \<Rightarrow>
   ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"castInductBodyAux a [] S = (S,[])"
| "castInductBodyAux a (b#l) S = (case (genCastInductBody a b S) of (S', l') \<Rightarrow>
    (case (castInductBodyAux a l S') of (Sa, la) \<Rightarrow> (Sa, l'@la)))" 

primrec castInductBodies :: "'upVar list \<Rightarrow> 'upVar list \<Rightarrow> 'iVar list \<Rightarrow>
   ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"castInductBodies [] T S = (S,[])"
| "castInductBodies (a#l) T S = (case (castInductBodyAux a T S) of (S', l') \<Rightarrow>
   (case (castInductBodies l T S') of (Sa, la) \<Rightarrow> (Sa, l'@la)))" 

definition castInductBodiesDef :: "('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"castInductBodiesDef = castInductBodies allSubsortableSorts allSubsortableSorts []"

function graphToTree :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a * 'a list) list \<Rightarrow> 'a list
        \<Rightarrow> 'a tree list \<Rightarrow> ('a tree * 'a list) option" where
"graphToTree a [] G visited acc = Some (Trunk a acc, visited)"
| "graphToTree a (x#l) G visited acc = (if x \<in> set visited then None else
     (case lookup x G of None \<Rightarrow> graphToTree a l G visited (acc@[Trunk x []])
     | Some xl \<Rightarrow> (case graphToTree x xl G (x#visited) [] of None \<Rightarrow> None
         | Some (newTree, visited') \<Rightarrow> graphToTree a l G visited' (acc@[newTree]))))"
by pat_completeness auto

definition sortTreeTest :: "'upVar tree option" where
"sortTreeTest = (case lookup K subsortGraph of None \<Rightarrow> None | Some xl \<Rightarrow>
         (case graphToTree K xl subsortGraph [K] [] of None \<Rightarrow> None
          | Some (theTree, visited) \<Rightarrow> Some theTree))"

fun genFunRuleHeaders :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list
      \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list option" where
"genFunRuleHeaders [] = Some []"
| "genFunRuleHeaders ((FunPat a b c)#l) = (case genFunRuleHeaders l of None \<Rightarrow> None
    | Some l' \<Rightarrow> (case getSort a of None \<Rightarrow> None | Some ty \<Rightarrow>
     Some (insertAll [(FunRuleAux (UserConstr (translateLabel a)),
      [IsabState (translateRightType ty) (translateRightType ty),
           IsabState (translateRightType ty) (translateRightType ty)], BoolIsab)] l')))"
| "genFunRuleHeaders (x#l) = genFunRuleHeaders l"

definition genFunRuleHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genFunRuleHeadersDef = (case funRuleTest of None \<Rightarrow> []
    | Some l \<Rightarrow> (case genFunRuleHeaders l of None \<Rightarrow> [] | Some l' \<Rightarrow> l'))"

fun genFunOwiseHeaders :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list
      \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list option" where
"genFunOwiseHeaders [] = Some []"
| "genFunOwiseHeaders ((FunPat a b c)#l) = (case c of None \<Rightarrow> genFunOwiseHeaders l
  | Some x \<Rightarrow> (case genFunOwiseHeaders l of None \<Rightarrow> None
    | Some l' \<Rightarrow> (case getSort a of None \<Rightarrow> None | Some ty \<Rightarrow>
     Some (insertAll [(FunRuleOwise (UserConstr (translateLabel a)),
      [IsabState (translateRightType ty) (translateRightType ty),
           IsabState (translateRightType ty) (translateRightType ty)], BoolIsab)] l'))))"
| "genFunOwiseHeaders (x#l) = genFunOwiseHeaders l"

definition genFunOwiseHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genFunOwiseHeadersDef = (case funRuleTest of None \<Rightarrow> []
    | Some l \<Rightarrow> (case genFunOwiseHeaders l of None \<Rightarrow> [] | Some l' \<Rightarrow> l'))"

fun genFunOwiseBodiesAux :: "'svar  \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) pat
   \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) subsFactor \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar)
   suKItem \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * ('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) option" where
"genFunOwiseBodiesAux a (KLabelFunPat s kl) (KLabelSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = KLabel then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUKLabel r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getSUKLabelMeaning r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunOwiseBodiesAux a (KFunPat s kl) (KSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = KLabel then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUK r K S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUKS r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunOwiseBodiesAux a (KItemFunPat s kl) (KItemSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if subsort ty KItem subsortGraph then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUType r ty S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUKItem r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunOwiseBodiesAux a (ListFunPat s kl) (ListSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = List then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUList r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUListS r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunOwiseBodiesAux a (SetFunPat s kl) (SetSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = Set then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUSet r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUSetS r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunOwiseBodiesAux a (MapFunPat s kl) (MapSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = Set then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUMap r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUMapS r of None \<Rightarrow>
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleOwise (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
|"genFunOwiseBodiesAux a x y c S = None"

fun genFunRuleBodiesAux :: "'svar  \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) pat
   \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) subsFactor \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar)
   suKItem \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * ('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) option" where
"genFunRuleBodiesAux a (KLabelFunPat s kl) (KLabelSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = KLabel then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUKLabel r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getSUKLabelMeaning r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (OtherType KLabelIsab)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunRuleBodiesAux a (KFunPat s kl) (KSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = KLabel then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUK r K S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUKS r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType K)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunRuleBodiesAux a (KItemFunPat s kl) (KItemSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if subsort ty KItem subsortGraph then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUType r ty S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUKItem r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType ty)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunRuleBodiesAux a (ListFunPat s kl) (ListSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = List then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUList r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUListS r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType List)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunRuleBodiesAux a (SetFunPat s kl) (SetSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = Set then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUSet r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUSetS r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Set)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
| "genFunRuleBodiesAux a (MapFunPat s kl) (MapSubs r) c S = (case getSort a of None \<Rightarrow> None
   | Some ty \<Rightarrow> if ty = Set then (case getArgSort a of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl S [] of None \<Rightarrow> None
    | Some (kl', S', M') \<Rightarrow> (case transToTermInSUMap r S' M' of None \<Rightarrow> None
   | Some r' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
    | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case getKLabelInSUMapS r of None \<Rightarrow>
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabGood (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
  | Some s' \<Rightarrow> if s = s' then
    Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabContinue r')
    else Some (newVar#S',FunRuleAux (UserConstr (translateLabel s)),newVar, [c'],
      (IsabContinue (Term (translateRightType Map)
       (UserConstr (translateLabel s)) kl')), IsabGood r'))))))) else None)"
|"genFunRuleBodiesAux a x y c S = None"

fun genFunRuleBodiesAuxs :: "'svar \<Rightarrow> (('upVar, 'var, 'svar, 'metaVar metaVar) pat * 
         ('upVar, 'var, 'svar, 'metaVar metaVar) subsFactor *
                       ('upVar, 'var, 'svar, 'metaVar metaVar) suKItem) list \<Rightarrow> 'iVar list \<Rightarrow>
    ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genFunRuleBodiesAuxs a [] S = Some (S,[])"
| "genFunRuleBodiesAuxs a ((x,y,z)#l) S = (case genFunRuleBodiesAuxs a l S of None \<Rightarrow> None
     | Some (S', l') \<Rightarrow> (case genFunRuleBodiesAux a x y z S of None \<Rightarrow> None
      | Some (S', terml) \<Rightarrow> Some (S', terml#l')))"

fun genFunRuleBodies :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list \<Rightarrow> 'iVar list
   \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genFunRuleBodies [] S = Some (S, [])"
| "genFunRuleBodies ((FunPat a b c)#l) S = (case genFunRuleBodiesAuxs a b S of None
    \<Rightarrow> None | Some (S', rl') \<Rightarrow> (case genFunRuleBodies l S' of None
    \<Rightarrow> None | Some (Sa, la) \<Rightarrow> (case getSort a of None \<Rightarrow> None
      | Some ty \<Rightarrow> if ty = KLabel then Some (Sa, la) else
         (case c of None \<Rightarrow> (case freshIVar Sa of newVar \<Rightarrow> 
   (case freshIVar (newVar#Sa) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#Sa) of newVarb \<Rightarrow>
(case freshIVar (newVarb#newVara#newVar#Sa) of newVarc \<Rightarrow>  
         Some ((newVarc#newVarb#newVara#newVar#Sa),
    (FunRuleInduct (translateRightType ty), newVar, [AppFun (BuiltInFunConstr
      Congruence (translateRightType ty)) [VarTerm (translateRightType ty) newVara,
   VarTerm (translateRightType ty) newVarb], AppFun (FunRuleAux (UserConstr (translateLabel a)))
     [IsabContinue (VarTerm (translateRightType ty) newVarb), VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVarc]],
   IsabContinue (VarTerm (translateRightType ty) newVara),VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVarc)#(rl'@la))))))
   | Some (x,y,z) \<Rightarrow> (case genFunOwiseBodiesAux a x y z Sa of None \<Rightarrow> None
    | Some (Sb,termOwise) \<Rightarrow> (case freshIVar Sb of newVar \<Rightarrow> 
   (case freshIVar (newVar#Sb) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#Sb) of newVarb \<Rightarrow>
   (case freshIVar (newVarb#newVara#newVar#Sb) of newVarc \<Rightarrow>  
   (case freshIVar (newVarc#newVarb#newVara#newVar#Sb) of newVard \<Rightarrow>  
   (case freshIVar (newVard#newVarc#newVarb#newVara#newVar#Sb) of newVare \<Rightarrow>  
   (case freshIVar (newVare#newVard#newVarc#newVarb#newVara#newVar#Sb) of newVarf \<Rightarrow>  
   (case freshIVar (newVarf#newVare#newVard#newVarc#newVarb#newVara#newVar#Sb) of newVarg \<Rightarrow>  
   (case freshIVar (newVarg#newVarf#newVare#newVard#newVarc#newVarb#newVara#newVar#Sb) of newVarh \<Rightarrow> 
   (case freshIVar (newVarh#newVarg#newVarf#newVare#newVard#newVarc#newVarb#newVara#newVar#Sb) of newVari \<Rightarrow>  
   Some ((newVari#newVarh#newVarg#newVarf#newVare#newVard#newVarc#newVarb#newVara#newVar#Sb),
     (FunRuleInduct (translateRightType ty), newVard,
     [IsabNot (IsabExist newVarf (translateRightType ty)
     (IsabAnd (AppFun (BuiltInFunConstr Congruence (translateRightType ty))
     [VarTerm (translateRightType ty) newVare, VarTerm (translateRightType ty) newVarf])
      (AppFun (FunRuleAux (UserConstr (translateLabel a)))
     [IsabContinue (VarTerm (translateRightType ty) newVarf), VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVarg]))),
     AppFun (BuiltInFunConstr Congruence (translateRightType ty))
     [VarTerm (translateRightType ty) newVare, VarTerm (translateRightType ty) newVarh],
     AppFun (FunRuleOwise (UserConstr (translateLabel a)))
     [IsabContinue (VarTerm (translateRightType ty) newVarh), VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVari]],
        IsabContinue (VarTerm (translateRightType ty) newVare),VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVari)#
    (FunRuleInduct (translateRightType ty), newVar, [AppFun (BuiltInFunConstr
      Congruence (translateRightType ty)) [VarTerm (translateRightType ty) newVara,
   VarTerm (translateRightType ty) newVarb], AppFun (FunRuleAux (UserConstr (translateLabel a)))
     [IsabContinue (VarTerm (translateRightType ty) newVarb), VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVarc]],
   IsabContinue (VarTerm (translateRightType ty) newVara),VarTerm (IsabState
    (translateRightType ty) (translateRightType ty)) newVarc)#termOwise#(rl'@la)))))))))))))))))"
| "genFunRuleBodies (a#l) S = genFunRuleBodies l S"

fun existsKLabelRule :: "('upVar, 'var, 'svar, 'a) rulePat list \<Rightarrow> bool" where
"existsKLabelRule [] = False"
| "existsKLabelRule (FunPat a b c#l) = (case getSort a of None \<Rightarrow> existsKLabelRule l
      | Some ty \<Rightarrow> if ty = KLabel then True else existsKLabelRule l)"
| "existsKLabelRule (a#l) = existsKLabelRule l"

definition funRuleHeaderKLabel :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"funRuleHeaderKLabel = (FunRuleInduct (OtherType KLabelIsab),
            [IsabState (OtherType KLabelIsab) (OtherType KLabelIsab),
              IsabState (OtherType KLabelIsab) (OtherType KLabelIsab)],BoolIsab)"

definition funRuleBodyKLabel :: "'iVar list \<Rightarrow> 
   ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"funRuleBodyKLabel S = (case funRuleTest of None \<Rightarrow> None | Some l \<Rightarrow> 
    genFunRuleBodies (foldl (\<lambda> acc x . (case x of FunPat a b c \<Rightarrow>
      (case getSort a of None \<Rightarrow> acc | Some ty \<Rightarrow> if ty = KLabel then (FunPat a b c)#acc else acc)
        | _ \<Rightarrow> acc)) l []) S)"

fun gunHasFunConstrHeaders :: "'tVar kType isabType list \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"gunHasFunConstrHeaders [] = []"
| "gunHasFunConstrHeaders (t#l) = (HasFunConstr t, [t], BoolIsab)#gunHasFunConstrHeaders l"

definition gunHasFunConstrHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"gunHasFunConstrHeadersDef = (case userDataTest of None \<Rightarrow> []
           | Some l \<Rightarrow> gunHasFunConstrHeaders ((map (\<lambda> (a,b) . a) l)@[IsabList
   (OtherType SingleKListIsab), IsabList (OtherType SingleBagIsab), IsabList (OtherType SingleKIsab),
        IsabList (OtherType SingleListIsab), IsabList (OtherType SingleSetIsab),
          IsabList (OtherType SingleMapIsab), IsabList (OtherType CellConType)]))"

fun genHasFunConditionList :: "'tVar kType isabType list \<Rightarrow>
   ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list option" where
"genHasFunConditionList [] [] = Some []"
| "genHasFunConditionList (t#tyl) (a#l) = (case genHasFunConditionList tyl l of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some ((AppFun (HasFunConstr t) [a])#l'))"
| "genHasFunConditionList T B = None"

fun genHasFunCondition :: "('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm" where
"genHasFunCondition [] = IsabTrue"
| "genHasFunCondition (a#l) = IsabAnd a (genHasFunCondition l)"

fun genHasFunConstrBodiesAux :: "'tVar kType isabType \<Rightarrow> 
     (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list
  \<Rightarrow> (('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"genHasFunConstrBodiesAux t [] = []"
| "genHasFunConstrBodiesAux ty ((a,b,c)#l) = (case toKItemFunPatTypes b [IVarOne] of la \<Rightarrow>
    (case genHasFunConditionList b la of None \<Rightarrow> genHasFunConstrBodiesAux ty l | Some lb \<Rightarrow> 
     (Term ty a la, IsabAnd (AppFun Membership
      [AppFun (BuiltInFunConstr GetKLabelFun ty) [Term ty a la], funTerms])
         (genHasFunCondition la))#(genHasFunConstrBodiesAux ty l)))"

fun genHasFunConstrBodies :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list) list
   \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list
   * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"genHasFunConstrBodies [] = []"
| "genHasFunConstrBodies ((x,xl)#l) = (HasFunConstr x, [IVarOne],
    CaseList (VarTerm x IVarOne) (genHasFunConstrBodiesAux x xl))#(genHasFunConstrBodies l)"

fun genHasFunConstrList :: "'tVar kType isabType \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
    * 'iVar list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
    'iVar) isabTerm)" where
"genHasFunConstrList x = (HasFunConstr (IsabList x), [IVarOne],
   CaseList (VarTerm (IsabList x) IVarOne) [(IsabEmptyList, IsabTrue),
          (IsabListCon (VarTerm x IVarTwo) (VarTerm (IsabList x) IVarThree),
         IsabAnd (AppFun (HasFunConstr x) [VarTerm x IVarTwo])
             (AppFun (HasFunConstr (IsabList x)) [VarTerm (IsabList x) IVarThree]))])"

definition gunHasFunConstrBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list
 * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm) list" where
"gunHasFunConstrBodiesDef = (case userDataTest of None \<Rightarrow> [] | Some l
     \<Rightarrow> (genHasFunConstrBodies l)@[genHasFunConstrList (OtherType SingleKListIsab),
     genHasFunConstrList (OtherType SingleBagIsab), genHasFunConstrList (OtherType SingleListIsab)
     , genHasFunConstrList (OtherType SingleKIsab), genHasFunConstrList (OtherType SingleSetIsab)
   , genHasFunConstrList (OtherType SingleMapIsab), genHasFunConstrList (OtherType CellConType)])"

definition allSubsortableTypes :: "'tVar kType isabType list" where
"allSubsortableTypes = map (\<lambda> a . translateRightType a) allSubsortableSorts"

fun genNoFunTermList :: "'tVar kType isabType list \<Rightarrow>
   ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list
   \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType,
          'var) kConstr, 'iVar) isabTerm list option" where
"genNoFunTermList [] [] = Some []"
| "genNoFunTermList (t#tyl) (a#l) = (case genNoFunTermList tyl l of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some ((AppFun (HasFunConstr t) [a])#l'))"
| "genNoFunTermList a b = None"

fun genFunInductAux :: "'tVar kType isabType \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr \<Rightarrow>
  'tVar kType isabType list \<Rightarrow> 'tVar kType isabType list \<Rightarrow>
 ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list 
 \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list 
 \<Rightarrow> bool \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genFunInductAux ty s tyl tyl' T [] b S = (if b then Some (S,[])
   else (case freshIVar S of newVar \<Rightarrow> (case genNoFunTermList tyl' T of None \<Rightarrow> None | Some l' \<Rightarrow>
     Some (newVar#S, [(FunRuleInduct ty, newVar, l', IsabContinue (Term ty s T),
       IsabGood(Term ty s T))]))))"
| "genFunInductAux ty s (ty'#tyl) tyl' T (a#l) b S = (if ty' = OtherType CellNameType
   then genFunInductAux ty s tyl tyl' (T@[a]) l b S
   else (case freshIVar S of newVar \<Rightarrow>
  (case freshIVar (newVar#S) of newVara \<Rightarrow>
    (case genFunInductAux ty s tyl tyl' (T@[a]) l b (newVara#newVar#S) of None \<Rightarrow> None
     | Some (S', l') \<Rightarrow>
     Some (S',(FunRuleInduct ty, newVar, [AppFun (HasFunConstr ty') [a],
        AppFun (FunRuleInduct ty') [a, VarTerm ty' newVara]], IsabContinue (Term ty s (T@(a#l))),
       IsabContinue (Term ty s (T@((VarTerm ty' newVara)#l))))#l')))))"
| "genFunInductAux ty s tyl tyl' T (a#l) b S = None"

primrec toFunPatTypes :: "'tVar kType isabType list \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list  * 
   ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list)" where
"toFunPatTypes [] S = (S,[])"
| "toFunPatTypes (t#l) S = (case freshIVar S of newVar \<Rightarrow>
   (case (toFunPatTypes l (newVar#S)) of (S',l') \<Rightarrow>
          (S',(VarTerm t newVar)#l')))"

fun genFunInductBodiesAux :: "'tVar kType isabType \<Rightarrow>
   (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genFunInductBodiesAux ty [] S = Some (S,[])"
| "genFunInductBodiesAux ty ((a,b,c,d)#l) S =
        (case toFunPatTypes b S of (S', bt) \<Rightarrow>
   (case genFunInductAux ty a b b [] bt d S' of None \<Rightarrow> None
     | Some (Sa, la) \<Rightarrow> (case genFunInductBodiesAux ty l Sa of None \<Rightarrow> None
    | Some (Sb, lb) \<Rightarrow> Some (Sb, la@lb))))"

fun genFunInductBodies :: "('tVar kType isabType *
   (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list) list \<Rightarrow> 'iVar list
   \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genFunInductBodies [] S = Some (S,[])"
| "genFunInductBodies ((x,y)#l) S = (if x = OtherType CellNameType then genFunInductBodies l S
   else (case genFunInductBodiesAux x y S of None \<Rightarrow> None
    | Some (S', l') \<Rightarrow> (case genFunInductBodies l S' of None \<Rightarrow> None
    | Some (Sa, la) \<Rightarrow> Some (Sa, l'@la))))"

primrec funInductHeaders :: "'tVar kType isabType list
    \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"funInductHeaders [] = []"
| "funInductHeaders (x#l) = (if x = (OtherType KLabelIsab) \<or>  x = OtherType CellNameType 
        then (funInductHeaders l)
       else (FunRuleInduct x, [x, x], BoolIsab)#(funInductHeaders l))"

definition funInductHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"funInductHeadersDef = (case userDataTest of None \<Rightarrow> []
    | Some l \<Rightarrow> (case funRuleBodyKLabel [] of None \<Rightarrow>
     (castInductHeadersDef @ genFunRuleHeadersDef @ genFunOwiseHeadersDef
          @ (funInductHeaders (map (\<lambda> (a,b) . a) l))) | Some (S', l') \<Rightarrow>
   if l' = [] then 
     (castInductHeadersDef @ genFunRuleHeadersDef @ genFunOwiseHeadersDef
          @ (funInductHeaders (map (\<lambda> (a,b) . a) l)))
   else (funRuleHeaderKLabel#((castInductHeadersDef @ genFunRuleHeadersDef @ genFunOwiseHeadersDef
          @ (funInductHeaders (map (\<lambda> (a,b) . a) l)))))))"

definition funInductDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"funInductDef = (case castInductBodiesDef of (S,l) \<Rightarrow>
     (case funRuleBodyKLabel S of None \<Rightarrow> [] | Some (S', l') \<Rightarrow> (case funRuleTest of None \<Rightarrow> []
    | Some rl \<Rightarrow> (case genFunRuleBodies rl S' of None \<Rightarrow> [] | Some (Sa, la) \<Rightarrow> if la = []
     then [] else (case userDataTest of None \<Rightarrow> []
          | Some ul \<Rightarrow> (case genFunInductBodies ul Sa of None \<Rightarrow> []
   | Some (Sb,lb) \<Rightarrow> (l@l'@la@lb)))))))"

fun leastComSuperSort :: "'upVar \<Rightarrow> 'upVar \<Rightarrow> 'upVar tree \<Rightarrow> 'upVar list \<Rightarrow> 'upVar list" where
"leastComSuperSort a b (Trunk x []) acc = (if acc = [] then [x] else acc)"
| "leastComSuperSort a b (Trunk x ((Trunk y yl)#l)) acc =
     (if subsort a y subsortGraph \<and> subsort b y subsortGraph then
     (case leastComSuperSort a b (Trunk y yl) [] of acc' \<Rightarrow> 
        leastComSuperSort a b (Trunk x l) (acc@acc'))
                        else leastComSuperSort a b (Trunk x l) acc)"

definition leastComSuperSortDef :: "'upVar \<Rightarrow> 'upVar  \<Rightarrow> 'upVar list" where
"leastComSuperSortDef a b = (case sortTreeTest of None \<Rightarrow> []
          | Some l \<Rightarrow> leastComSuperSort a b l [])"

fun getSortInSUK :: "('upVar, 'var, 'svar, 'metaVar metaVar) suKFactor list \<Rightarrow> 'upVar" where
"getSortInSUK [] = K"
| "getSortInSUK (a#l) = (if l = [] then
           (case a of IdFactor x \<Rightarrow> K
       | ItemFactor (SUHOLE ty) \<Rightarrow> ty
       | ItemFactor (SUIdKItem x ty) \<Rightarrow> ty
       | ItemFactor (SUKItem x y ty) \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> ty
         | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> ty | Some ty' \<Rightarrow> 
              if subsort ty' ty subsortGraph then ty' else ty))
           | SUKKItem x y ty \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> ty
          | Some s \<Rightarrow> (case getSort s of None \<Rightarrow> ty | Some ty' \<Rightarrow>
            if subsort ty' ty subsortGraph then ty' else ty))) else K)"

fun genListOfAnywhereBodies :: "'upVar list \<Rightarrow> 'iVar
      \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm \<Rightarrow> 'tVar kType isabType \<Rightarrow>
    ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm \<Rightarrow> 'tVar kType isabType \<Rightarrow> 
     ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"genListOfAnywhereBodies [] v c lt lterm rt rterm = []"
| "genListOfAnywhereBodies (ty#l) v c lt lterm rt rterm = 
  (AnywhereAux (translateRightType ty), v, [c], IsabContinue
          (AppFun (UnifyFun (translateRightType ty) lt) [lterm]),
    IsabGood (AppFun (UnifyFun (translateRightType ty) rt) [rterm]))
       #(genListOfAnywhereBodies l v c lt lterm rt rterm)"

(* generete anywhere rules in Isabelle *)
definition genAnywhereBodiesAux :: "'svar \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) irKList \<Rightarrow>
       ('upVar, 'var, 'svar, 'metaVar metaVar) suKFactor list
    \<Rightarrow> ('upVar, 'var, 'svar, 'metaVar metaVar) suKItem \<Rightarrow> 'iVar list
    \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereBodiesAux s kl terml c S = (case freshIVar S of newVar \<Rightarrow>
    (case getSort s of None \<Rightarrow> None
        | Some ty \<Rightarrow> (case getSortInSUK terml of ty' \<Rightarrow>
      if subsort ty ty' subsortGraph then (case getArgSort s of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl (newVar#S) [] of None \<Rightarrow> None
         | Some (terms, S', M') \<Rightarrow> (case transToTermInSUK terml ty' S' M' of None \<Rightarrow> None
       | Some terml' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
      | Some c' \<Rightarrow> Some (S', [(AnywhereAux (translateRightType ty'), newVar,
       [c'], IsabContinue (AppFun (UnifyFun (translateRightType ty') (translateRightType ty))
      [Term (translateRightType ty') (UserConstr (translateLabel s)) terms]),
           IsabGood terml')])))))
      else if subsort ty' ty subsortGraph then (case getArgSort s of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl (newVar#S) [] of None \<Rightarrow> None
         | Some (terms, S', M') \<Rightarrow> (case transToTermInSUK terml ty S' M' of None \<Rightarrow> None
       | Some terml' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
      | Some c' \<Rightarrow> Some (S', [(AnywhereAux (translateRightType ty), newVar,
       [c'], IsabContinue (Term (translateRightType ty) (UserConstr (translateLabel s)) terms),
           IsabGood (AppFun (UnifyFun (translateRightType ty) (translateRightType ty')) [terml']))])))))
      else (case leastComSuperSortDef ty ty' of theTyl
         \<Rightarrow> (case getArgSort s of None \<Rightarrow> None
    | Some tyl \<Rightarrow> (case transToTermInIRKList kl tyl (newVar#S) [] of None \<Rightarrow> None
         | Some (terms, S', M') \<Rightarrow> (case transToTermInSUK terml ty S' M' of None \<Rightarrow> None
       | Some terml' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
      | Some c' \<Rightarrow> Some (S', genListOfAnywhereBodies theTyl newVar c' (translateRightType ty)
        (Term (translateRightType ty) (UserConstr (translateLabel s)) terms)
             (translateRightType ty') terml')))))))))"

fun genAnywhereBodies :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list
             \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereBodies [] S = Some (S, [])"
| "genAnywhereBodies ((AnywherePat a b c d)#l) S =
    (case genAnywhereBodiesAux a b c d S of None \<Rightarrow> None
        | Some (S', l') \<Rightarrow> (case genAnywhereBodies l S' of None \<Rightarrow> None
         | Some (Sa, la) \<Rightarrow> Some (Sa, l'@la)))"
| "genAnywhereBodies (a#l) S = genAnywhereBodies l S"

primrec genAnywherePartialInductBodies :: "'tVar kType isabType list
             \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywherePartialInductBodies [] S = Some (S, [])"
| "genAnywherePartialInductBodies (t#l) S = (case genAnywherePartialInductBodies l S of None \<Rightarrow> None
        | Some (S',l') \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case freshIVar (newVar#S') of newVara \<Rightarrow>
  (case freshIVar (newVara#newVar#S') of newVarb \<Rightarrow>
    Some (newVarb#newVara#newVar#S',(AnywhereInduct t, newVar,
       [AppFun (AnywhereAux t) [IsabContinue (VarTerm t newVara), IsabGood (VarTerm t newVarb)]],
      IsabContinue (VarTerm t newVara), IsabGood (VarTerm t newVarb))#l')))))"

definition genAnywhereBodiesTest :: "'iVar list
      \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereBodiesTest S = (case anywhereRuleTest of None \<Rightarrow> None
    | Some l \<Rightarrow> (genAnywhereBodies l S))"

definition genAnywhereMoreBodiesTest :: "'iVar list
      \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereMoreBodiesTest S = (case genAnywhereBodiesTest S of None \<Rightarrow> None
       | Some (S',l') \<Rightarrow> genAnywherePartialInductBodies (foldl (\<lambda> acc (a,b) .
    (case a of AnywhereAux t \<Rightarrow> insertAll [t] acc | _ \<Rightarrow> acc)) [] l') S')"

primrec genAnywhereHeaders :: "'tVar kType isabType list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genAnywhereHeaders [] = []"
| "genAnywhereHeaders (t#l) = (AnywhereAux t, [IsabState t t, IsabState t t],
             BoolIsab)#(genAnywhereHeaders l)"

definition genAnywhereHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genAnywhereHeadersDef = (case genAnywhereBodiesTest [] of None \<Rightarrow> []
       | Some (S,l) \<Rightarrow> genAnywhereHeaders (foldl (\<lambda> acc (a,b) .
    (case a of AnywhereAux t \<Rightarrow> insertAll [t] acc | _ \<Rightarrow> acc)) [] l))"

primrec genAnywhereInductHeaders :: "'tVar kType isabType list
    \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genAnywhereInductHeaders [] = []"
| "genAnywhereInductHeaders (t#l) = (if t = (OtherType KLabelIsab) \<or> t = OtherType CellNameType
      then (genAnywhereInductHeaders l)
   else (AnywhereInduct t, [IsabState t t, IsabState t t],
          BoolIsab)#(genAnywhereInductHeaders l))"

definition genAnywhereInductHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genAnywhereInductHeadersDef = (case userDataTest of None \<Rightarrow> []
           | Some l \<Rightarrow> genAnywhereInductHeaders ((map (\<lambda> (a,b) . a) l)@[IsabList
   (OtherType SingleKListIsab), IsabList (OtherType SingleBagIsab), IsabList (OtherType SingleKIsab),
        IsabList (OtherType SingleListIsab), IsabList (OtherType SingleSetIsab),
          IsabList (OtherType SingleMapIsab), IsabList (OtherType CellConType)]))"

primrec genAnywhereInductList :: "'tVar kType isabType list \<Rightarrow> 'iVar list \<Rightarrow>
    ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"genAnywhereInductList [] S = (S,[])"
| "genAnywhereInductList (t#l) S = (case genAnywhereInductList l S of (S',l') \<Rightarrow>
(case freshIVar S' of newVar \<Rightarrow>
  (case freshIVar (newVar#S') of newVara \<Rightarrow> (case freshIVar (newVara#newVar#S') of newVarb \<Rightarrow>
   (case freshIVar (newVarb#newVara#newVar#S') of newVarc \<Rightarrow>
  (case freshIVar (newVarc#newVarb#newVara#newVar#S') of newVard \<Rightarrow>
   (case freshIVar (newVard#newVarc#newVarb#newVara#newVar#S') of newVare \<Rightarrow>
    (newVare#newVard#newVarc#newVarb#newVara#newVar#S',
          [(AnywhereInduct (IsabList t), newVar, [], IsabContinue IsabEmptyList,
            IsabGood IsabEmptyList),
     (AnywhereInduct (IsabList t), newVara, [AppFun (AnywhereInduct t)
           [IsabContinue (VarTerm t newVarb), IsabGood (VarTerm t newVard)]],
      IsabContinue (IsabListCon (VarTerm t newVarb)
              (VarTerm (IsabList t) newVarc)),
            IsabGood (IsabListCon (VarTerm t newVard)
              (VarTerm (IsabList t) newVarc))),
    (AnywhereInduct (IsabList t), newVare, [AppFun (AnywhereInduct t)
           [IsabContinue (VarTerm (IsabList t) newVarc), IsabGood (VarTerm (IsabList t) newVard)]],
      IsabContinue (IsabListCon (VarTerm t newVarb)
              (VarTerm (IsabList t) newVarc)),
            IsabGood (IsabListCon (VarTerm t newVarb)
              (VarTerm (IsabList t) newVard)))]@l'))))))))"

definition genAnywhereInductListDef :: "'iVar list \<Rightarrow>
    ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"genAnywhereInductListDef S = genAnywhereInductList [(OtherType SingleKListIsab),
    (OtherType SingleBagIsab), (OtherType SingleKIsab), (OtherType SingleListIsab),
    (OtherType SingleSetIsab), (OtherType SingleMapIsab), (OtherType CellConType)] S"

fun genAnywhereInductAux :: "'tVar kType isabType \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr \<Rightarrow>
  'tVar kType isabType list \<Rightarrow>
 ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list 
 \<Rightarrow> ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm list 
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereInductAux ty s tyl T [] S = Some (S,[])"
| "genAnywhereInductAux ty s (ty'#tyl) T (a#l) S = (if ty' = (OtherType KLabelIsab) \<or>
   ty' = OtherType CellNameType
   then genAnywhereInductAux ty s tyl (T@[a]) l S else (case freshIVar S of newVar \<Rightarrow>
  (case freshIVar (newVar#S) of newVara \<Rightarrow>
    (case genAnywhereInductAux ty s tyl (T@[a]) l (newVara#newVar#S) of None \<Rightarrow> None
     | Some (S', l') \<Rightarrow>
     Some (S',(AnywhereInduct ty, newVar, [AppFun (AnywhereInduct ty') [a, VarTerm ty' newVara]],
    IsabContinue (Term ty s (T@(a#l))),  IsabGood (Term ty s (T@((VarTerm ty' newVara)#l))))#l')))))"
| "genAnywhereInductAux ty s tyl T (a#l) S = None"

fun geAnywhereInductBodiesAux :: "'tVar kType isabType \<Rightarrow>
   (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list
    \<Rightarrow> 'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"geAnywhereInductBodiesAux ty [] S = Some (S,[])"
| "geAnywhereInductBodiesAux ty ((a,b,c,d)#l) S =
        (case toFunPatTypes b S of (S', bt) \<Rightarrow>
   (case genAnywhereInductAux ty a b [] bt S' of None \<Rightarrow> None
     | Some (Sa, la) \<Rightarrow> (case geAnywhereInductBodiesAux ty l Sa of None \<Rightarrow> None
    | Some (Sb, lb) \<Rightarrow> Some (Sb, la@lb))))"

fun genAnywhereInductBodies :: "('tVar kType isabType *
   (('cVar, 'tVar kType isabType, 'var) kConstr \<times>
   'tVar kType isabType list \<times> isabelleStricts option \<times> bool) list) list \<Rightarrow> 'iVar list
   \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"genAnywhereInductBodies [] S = Some (S,[])"
| "genAnywhereInductBodies ((x,y)#l) S = (case geAnywhereInductBodiesAux x y S of None \<Rightarrow> None
    | Some (S', l') \<Rightarrow> (case genAnywhereInductBodies l S' of None \<Rightarrow> None
    | Some (Sa, la) \<Rightarrow> Some (Sa, l'@la)))"

definition AnywhereInductDef :: "'iVar list
       \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"AnywhereInductDef S = (case genAnywhereMoreBodiesTest S of None \<Rightarrow> None
    | Some (S', l') \<Rightarrow> if l' = [] then Some (S', []) else
         (case genAnywhereInductListDef S' of (Sa, la)
       \<Rightarrow> (case userDataTest of None \<Rightarrow> None
       | Some rl \<Rightarrow> (case genAnywhereInductBodies rl Sa of None \<Rightarrow> None
     | Some (Sb, lb) \<Rightarrow> Some (Sb, l'@la@lb)))))"

definition anywhereSeqHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"anywhereSeqHeader = (AnywhereSeq, [IsabState (IsabList (OtherType SingleBagIsab))
         (IsabList (OtherType SingleBagIsab)), IsabState (IsabList (OtherType SingleBagIsab))
         (IsabList (OtherType SingleBagIsab))], BoolIsab)"

definition anywhereSeqBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"anywhereSeqBodies = (case freshIVar [IVarOne, IVarTwo, IVarThree] of newVar \<Rightarrow> 
  (case freshIVar [IVarOne, IVarTwo, IVarThree, newVar] of newVara \<Rightarrow> 
 (case freshIVar [IVarOne, IVarTwo, IVarThree, newVar, newVara] of newVarb \<Rightarrow> 
   [(AnywhereSeq, newVar, [IsabNot (IsabExist (IVarTwo)
        (IsabList (OtherType SingleBagIsab)) (IsabAnd (AppFun (BuiltInFunConstr
      Congruence (IsabList (OtherType SingleBagIsab))) [VarTerm (IsabList (OtherType SingleBagIsab))
        IVarOne, VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo]) (AppFun (AnywhereInduct
        (IsabList (OtherType SingleBagIsab))) [IsabContinue (VarTerm (IsabList
       (OtherType SingleBagIsab)) IVarTwo), IsabGood (VarTerm (IsabList
       (OtherType SingleBagIsab)) IVarThree)])))], IsabContinue (VarTerm (IsabList (OtherType
      SingleBagIsab)) IVarOne), IsabGood (VarTerm (IsabList (OtherType SingleBagIsab)) IVarOne)),
  (AnywhereSeq, newVara, [AppFun (AnywhereInduct (IsabList (OtherType SingleBagIsab)))
        [(AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleBagIsab)))
        [VarTerm (IsabList (OtherType SingleBagIsab))
        IVarOne, VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo]),
   IsabContinue (VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo),
       IsabGood (VarTerm (IsabList (OtherType SingleBagIsab)) IVarThree)],
      AppFun AnywhereSeq [IsabContinue (VarTerm (IsabList (OtherType SingleBagIsab)) IVarThree),
       IsabGood (VarTerm (IsabList (OtherType SingleBagIsab)) newVarb)]],
      IsabContinue (VarTerm (IsabList (OtherType
      SingleBagIsab)) IVarOne), IsabGood (VarTerm (IsabList (OtherType SingleBagIsab)) newVarb))])))"

definition allAnywhereHeaders :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"allAnywhereHeaders = (case AnywhereInductDef [] of None \<Rightarrow> []
    | Some (S, l) \<Rightarrow> if l = [] then [] else
       anywhereSeqHeader#(genAnywhereHeadersDef@genAnywhereInductHeadersDef))"

definition allAnywhereBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"allAnywhereBodies = (case AnywhereInductDef [] of None \<Rightarrow> []
         | Some (S, l) \<Rightarrow> if l = [] then [] else (anywhereSeqBodies@l))"

(* transfer k rules into Isabelle *)
definition kruleInductHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"kruleInductHeader = (KRuleInduct, [IsabState (IsabList (OtherType SingleKIsab))
         (IsabList (OtherType SingleKIsab)), IsabState (IsabList (OtherType SingleKIsab))
         (IsabList (OtherType SingleKIsab))], BoolIsab)"

fun kruleInductBodies :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list \<Rightarrow> 
    'iVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list option" where
"kruleInductBodies [] S = Some []"
| "kruleInductBodies ((KRulePat a b c)#l) S =
   (case transToTermInIRK a K S [] of None \<Rightarrow> None
     | Some (a', S', M') \<Rightarrow> (case transToTermInSUK b K S' M' of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
       | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case (kruleInductBodies l (newVar#S'))
    of None \<Rightarrow> None | Some l' \<Rightarrow>
             Some ((KRuleInduct, newVar, [c'], IsabContinue a', IsabGood b')#l'))))))"
| "kruleInductBodies (a#l) S = None"

definition kruleInductBodiesDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"kruleInductBodiesDef = (case normalKRuleTest of None \<Rightarrow> []
           | Some l \<Rightarrow> (case kruleInductBodies l [] of None \<Rightarrow> []
         | Some l' \<Rightarrow> l'))"

primrec BagRuleInductHeaders :: "'tVar kType isabType list \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"BagRuleInductHeaders [] = []"
| "BagRuleInductHeaders (t#l) = (BagRuleInduct t, [IsabState t t, IsabState t t], BoolIsab)
       #(BagRuleInductHeaders l)"

definition BagRuleInductHeadersDef :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType) list" where
"BagRuleInductHeadersDef = BagRuleInductHeaders [OtherType SingleBagIsab,
    IsabList (OtherType SingleBagIsab), IsabList (OtherType CellConType), OtherType CellType]"

fun bagRuleInductBodies :: "('upVar, 'var, 'svar, 'metaVar metaVar) rulePat list \<Rightarrow> 
    'iVar list \<Rightarrow> ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"bagRuleInductBodies [] S = (case freshIVar S of newVar \<Rightarrow> 
  (case freshIVar (newVar#S) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#S) of newVarb \<Rightarrow> 
  (case freshIVar (newVarb#newVara#newVar#S) of newVarc
      \<Rightarrow> (case freshIVar (newVarc#newVarb#newVara#newVar#S) of newVard 
      \<Rightarrow> (case freshIVar (newVard#newVarc#newVarb#newVara#newVar#S) of newVare \<Rightarrow> 
    Some ((newVare#newVard#newVarc#newVarb#newVara#newVar#S),
      [(BagRuleInduct (IsabList (OtherType SingleBagIsab)),
         newVar, [], IsabContinue IsabEmptyList,
            IsabGood IsabEmptyList),
     (BagRuleInduct (IsabList (OtherType SingleBagIsab)), newVara,
       [AppFun (BagRuleInduct (OtherType SingleBagIsab))
   [IsabContinue (VarTerm (OtherType SingleBagIsab) newVarb),
    IsabGood (VarTerm (OtherType SingleBagIsab) newVard)]],
      IsabContinue (IsabListCon (VarTerm (OtherType SingleBagIsab) newVarb)
              (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc)),
            IsabGood (IsabListCon (VarTerm (OtherType SingleBagIsab) newVard)
              (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc))),
    (BagRuleInduct (IsabList (OtherType SingleBagIsab)), newVare,
   [AppFun (BagRuleInduct (IsabList (OtherType SingleBagIsab)))
       [IsabContinue (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc),
        IsabGood (VarTerm (IsabList (OtherType SingleBagIsab)) newVard)]],
      IsabContinue (IsabListCon (VarTerm (OtherType SingleBagIsab) newVarb)
              (VarTerm (IsabList (OtherType SingleBagIsab)) newVarc)),
            IsabGood (IsabListCon (VarTerm(OtherType SingleBagIsab) newVarb)
              (VarTerm (IsabList (OtherType SingleBagIsab)) newVard)))])))))))"
| "bagRuleInductBodies ((BagRulePat a b c)#l) S =
   (case transToTermInIRBag a S [] of None \<Rightarrow> None
     | Some (a', S', M') \<Rightarrow> (case transToTermInSUBag b S' M' [] [] of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case transToTermInSUType c Bool S' M' of None \<Rightarrow> None
       | Some c' \<Rightarrow> (case freshIVar S' of newVar \<Rightarrow> (case (bagRuleInductBodies l (newVar#S'))
    of None \<Rightarrow> None | Some (Sa, l') \<Rightarrow> Some (Sa, (BagRuleInduct (IsabList (OtherType SingleBagIsab)),
      newVar, [c'], IsabContinue a', IsabGood b')#l'))))))"
| "bagRuleInductBodies (a#l) S = None"

definition bagRuleInductBodiesDef :: "'iVar list \<Rightarrow>
   ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list) option" where
"bagRuleInductBodiesDef S = (case normalBagRuleTest of None \<Rightarrow> None
           | Some l \<Rightarrow> bagRuleInductBodies l S)"

definition bagRuleCellTypeBody :: "'iVar list \<Rightarrow> 
  ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"bagRuleCellTypeBody S = (case freshIVar S of newVar \<Rightarrow> 
  (case freshIVar (newVar#S) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#S) of newVarb \<Rightarrow> 
  (case freshIVar (newVarb#newVara#newVar#S) of newVarc \<Rightarrow> 
   ((newVarb#newVara#newVar#S), [(BagRuleInduct (OtherType CellType), newVar,
     [AppFun KRuleInduct [IsabContinue (VarTerm (IsabList (OtherType SingleKIsab))
        newVarb), IsabGood (VarTerm (IsabList (OtherType SingleKIsab))
        newVarc)]], IsabContinue (Term (OtherType CellType) Cell
             [VarTerm (OtherType CellNameType) newVara,
     Term (OtherType CellConType) KCellIsab [VarTerm (IsabList (OtherType SingleKIsab)) newVarb]]),
      IsabGood (Term (OtherType CellType) Cell [VarTerm (OtherType CellNameType) newVara,
     Term (OtherType CellConType) KCellIsab
               [VarTerm (IsabList (OtherType SingleKIsab)) newVarc]]))])))))"

definition bagRuleCellConTypesBody :: "'iVar list \<Rightarrow> 
  ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"bagRuleCellConTypesBody S = (case freshIVar S of newVar \<Rightarrow> 
  (case freshIVar (newVar#S) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#S) of newVarb \<Rightarrow> 
  (case freshIVar (newVarb#newVara#newVar#S) of newVarc \<Rightarrow> 
 (case freshIVar (newVarc#newVarb#newVara#newVar#S) of newVard \<Rightarrow> 
 (case freshIVar (newVard#newVarc#newVarb#newVara#newVar#S) of newVare \<Rightarrow> 
   ((newVarb#newVara#newVar#S), [(BagRuleInduct (IsabList (OtherType CellConType)),
         newVar, [], IsabContinue IsabEmptyList,
            IsabGood IsabEmptyList),
     (BagRuleInduct (IsabList (OtherType CellConType)), newVara,
       [AppFun KRuleInduct [IsabContinue (Term (OtherType CellConType) KCellIsab
      [VarTerm (IsabList (OtherType SingleKIsab)) newVarb]),
    IsabGood (Term (OtherType CellConType) KCellIsab
      [VarTerm (IsabList (OtherType SingleKIsab)) newVard])]],
      IsabContinue (IsabListCon (Term (OtherType CellConType) KCellIsab
      [VarTerm (IsabList (OtherType SingleKIsab)) newVarb])
              (VarTerm (IsabList (OtherType CellConType)) newVarc)),
            IsabGood (IsabListCon (Term (OtherType CellConType) KCellIsab
      [VarTerm (IsabList (OtherType SingleKIsab)) newVard])
              (VarTerm (IsabList (OtherType CellConType)) newVarc))),
    (BagRuleInduct (IsabList (OtherType CellConType)), newVare,
   [AppFun (BagRuleInduct (IsabList (OtherType CellConType)))
       [IsabContinue (VarTerm (IsabList (OtherType CellConType)) newVarc),
        IsabGood (VarTerm (IsabList (OtherType CellConType)) newVard)]],
      IsabContinue (IsabListCon (VarTerm (OtherType CellConType) newVarb)
              (VarTerm (IsabList (OtherType CellConType)) newVarc)),
            IsabGood (IsabListCon (VarTerm(OtherType CellConType) newVarb)
              (VarTerm (IsabList (OtherType CellConType)) newVard)))])))))))"

definition bagRuleSingleBagBody :: "'iVar list \<Rightarrow> 
  ('iVar list * (('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list)" where
"bagRuleSingleBagBody S = (case freshIVar S of newVar \<Rightarrow> 
  (case freshIVar (newVar#S) of newVara \<Rightarrow> (case freshIVar (newVara#newVar#S) of newVarb \<Rightarrow> 
  (case freshIVar (newVarb#newVara#newVar#S) of newVarc \<Rightarrow> 
 (case freshIVar (newVarc#newVarb#newVara#newVar#S) of newVard \<Rightarrow> 
 (case freshIVar (newVard#newVarc#newVarb#newVara#newVar#S) of newVare \<Rightarrow> 
   ((newVare#newVard#newVarc#newVarb#newVara#newVar#S),
       [(BagRuleInduct (OtherType SingleBagIsab), newVar,
     [AppFun (BagRuleInduct (OtherType CellType)) [IsabContinue (VarTerm (OtherType CellType)
    newVara), IsabGood (VarTerm (OtherType CellType) newVarb)]],
    IsabContinue (Term (OtherType SingleBagIsab) SingleCellAsBag [VarTerm (OtherType CellType)
        newVara]),  IsabGood (Term (OtherType SingleBagIsab) SingleCellAsBag
           [VarTerm (OtherType CellType) newVarb])),
     (BagRuleInduct (OtherType SingleBagIsab), newVarc,
     [AppFun (BagRuleInduct (OtherType CellType)) [IsabContinue (VarTerm (OtherType CellType)
    newVara), IsabGood (VarTerm (OtherType CellType) newVarb)]],
    IsabContinue (Term (OtherType SingleBagIsab) OptionCellAsBag [IsabSome (VarTerm (OtherType CellType)
        newVara)]),  IsabGood (Term (OtherType SingleBagIsab) OptionCellAsBag
           [IsabSome (VarTerm (OtherType CellType) newVarb)])),
   (BagRuleInduct (OtherType SingleBagIsab), newVard,
     [AppFun (BagRuleInduct (IsabList (OtherType CellConType)))
    [IsabContinue (VarTerm (IsabList (OtherType CellConType)) newVara),
          IsabGood (VarTerm (IsabList (OtherType CellConType)) newVarb)]],
    IsabContinue (Term (OtherType SingleBagIsab) StarCellAsBag
  [(VarTerm (OtherType CellNameType) newVare), (VarTerm (IsabList (OtherType CellConType)) newVara)]),
   IsabGood (Term (OtherType SingleBagIsab) StarCellAsBag [(VarTerm (OtherType CellNameType)
    newVare), (VarTerm (IsabList (OtherType CellConType)) newVarb)]))])))))))"

definition allBagRuleInductBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"allBagRuleInductBodies = (case bagRuleInductBodiesDef [] of None \<Rightarrow> []
      | Some (S,l) \<Rightarrow> (case bagRuleCellTypeBody S of (S', l') \<Rightarrow> 
    (case bagRuleCellConTypesBody S' of (Sa, la) \<Rightarrow> (case bagRuleSingleBagBody Sa
    of (Sb, lb) \<Rightarrow> (l@l'@la@lb)))))"

definition topRuleHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
        * 'tVar kType isabType list * 'tVar kType isabType)" where
"topRuleHeader = (TopRule, [IsabState (IsabList (OtherType SingleBagIsab))
     (IsabList (OtherType SingleBagIsab)), IsabState (IsabList (OtherType SingleBagIsab))
     (IsabList (OtherType SingleBagIsab))], BoolIsab)"

definition topRuleBody :: "(('cVar, 'tVar kType isabType, 'var) kConstr
      * 'iVar * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm list * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm * ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
  'iVar) isabTerm) list" where
"topRuleBody = (case freshIVar [IVarOne,IVarTwo,IVarThree] of newVar \<Rightarrow>
  (case freshIVar [IVarOne,IVarTwo,IVarThree, newVar] of newVara \<Rightarrow>
  (case freshIVar [IVarOne,IVarTwo,IVarThree, newVar,newVara] of newVarb \<Rightarrow>
    (if funInductDef = [] then [] else
        [(TopRule, IVarOne, [AppFun (HasFunConstr (IsabList
           (OtherType SingleBagIsab))) [(VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo)], AppFun (FunRuleInduct (IsabList
           (OtherType SingleBagIsab))) [IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree)]], IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree))])
    @(if allAnywhereBodies = [] then [] else [(TopRule, newVar,
        ((if funInductDef = [] then [] else [IsabNot (AppFun (HasFunConstr (IsabList
           (OtherType SingleBagIsab))) [(VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo)])])@
         [AppFun AnywhereSeq [IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree)]]), IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree))])
    @([(TopRule, newVara,
        ((if funInductDef = [] then [] else [IsabNot (AppFun (HasFunConstr (IsabList
           (OtherType SingleBagIsab))) [(VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarOne)])])@
        (if allAnywhereBodies = [] then [] else [IsabNot (IsabExist newVarb (IsabList
           (OtherType SingleBagIsab)) (AppFun AnywhereSeq [IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarOne), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) newVarb)]))])@
         [AppFun (BuiltInFunConstr Congruence (IsabList (OtherType SingleBagIsab)))
         [(VarTerm (IsabList (OtherType SingleBagIsab)) IVarOne), (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarTwo)], AppFun (BagRuleInduct
                 (IsabList (OtherType SingleBagIsab)))
         [IsabContinue (VarTerm (IsabList (OtherType SingleBagIsab)) IVarTwo),
           IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree)]]), IsabContinue (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarOne), IsabGood (VarTerm (IsabList
           (OtherType SingleBagIsab)) IVarThree))]))))"


end

end