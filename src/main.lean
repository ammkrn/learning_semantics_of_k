import meta_k.meta_sort
import meta_k.meta_var
import meta_k.meta_symbol
import meta_k.meta_pattern
import object_k.object_symbol
import object_k.object_pattern
import meta_k.sort_schemas
import meta_k.symbol_schemas


/-

This file contains a definition of the 'working example' matching logic
theory described in chapter 8 of the "Semantics of K" document for illustration
purposes. 
Notation used that differs from that in the document is
1) the use of tilde (~) as a prefix for object theory elements (like # for meta)m
2) the ↑ up arrow is used to cast one type into another in a way that
    is explicit. Matching Logic is based on many-sorted logic, and there are 
    implicit transofrmations happening all over the place, which is daunting for
    the uninitiated, so I've made them explicit lifts instead of implicit coercions.
3) The modified logical connective notation corresponds to its matching logic pattern
   counterpart. IE #∧ is the #and pattern, ~s~> is implication parameterized by sort s, etc.

For the purposes of chapter 8, the definition of T here can just be thought of as the
items in scope. 
The constructions and lifting used in chapters 7 and 8 are also surprisingly different
from thos used in Kore; Symbols become 'head' objects, pattern constructions are all
made into independent production rules, and they object pattern/meta pattern constructors
are parametric across all patterns, and the lifting process between object theory 
elements and meta theory elements is altered.

-/


-- object sort definition of Nat
def Nat : object_sort := ~sort ⟨"Nat"⟩ ~nilSortList

-- object sort definition of List{Nat}
def List_Nat : object_sort := ~sort ⟨"List"⟩ ↑[~sort ⟨"Nat"⟩ ~nilSortList]


-- specification of lift for sorts as defined in 8.3
mutual def lift_object_sort, lift_object_sort_list 
with lift_object_sort : object_sort → meta_sort 
| (object_sort.mk ident object_sort_list.nil) := #sort (repr ident) #nilSortList
| (object_sort.mk ident L) := #sort (repr ident) (lift_object_sort_list L)
with lift_object_sort_list : object_sort_list → meta_sort_list
| (object_sort_list.nil) := #nilSortList
| (object_sort_list.cons hd tl) := #consSortList (lift_object_sort hd) (lift_object_sort_list tl)

instance : has_lift object_sort meta_sort := ⟨ lift_object_sort ⟩ 
instance : has_lift object_sort_list meta_sort_list := ⟨ lift_object_sort_list ⟩ 

def meta_Nat : meta_sort := ↑Nat
def meta_List_Nat : meta_sort := ↑List_Nat

-- evaluation of lifting process from 8.3 on Nat and List_Nat; VM evaluation
-- will show that they come out to
-- #sort "Nat" ε
-- #sort "List" [#sort "Nat" ε]
-- respectively
#eval meta_Nat
#eval meta_List_Nat


-- The literal definition of the sort helper functions for #'Nat and #'List
-- given in 8.3 would be these two functions.
def nat_meta_rep : #Sort := #sort "Nat" #nilSortList
notation `#'Nat` := nat_meta_rep

def list_meta_rep : #Sort → #Sort 
| s := #sort "List" ↑[s]
notation `#'List` := list_meta_rep

-- The axioms which define them intensionally in matching logic would be as follows,
-- so we add these patterns to our theory T.
def nat_constructor_axiom : #Pattern := 
    let s1 := #'Nat,
        s2 := #sort "Nat" #nilSortList
    in (↑s1 #= (s1, s2); ↑s2)

def list_constructor_axiom {carrier s : #Sort} : #Pattern :=
   let s1 := #'List s,
       s2 := #sort "List" ↑[s]
    in #∀carrier, "s" : %Sort . (↑s1) #= (s1, s2); (↑s2)


-- axiom schema about definedness of list parameters; for any sort s,
-- if s is defined in the current theory, that implies that the sort List s
-- is therefore defined.
def list_axiom_schema {carrier s : #Sort} {L : #SortList}: #Pattern :=
    #∀carrier, "s" : %Sort . 
        (#apply (#symbol "sortDeclared" [%Sort] [%Sort, %SortList] %Sort) . [↑s, ↑L])
        ~carrier~> 
        (#apply (#symbol "sortDeclared" [%Sort] [%Sort, %SortList] %Sort) . [↑(#'List s), ↑L])


-- Generic function to lift object symbol declarations into meta theory
-- based on specification in chapter 8. Uses already defined lifts for sort.
def object_symbol_lift_to_meta : object_symbol → meta_symbol
| (~symbol ident params args ret) := 
    #symbol (name_fn ident) ↑params ↑args ↑ret

instance : has_lift object_symbol meta_symbol := ⟨ object_symbol_lift_to_meta ⟩ 

def object_nat_zero : ~Symbol := ~symbol "O" [] [] Nat
def meta_nat_zero : #Symbol := #symbol "zero" [] [] #'Nat
notation `~O` := object_nat_zero

-- definition of object theory's 'zero' symbol in meta theory
-- is as follows; #eval shows that the version produced by the 
-- lifting function is identical.
def zeros_eq : bool := ↑object_nat_zero = meta_nat_zero
#eval zeros_eq


def object_nat_succ : ~Symbol := ~symbol "succ" [] [Nat] Nat
def meta_nat_succ : #Symbol := #symbol "succ" [] [#'Nat] #'Nat

def succs_eq : bool := ↑object_nat_succ = meta_nat_succ
#eval succs_eq

def object_nat_plus : ~Symbol := ~symbol "+" [] [Nat, Nat] Nat
def meta_nat_plus : #Symbol := #symbol "plus" [] [#'Nat, #'Nat] #'Nat
notation `~+` := object_nat_plus

def pluses_eq : bool := ↑object_nat_plus = meta_nat_plus
#eval pluses_eq

def object_list_nat_nil : ~Symbol := ~symbol "ε" [Nat] [] (List_Nat)
def meta_list_nat_nil : #Symbol := #symbol "nil" [#'Nat] [] (#'List(#'Nat))

def nils_eq : bool := ↑object_list_nat_nil = meta_list_nat_nil
#eval nils_eq

def object_list_nat_cons : ~Symbol := ~symbol "::" [Nat] [Nat, List_Nat] (List_Nat)
def meta_list_nat_cons : #Symbol := #symbol "cons" [#'Nat] [#'Nat, #'List(#'Nat)] (#'List(#'Nat))

-- parametric list symbols
def meta_list_nil : #Sort → #Symbol
| s := #symbol "nil" [%Sort] [] (#'List s)
notation `#'nil` := meta_list_nil

def meta_list_cons : #Sort → #Symbol
| s := #symbol "cons" [%Sort] [s, #'List s] (#'List s)
notation `#'cons` := meta_list_cons

def meta_list_append : #Sort → #Symbol
| s := #symbol "append" [%Sort] [#'List s, #'List s] (#'List s)
notation `#'append` := meta_list_append

def cons_eq : bool := ↑object_list_nat_cons = meta_list_nat_cons
#eval cons_eq


def object_list_nat_append : ~Symbol := ~symbol "@" [Nat] [List_Nat, List_Nat] (List_Nat)
def meta_list_nat_append : #Symbol := #symbol "append" [#'Nat] [#'List(#'Nat), #'List(#'Nat)] (#'List(#'Nat))
notation `#'append` := meta_list_nat_append

def append_eq : bool := ↑object_list_nat_append = meta_list_nat_append
#eval append_eq

def symbol_declared_pred {s : #Sort} := #symbol "symbolDeclared" [%Sort] [%Symbol, %SymbolList] %Pattern
def sort_declared_pred   {s : #Sort} := #symbol "sortDeclared" [%Sort] [%Sort, %SortList] %Pattern
def sorts_declared_pred  {s : #Sort} := #symbol "sortsDeclared" [%Sort] [%SortList, %SortList] %Pattern
def axiom_declared_pred  {s : #Sort} := #symbol "axiomDeclared" [%Sort] [%Pattern, %PatternList] %Pattern

-- for any #s : Sort in T, the meta representation of the nat zero symbol
-- is declared, but not for any other sorts.
-- object_nat_zero gets lifted to meta_symbol, then to meta_pattern to
-- satisfy the specification.
def non_parametric_axiom1 {«#s» : #Sort} {L : #SymbolList }: #Pattern :=
    #apply (@symbol_declared_pred «#s») . [↑object_nat_zero, ↑L]

-- for any #s : Sort in T, the meta representation of succ is declared,
-- but not for any others.
def non_parametric_axiom2 {«#s» : #Sort} {L : #SymbolList} : #Pattern := 
    #apply (@symbol_declared_pred «#s»)  . [↑object_nat_succ, ↑L]

def non_parametric_axiom3 {«#s» : #Sort} {L : #SymbolList} : #Pattern := 
    #apply (@symbol_declared_pred «#s»)  . [↑object_nat_plus, ↑L]

def parametric_axiom1 {«#s» s  : #Sort} {LS : #SortList} {LSy : #SymbolList} : #Pattern :=
    (#apply (@sort_declared_pred «#s») . [↑s, ↑LS])
    ~s~> 
    (#apply (@symbol_declared_pred «#s») . [↑object_list_nat_nil, ↑LSy])

def parametric_axiom2 {«#s» s : #Sort} {LS : #SortList} {LSy : #SymbolList} : #Pattern :=
    (#apply (@sort_declared_pred «#s») . [↑s, ↑LS])
    ~s~> 
    (#apply (@symbol_declared_pred «#s») . [↑object_list_nat_cons, ↑LSy])

def parametric_axiom3 {«#s» s : #Sort} {LS : #SortList} {LSy : #SymbolList} : #Pattern :=
    (#apply (@sort_declared_pred «#s») . [↑s, ↑LS])
    ~s~> 
    (#apply (@symbol_declared_pred «#s») . [↑object_list_nat_append, ↑LSy])


def object_variable_lift_meta : ~Variable → #Variable
| (~variable ident s) := #variable (name_fn ident) (↑s)

instance : has_lift object_variable meta_variable := ⟨ object_variable_lift_meta ⟩ 

open object_pattern
open meta_pattern

mutual def object_pattern_lift_meta, object_pattern_list_lift_meta 
with object_pattern_lift_meta : ~Pattern → #Pattern
| (~variableAsPattern v) := #variableAsPattern ↑v
| (object_application σ L) := #apply ↑σ  . (object_pattern_list_lift_meta L)
| (object_and s φ1 φ2) := meta_and ↑s (object_pattern_lift_meta φ1) (object_pattern_lift_meta φ2)
| (object_not s φ) := meta_not ↑s (object_pattern_lift_meta φ)
| (object_exsts s v φ) := meta_exsts ↑s ↑v (object_pattern_lift_meta φ)
with object_pattern_list_lift_meta : ~PatternList → #PatternList
| [] := []
| (hd :: tl) := object_pattern_lift_meta hd :: (object_pattern_list_lift_meta tl)

instance object_pattern_to_meta_pattern_lift : has_lift object_pattern meta_pattern := ⟨ object_pattern_lift_meta ⟩ 

def object_nat_var : ~Variable := ⟨ "x", Nat ⟩ 
def meta_nat_var : #Variable := ⟨ "x", #'Nat ⟩ 
#eval ((((↑object_nat_var) : #Pattern) = (↑meta_nat_var))  : bool)


-- for any x : Nat, x + O is equal to x
-- extremely verbose version to clarify what's going on.
def object_aux_axiom1_verbose {c s' : ~Sort} : ~Pattern :=
    ~∀c, "x" : Nat . ((~apply (~symbol "+" [] [Nat, Nat] Nat) . [(~variableAsPattern ⟨"x", Nat⟩), ↑(~symbol "O" [] [] Nat)]) ~= (Nat, s'); (~variableAsPattern ⟨"x", Nat⟩))

-- more comfortable version
def object_aux_axiom1 {c s' : ~Sort} : ~Pattern :=
    let x : ~Variable := ⟨ "x", Nat ⟩
    in ~∀c, x . ((~apply ~+ . [↑x, ↑~O]) ~= (Nat, s'); (↑x))

def meta_aux_axiom1 {c s' : #Sort} : #Pattern :=
    let x : #Variable := #variable "x" #'Nat
    in #∀c, x . ((#apply meta_nat_plus . [↑x, ↑meta_nat_zero]) #= (#'Nat, s'); (↑x))

def a_lift : #Pattern := ↑(@object_aux_axiom1 object_sort.inhabited.default object_sort.inhabited.default)
#eval a_lift 


-- example of naming helper functions given on p. 49-50, allowing
-- #'zero to be used in place of the longer 'raw' representation
def «#'zero» : #Symbol := #symbol "zero" [] [] #'Nat
def zero_axiom {«#s» : #Sort} : #Pattern := 
    ↑«#'zero» #= (#'Nat, «#s»); #apply (#symbol "zero" [] [] #'Nat) . []


def «#'nil» : #Sort → #Symbol 
| s := #symbol "nil" [%Sort] [] s

def nil_axiom {«#s» : #Sort} : #Sort → #Pattern
| s' := #∀«#s», "s'" : s' . ↑(«#'nil» s') #= (s', «#s»); #apply (#symbol "nil" [%Sort] [] s') . []

def Ψ1 {s' : #Sort} : #Pattern :=
    (#apply (#symbol "#'plus" [] [#'Nat, #'Nat] #'Nat) . [#variableAsPattern ⟨ "x", #'Nat⟩, ↑«#'zero»]) 
    #= (#'Nat, s'); 
    (#variableAsPattern ⟨ "x", #'Nat ⟩)

-- append(s) (x :: L0) (L) == x :: (L0 ++ L)
def Ψ2 {s s' : #Sort} : #Pattern :=
    (#apply (#'append s) . [(#apply (#'cons s) . [#variableAsPattern ⟨"L0", (#'List s)⟩]), (#variableAsPattern ⟨"L", (#'List s)⟩) ])
    #= (#'List s, s');
    (#apply (#'cons s) . [(#apply (#'append s) . [#variableAsPattern ⟨"L0", (#'List s)⟩, #variableAsPattern ⟨"L", (#'List s)⟩]) ])

def axiom_Ψ1 {«#s» s s' : #Sort} {Ss : #SortList} {φs : #PatternList} : #Pattern :=
    #∀«#s», "s'" : %Sort . (#apply (@sort_declared_pred «#s») . [↑s'])
    ~«#s»~> 
    (#apply (@axiom_declared_pred «#s») . [@Ψ1 s'])
    
def axiom_Ψ2 {«#s» s s' : #Sort} {Ss : #SortList} {φs : #PatternList} : #Pattern :=
    #∀«#s», "s'" : %Sort . ((#apply (@sort_declared_pred «#s») . [↑s]) 
                            #∧(s'); (#apply (@sort_declared_pred «#s») . [↑s']))
                            ~«#s»~> 
                            (#apply (@axiom_declared_pred «#s») . [@Ψ2 s s'])



    

       