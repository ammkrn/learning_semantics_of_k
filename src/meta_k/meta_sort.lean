open nat

-- #########################################################
-- #####    meta-sort    ########################################

instance {α : Type*} [has_repr α] : has_repr (id α) := by dsimp; apply_instance

class has_name (α : Type) :=
(get_name : α → string)

notation `getName` := has_name.get_name

class is_Sort (α : Type) :=
(get_sort_params : α → list α)

notation `getSortParameters` := is_Sort.get_sort_params

class has_sort (α : Type) (S : out_param Type) [out_param (is_Sort S)] :=
(get_sort : α → S)

notation `getSort` := has_sort.get_sort

class is_Variable (V : Type) :=
(witness : V → string)

class is_Symbol (σ : Type) :=
(S : Type) [S_ : is_Sort S]
(get_argument_sorts : σ → list S) 
(get_return_sort : σ → S) 

notation `getArgumentSorts` := is_Symbol.get_argument_sorts
notation `getReturnSort` := is_Symbol.get_return_sorts

class is_Pattern (φ : Type) :=
(V : Type) [V_ : is_Variable V]
(S : Type) [S_ : is_Sort S]
(isTop : φ → bool)
(isBottom : φ → bool)
(getFV : φ → list V)
(getFVFromPatterns : list φ → list V)
(occursFree : S → V → φ → φ)
(BtoP : bool → (S → φ))
(sc : S → φ → φ → φ)
(sc_l : S → φ → list φ → φ)
(freshName : list φ → string)
(substitute_i : φ → φ → V → option φ)

notation `#String` := string

inductive meta_sort_variable 
| mk : string → meta_sort_variable

mutual inductive meta_sort, meta_sort_list
with meta_sort : Type
| mk : string → meta_sort_list → meta_sort
with meta_sort_list : Type
| nil : meta_sort_list
| cons : meta_sort → meta_sort_list → meta_sort_list


open meta_sort
open meta_sort_list

def meta_sort_list.to_list_meta_sort : meta_sort_list → list meta_sort 
| nil := [] 
| (cons hd tl) := hd :: (meta_sort_list.to_list_meta_sort tl)

def list_meta_sort.to_meta_sort_list : list meta_sort → meta_sort_list 
| [] := meta_sort_list.nil
| (hd :: tl) := cons hd (list_meta_sort.to_meta_sort_list tl)

instance meta_sort_list_to_list_meta_sort_lift : 
   has_lift meta_sort_list (list meta_sort) := 
   ⟨ meta_sort_list.to_list_meta_sort ⟩

instance list_meta_sort_to_meta_sort_list : 
   has_lift (list meta_sort) (meta_sort_list) := 
   ⟨ list_meta_sort.to_meta_sort_list ⟩

instance : decidable_eq meta_sort_variable :=
by tactic.mk_dec_eq_instance

instance : decidable_eq meta_sort :=
by tactic.mk_dec_eq_instance

instance : decidable_eq meta_sort_list :=
by tactic.mk_dec_eq_instance


notation `#Sort` := meta_sort
notation `#SortList` := list meta_sort
notation `#sort` := meta_sort.mk
notation `#ε` := meta_sort_list.nil
notation `#nilSortList` :=  (meta_sort_list.nil)
notation `#consSortList` := (meta_sort_list.cons)

def meta_sort_variable.to_string : meta_sort_variable → string
| (meta_sort_variable.mk str) := str

instance : has_repr meta_sort_variable := ⟨ meta_sort_variable.to_string ⟩ 

mutual def meta_sort_to_string, meta_sort_list_to_string
with meta_sort_to_string : meta_sort → string
| (#sort str L) := "#Sort : (" ++ repr str ++ ", " ++ (meta_sort_list_to_string L) ++ "), "
with meta_sort_list_to_string : meta_sort_list → string
| (meta_sort_list.nil) := "#sort_ε"
| (meta_sort_list.cons s l) := meta_sort_to_string s ++ meta_sort_list_to_string l

def pretty_meta_sort_list_to_string : meta_sort_list → string
| meta_sort_list.nil := ""
| l := "[" ++ string.popn_back (meta_sort_list_to_string l) 7 ++ "]"           

instance : has_repr meta_sort_list := ⟨ pretty_meta_sort_list_to_string ⟩ 

def pretty_meta_sort_to_string : meta_sort → string
| (#sort str meta_sort_list.nil) := (repr str) ++ " #ε"
| (#sort str L) := "#sort " ++ (repr str) ++ " : " ++ repr L

instance : has_repr meta_sort := ⟨ pretty_meta_sort_to_string ⟩ 

def meta_sort_name : meta_sort → string
| (#sort a b) := a

def meta_sort_list_name : meta_sort_list → string
| (meta_sort_list.nil) := ""
| (meta_sort_list.cons s l) := meta_sort_name s

def meta_sort_params : meta_sort → meta_sort_list
| (#sort a b) := b

def meta_sort_params_for_class : meta_sort → list meta_sort
| (#sort a b) := (lift b)


instance : is_Sort meta_sort := ⟨ meta_sort_params_for_class ⟩


-- This cannot be implemented as a lift, since the items being
-- converted are going from type land to value land.

def meta_sort_sort : #Sort := #sort "#Sort" #ε
def meta_sort_sort_list : #Sort := #sort "#SortList" #ε
def meta_sort_var : #Sort := #sort "#Variable" #ε
def meta_sort_var_list : #Sort := #sort "#VariableList" #ε
def meta_sort_symbol : #Sort := #sort "#Symbol" #ε
def meta_sort_symbol_list : #Sort := #sort "#SymbolList" #ε
def meta_sort_pattern : #Sort := #sort "#Pattern" #ε
def meta_sort_pattern_list : #Sort := #sort "#PatternList" #ε
def meta_sort_char : #Sort := #sort "#Char" #ε
def meta_sort_char_list : #Sort := #sort "#CharList" #ε
def meta_sort_string : #Sort := #sort "#String" #ε


notation `%Sort` := meta_sort_sort
notation `%SortList` := meta_sort_sort_list
notation `%Variable` := meta_sort_var
notation `%VariableList` := meta_sort_var_list
notation `%Symbol` := meta_sort_symbol
notation `%SymbolList` := meta_sort_symbol_list
notation `%Pattern` := meta_sort_pattern
notation `%PatternList` := meta_sort_pattern_list
notation `%Char` := meta_sort_char
notation `%CharList` := meta_sort_char_list
notation `%String` := meta_sort_string


-- ############ Coercions/Lifts

@[reducible]
def meta_sort_list.to_meta_sort : #SortList → #Sort
| L := #sort "#SortList" (lift L)

instance meta_sort_list_to_meta_sort_lift : has_lift #SortList #Sort := ⟨ meta_sort_list.to_meta_sort ⟩ 


def Sₖ : list #Sort := [ 
    %Sort,
    %SortList,
    %Variable,
    %VariableList,
    %Symbol,
    %SymbolList,
    %Pattern,
    %PatternList,
    %Char,
    %CharList,
    %String
]

def delete_sort_list {S : Type} [is_Sort S] [decidable_eq S]: S → list S → list S
| s [] := []
| s (hd :: tl) := if s = hd then delete_sort_list s tl else hd :: delete_sort_list s tl




