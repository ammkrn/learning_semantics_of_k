import .meta_sort
import .meta_var

-- ###########################################
-- #####    meta_symbol    ###################


@[derive decidable_eq]
inductive meta_symbol 
| mk : string → #SortList  → #SortList → #Sort → meta_symbol

notation `#Symbol` := meta_symbol
notation `#symbol` := meta_symbol.mk
notation `#SymbolList` := list #Symbol

instance : inhabited #Symbol := ⟨ (#symbol ("default #Symbol") [] [] %Symbol) ⟩ 

open meta_symbol

def meta_symbol_get_name : #Symbol → string
| (#symbol n p a r) := n

instance : has_name meta_symbol := ⟨ meta_symbol_get_name ⟩ 

def meta_symbol_get_argument_sorts : #Symbol → #SortList
| (meta_symbol.mk n p a r) := a

def meta_symbol_get_return_sort : #Symbol → #Sort
| (#symbol n p a r) := r

instance meta_symbol.has_sort : has_sort meta_symbol meta_sort := ⟨ meta_symbol_get_return_sort ⟩


instance : is_Symbol meta_symbol := 
    ⟨ #Sort, (meta_symbol_get_argument_sorts), (meta_symbol_get_return_sort) ⟩ 


definition meta_symbol_to_string : meta_symbol → string
| (meta_symbol.mk n p a r) := "#σ: " ++ (repr n) ++ " " ++ repr p ++ " " ++ repr a ++ " → (" ++ repr r ++ ")"

instance meta_symbol.has_repr : has_repr meta_symbol := has_repr.mk meta_symbol_to_string

definition meta_beq_symbol : meta_symbol → meta_symbol → bool
| σ1 σ2 := σ1 = σ2

--  ############### Coercions/lifts

def meta_symbol.to_meta_sort : #Symbol → #Sort          := λ σ : #Symbol, #sort "#Symbol" #ε 
def meta_symbol_list.to_meta_sort : #SymbolList → #Sort := λ L : #SymbolList, #sort "#SymbolList" #ε

def meta_sort.to_meta_symbol : #Sort → #Symbol 
| (meta_sort.mk str #nilSortList) := #symbol str [] [] %Sort
| (meta_sort.mk str L) := #symbol str [] ↑L %Sort

instance meta_symbol_to_meta_sort_lift : has_lift #Symbol #Sort := ⟨ meta_symbol.to_meta_sort ⟩ 
instance meta_symbol_list_to_meta_sort_lift : has_lift #SymbolList #Sort := ⟨ meta_symbol_list.to_meta_sort ⟩ 
instance meta_sort_to_meta_symbol_lift : has_lift #Sort #Symbol := ⟨ meta_sort.to_meta_symbol ⟩ 
