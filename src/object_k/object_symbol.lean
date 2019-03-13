import .object_sort
import .object_var
import meta_k.meta_symbol

-- ############################################
-- #####    object_symbol    ##################


@[derive decidable_eq]
inductive object_symbol 
| mk : string → list object_sort  → list object_sort → object_sort → object_symbol

notation `~Symbol` := object_symbol
notation `~symbol` := object_symbol.mk
notation `~SymbolList` := list ~Symbol

open object_symbol

def object_symbol_get_name : ~Symbol → string
| (mk n p a r) := n

def object_symbol_get_argument_sorts : ~Symbol → list object_sort
| (object_symbol.mk n p a r) := a

def object_symbol_get_return_sort : ~Symbol → object_sort
| (mk n p a r) := r

instance object_symbol.has_name : has_name object_symbol := ⟨ object_symbol_get_name ⟩ 

instance object_symbol.is_Symbol : is_Symbol object_symbol := ⟨ object_sort, object_symbol_get_argument_sorts, object_symbol_get_return_sort ⟩ 

instance object_symbol.has_sort : has_sort object_symbol object_sort := ⟨ object_symbol_get_return_sort ⟩ 

definition object_symbol_to_string : object_symbol → string
| (object_symbol.mk n p a r) := "~Symbol; " ++ (repr n) ++ ". (" ++ repr p ++ ", " ++ repr a ++ ") : " ++ repr r

instance object_symbol.has_repr : has_repr object_symbol := has_repr.mk object_symbol_to_string

definition object_beq_symbol : object_symbol → object_symbol → bool
| σ1 σ2 := σ1 = σ2

def object_symbol.to_object_sort : object_symbol → object_sort          := λ σ : ~Symbol, object_sort.mk ⟨ "~Symbol" ⟩  (object_sort_list.nil)


