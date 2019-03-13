import meta_k.meta_sort
import meta_k.meta_pattern
import meta_k.meta_symbol

@[reducible]
def object_identifier := string

inductive object_sort_constructor
| mk : object_identifier → object_sort_constructor

inductive object_sort_variable
| mk : object_identifier → object_sort_variable

mutual inductive object_sort, object_sort_list
with object_sort : Type 
| mk : object_sort_constructor → object_sort_list → object_sort
with object_sort_list : Type
| nil : object_sort_list
| cons : object_sort → object_sort_list → object_sort_list

open object_sort_constructor
open object_sort_variable
open object_sort
open object_sort_list

instance : decidable_eq object_sort_constructor := by tactic.mk_dec_eq_instance
instance : decidable_eq object_sort_variable := by tactic.mk_dec_eq_instance

instance : decidable_eq object_sort := by tactic.mk_dec_eq_instance
instance : decidable_eq object_sort_list := by tactic.mk_dec_eq_instance

def object_sort_constructor.to_string : object_sort_constructor → string
| (mk str) := str

def object_sort_variable.to_string : object_sort_variable → string
| (mk str) := str

instance : has_repr object_sort_constructor := ⟨ object_sort_constructor.to_string ⟩ 
instance : has_repr object_sort_variable := ⟨ object_sort_variable.to_string ⟩

-- #########################


notation `~Sort` := object_sort
notation `~SortList` := list object_sort
notation `~nilSortList` := object_sort_list.nil
notation `~consSortList` := object_sort_list.cons
notation `~sort` := object_sort.mk

class object_has_sort (α : Type) :=
(get_sort : α → object_sort)

def object_sort_list.to_list_object_sort : object_sort_list → ~SortList
| nil := [] 
| (cons hd tl) := hd :: (object_sort_list.to_list_object_sort tl)


mutual def object_sort_to_string, object_sort_list_to_string
with object_sort_to_string : object_sort → string
| (object_sort.mk ident L) := "Sort : (" ++ repr ident ++ ", " ++ (object_sort_list_to_string L) ++ "), "
with object_sort_list_to_string : object_sort_list → string
| (object_sort_list.nil) := "sort_ε"
| (object_sort_list.cons s l) := object_sort_to_string s ++ object_sort_list_to_string l

def pretty_object_sort_list_to_string : object_sort_list → string
| object_sort_list.nil := ""
| l := "[" ++ string.popn_back (object_sort_list_to_string l) 7 ++ "]"           

instance : has_repr object_sort_list := ⟨ pretty_object_sort_list_to_string ⟩ 

def pretty_object_sort_to_string : object_sort → string
| (object_sort.mk ident object_sort_list.nil) := (repr ident)
| (object_sort.mk ident L) := (repr ident) ++ " : " ++ repr L

def object_sort_get_name : object_sort → string
| (object_sort.mk ident _) := (repr ident)

instance : has_repr object_sort := ⟨ pretty_object_sort_to_string ⟩ 

def list_object_sort.to_object_sort_list : ~SortList → object_sort_list
| [] := object_sort_list.nil
| (hd :: tl) := object_sort_list.cons hd (list_object_sort.to_object_sort_list tl)

instance object_sort_list_to_list_object_sort_lift : 
  has_lift object_sort_list (list object_sort) := 
  ⟨ object_sort_list.to_list_object_sort ⟩ 

instance list_object_sort_to_object_sort_list_lift : 
  has_lift (list object_sort) (object_sort_list) := 
  ⟨ list_object_sort.to_object_sort_list ⟩ 


def object_sort_params_for_class : object_sort → ~SortList
| (object_sort.mk ident L) := lift L

instance : is_Sort object_sort := ⟨ object_sort_params_for_class ⟩

instance : inhabited object_sort := ⟨ object_sort.mk ⟨"Nat"⟩ ~nilSortList ⟩ 



def name_fn : string → string
| "O" := "zero"
| "S" := "succ"
| "+" := "plus"
| "ε" := "nil"
| "::" := "cons"
| "@" := "append"
| s := s