import .object_sort
import meta_k.meta_sort


-- ##########################################
-- #####    object_variable    ##############

@[derive decidable_eq]
inductive object_variable : Type
| mk : string → object_sort → object_variable

open object_variable

notation `~Variable` := object_variable
notation `~VariableList` := list object_variable
notation `~variable` := object_variable.mk 

definition object_variable_get_sort : object_variable → object_sort
| (object_variable.mk (str) (s)) := s

instance object_variable.has_sort : has_sort object_variable object_sort := ⟨ object_variable_get_sort ⟩ 


definition object_var_to_string : object_variable → string
| (object_variable.mk (str) (sort))  := (repr str) ++ " : " ++ (repr (object_sort_get_name sort))

definition object_var_get_name : object_variable → string
| (object_variable.mk (str) (sort))  := (str) 

instance : has_name object_variable := ⟨ object_var_get_name ⟩ 

instance : has_repr object_variable := has_repr.mk (object_var_to_string)

def object_sort.to_object_variable : object_sort → ~Variable
| s := mk (object_sort_get_name s) s

instance object_sort_to_object_var_lift : has_lift object_sort ~Variable := ⟨ object_sort.to_object_variable ⟩

instance object_variable.is_Variable : is_Variable object_variable := ⟨ object_var_get_name ⟩ 
