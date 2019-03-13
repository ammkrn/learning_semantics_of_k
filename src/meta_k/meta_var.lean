import .meta_sort


-- #############################################
-- #####    meta_variable    ###################

@[derive decidable_eq]
inductive meta_variable : Type
| mk : #String → #Sort → meta_variable

instance : inhabited meta_variable := 
    inhabited.mk (meta_variable.mk ("default_#Variable") (%Sort))

notation `#Variable` := meta_variable
notation `#variable` := meta_variable.mk
notation `#VariableList` := list meta_variable

definition meta_variable_get_sort : meta_variable → meta_sort
| (meta_variable.mk (str) (s)) := s

instance meta_variable.has_sort : has_sort meta_variable meta_sort := ⟨ meta_variable_get_sort ⟩ 

definition meta_variable_to_string : meta_variable → string
| (meta_variable.mk (str) (sort))  := (repr str) ++ " : " ++ (repr (meta_sort_name sort))

definition get_meta_variable_name : meta_variable → string
| (meta_variable.mk (str) (sort))  := (repr str) 

instance : has_name meta_variable := ⟨ get_meta_variable_name ⟩ 

instance meta_variableiable.is_Variable : is_Variable meta_variable := ⟨ meta_variable_to_string ⟩ 

-- ########## Coercions/lifts

def meta_variable.to_meta_sort : #Variable → #Sort := λ v : #Variable, %Variable
instance meta_variable_to_meta_sort_lift : has_lift meta_variable #Sort := ⟨ meta_variable.to_meta_sort ⟩ 

instance : has_repr meta_variable := has_repr.mk (meta_variable_to_string)

def meta_sort.to_meta_variable : #Sort → #Variable
| s := #variable (meta_sort_name s) s

instance meta_sort_to_meta_variable_lift : has_lift #Sort #Variable := ⟨ meta_sort.to_meta_variable ⟩


def delete_variable_list {V : Type} [is_Variable V] [decidable_eq V]: V → list V → list V
| v [] := []
| v (hd :: tl) := if v = hd then delete_variable_list v tl else hd :: (delete_variable_list v tl)