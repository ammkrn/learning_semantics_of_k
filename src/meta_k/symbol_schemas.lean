import .meta_sort
import .meta_symbol
import .meta_pattern
import .sort_schemas

-- nil{s} ∈ Σ *, List{S}
def List_nil : #Sort → #Symbol 
| s := #symbol "nil" [s] [] (List s)

def List_cons : #Sort → #Symbol
| s := #symbol "cons" [s] [s, List s] (List s)

def List_append : #Sort → #Symbol
| s := ⟨ "append", [s], [List s, List s], (List s) ⟩ 
--| s := #symbol "append" [s] [List s, List s] (List s)


def empty_map : #Sort → #Sort → #Symbol
| s s' := ⟨ "empty_map", [s, s'], [], (Map s s') ⟩

def bind_map : #Sort → #Sort → #Symbol
| s s' := ⟨ "bind_map", [s, s'], [s, s', Map s s'], (Map s s') ⟩

def merge_map : #Sort → #Sort → #Symbol
| s s' := ⟨ "merge_map", [s, s'], [s, s', Map s s', Map s s'], (Map s s') ⟩
