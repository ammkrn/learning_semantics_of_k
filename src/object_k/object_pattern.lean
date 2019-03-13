import object_k.object_sort
import .object_sort
import .object_var
import .object_symbol
import term_lemmas

open nat
open has_sort

-- #########################################################
-- #####    object_pattern    ##############################

inductive object_pattern : Type
| object_variable_as_pattern : ~Variable → object_pattern
-- ??
| object_application : ~Symbol → list object_pattern → object_pattern
| object_and : object_sort → object_pattern → object_pattern → object_pattern
| object_not : object_sort → object_pattern → object_pattern
| object_exsts : object_sort → ~Variable → object_pattern → object_pattern

instance : decidable_eq object_pattern :=
by tactic.mk_dec_eq_instance

open object_pattern

notation `~Pattern` := object_pattern
notation `~variableAsPattern` := object_variable_as_pattern
notation `~PatternList` := list object_pattern

notation φ `~∧` s `;`  ψ := object_and s φ ψ 

notation `~apply` σ . L := object_application σ L
notation `~∃` s `,` v `:`s `.` φ := object_exsts s (object_variable.mk v s) φ
notation `~∃` s `,` v `.` φ := object_exsts s v φ
notation `~∃*` v `.` φ := object_exsts (getSort v) v φ
notation `~¬` := object_not
notation `~¬` := object_not


-- φ₁ ∨ φ₂ ≣ ¬ (¬ φ₁ ∧ ¬ φ₂)
--| s φ ψ :=  (~¬s φ) ~∧s; (~¬s ψ)
notation φ `~∨` s `;` ψ := object_not s (object_and s (object_not s φ) (object_not s ψ))

-- φ → ψ ≣ ¬ φ ∨ ψ 
notation φ `~` s `~>` ψ :=  (~¬s φ) ~∨ s; (ψ)
--notation φ `~` s `~>` ψ :=   

--| s φ ψ := object_and (s) (object_implies (s) (φ) (ψ)) (object_implies (s) (ψ) (φ))
-- φ ↔ ψ ≣ φ →s ψ ∧s ψ →s φ 
notation φ `<~>` s `;` ψ := (φ ~s~> ψ)  ~∧s; (ψ ~s~> φ)

notation `~∀` s `,` name `:` sort `.` pat := ~¬s (~∃s, name : sort . pat)
notation `~∀` s `,` v `.` φ := ~¬s (~∃s, v . ~¬s φ)
notation `~∀` v `:` s `.` φ := ~∀ (getSort v) , v : s . φ 

-- #'ceil is defined as a symbol.
--  ⌈_⌉ (s1, s2) ∈ Σ s1, s2
def object_'ceil  : object_sort → object_sort → ~Symbol  
| s1 s2 := ⟨ "'ceil", [s1, s2], [s1], s2 ⟩

notation `#'ceil` (s1, s2) := object_'ceil s1 s2

notation  `⌈` φ `⌉` (s1, s2) := ~apply (object_'ceil s1 s2) . [φ]
notation `⌊` φ `⌋` (s1, s2) := ~¬s2 ⌈~¬s1 φ⌉ (s1, s2)
notation φ1 `~=` (s1, s2) `;` φ2 := ⌊ ((φ1) <~> s1; (φ2)) ⌋ (s1, s2)
notation φ1 `¬~=` (s1, s2) `;` φ2 := object_not s1 (⌊ ((φ1) <~> s1; (φ2)) ⌋ (s1, s2))
notation φ `~∈` (s1, s2) `;` ψ  := ⌈(φ ~∧s1; ψ)⌉ (s1, s2)
--notation φ `#∈` (s1, s2) `;` ψ  := ⌈object_and s1 φ ψ⌉ (s1, s2)
notation `~⊤` s := object_exsts s (object_variable.mk "⊤" s) (~variableAsPattern (object_variable.mk "⊤" s))
notation `~⊥` s := object_not s (~⊤s)

open object_pattern

definition object_var_elems_to_pat : string → object_sort → object_pattern
| str sort := ~variableAsPattern (object_variable.mk str sort)


definition object_get_pattern_sort : object_pattern → object_sort
| (object_variable_as_pattern v) := getSort v
| (object_application (σ) (Sigma)) := getSort σ
| (object_and s φ₁ φ₂) := s
| (object_not s φ) := s
| (object_exsts s v φ) := s
--
instance object_pattern.has_sort : has_sort object_pattern object_sort := ⟨ object_get_pattern_sort ⟩ 

-- ################ Auxiliary stuff for ⊤ 

def object_btop : bool → (object_sort → ~Pattern)
| tt s := ~⊤ s
| ff s := ~⊥ s

def object_is_top : object_pattern → bool 
| (object_exsts _ (object_variable.mk "⊤" _) (~variableAsPattern (object_variable.mk "⊤" _))) := tt
| _ := ff


def object_is_bottom : object_pattern → bool
| (object_not _ φ) := if object_is_top φ then tt else ff
| _ := ff

mutual def object_pattern_to_string, object_pattern_list_to_string 
with object_pattern_to_string : object_pattern → string
| (~variableAsPattern (v)) := "(~var : " ++ (repr v) ++ ")"
| (object_application σ L) := "(~apply " ++ (repr σ) ++ " . (" ++ (object_pattern_list_to_string L) ++ ")" ++ ")"
| (object_and (s) (φ1) (φ2)) := "(" ++ (object_pattern_to_string φ1) ++ " ∧" ++ (repr s) ++ " " ++ (object_pattern_to_string φ2) ++ ")"
| (object_not (s) (φ)) := if object_is_top φ then ("( ⊥" ++ (repr (getSort φ))) ++ " )"
                     else "( ¬" ++ (repr s) ++ " " ++ (object_pattern_to_string φ) ++ " )"
| (object_exsts (s) (v) (φ)) := 
    if (object_is_top (object_exsts s v φ)) then ("( ⊤" ++ repr s) ++ " )"
    else "(∃" ++ (repr s) ++ ", (" ++ (repr v) ++ ":" ++ (repr (getSort v))  ++ ") " ++ " . " ++ (object_pattern_to_string φ) ++ " )"
with object_pattern_list_to_string : list object_pattern → string
| [] := ""
| (hd :: tl) := (object_pattern_to_string hd) ++ ", " ++ object_pattern_list_to_string tl

instance : has_repr object_pattern := ⟨ object_pattern_to_string ⟩ 

-- ~apply object_get_fv . [φ1, φ2, ...]
-- This definition is based on the axioms outlined on p. 33
-- The interesting case is the existential quantifier, which acts
-- as variable binding, and therefore removes the bound variable
-- from the eventual list of free variables.

mutual def object_get_fv, object_get_fv_from_patterns
with object_get_fv : ~Pattern → ~VariableList
| (~variableAsPattern v) := [v]
| (object_application σ L) := object_get_fv_from_patterns L
| (object_and s φ1 φ2) := object_get_fv φ1 ++ object_get_fv φ2
| (object_not s φ) := object_get_fv φ
| (object_exsts s v φ) := delete_variable_list v (object_get_fv φ)
with object_get_fv_from_patterns : ~PatternList → ~VariableList
| [] := []
| (hd :: tl) := object_get_fv hd ++ object_get_fv_from_patterns tl


def object_occurs_free : object_sort → ~Variable → ~Pattern → ~Pattern
| carrier v φ := object_btop (list.mem v (object_get_fv φ)) carrier


def object_longest_string : list #String → #String
| l := list.foldl (λ s : #String, (λ acc : #String, if string.length (s) > string.length (acc) then s else acc)) ("") (l)

def object_fresh_name : ~PatternList → #String
| l := let longest_varname := object_longest_string (list.map getName (object_get_fv_from_patterns (l)))
         in  (longest_varname ++ "_a")


definition object_unwrap : option ~Pattern → ~Pattern
| none := ~⊥ (object_sort.mk ⟨ "BottomSort" ⟩  object_sort_list.nil)
| (some φ) := φ

--φ [ψ / v]
definition object_substitute : ℕ → ~Pattern → ~Pattern → ~Variable → option ~Pattern 
| zero a b c := a
| (succ n) (~variableAsPattern (u)) (ψ) (v) := if u = v then some ψ else some (~variableAsPattern (u))
--| (succ n) (object_application (σ) (L)) ψ v :=  ~apply σ . (list.map (λ p : object_pattern, object_substitute n p ψ v) L)
| (succ n) (object_application (σ) (L)) ψ v :=  
    let mapped :  list (option ~Pattern) := list.map (λ p : object_pattern, object_substitute n p ψ v) L,
        terminated : bool := list.any mapped (λ x : option ~Pattern, x = none),
        object_unwrapped : ~PatternList := list.map(λ p : option ~Pattern, object_unwrap p) mapped
    in if terminated then none else some (~apply σ . object_unwrapped)
| (succ n) (object_and (s) (φ1) (φ2)) (ψ) (v) := 
    let lhs : option ~Pattern := object_substitute n φ1 ψ v,
        rhs : option ~Pattern := object_substitute n φ2 ψ v
    in  match (lhs, rhs) with
        (none, none) := none,
        (some l, none) := none,
        (none, some r) := none,
        (some l, some r) := some (l ~∧s; r)
        end
| (succ n) (object_not (s) (φ)) (ψ) (v) := 
    let mapped : option ~Pattern := object_substitute n φ ψ v
    in  match mapped with
        (some φ') := some (~¬s φ'),
        (none) := none
        end
| (succ n) (object_exsts (s') (x) φ) (ψ) (v) := 
             let x'_var := object_variable.mk (object_fresh_name [φ, ψ, ~variableAsPattern v]) s',
                 x'_pat := ~variableAsPattern x'_var,
                 mapped_one : option ~Pattern := object_substitute (n) (φ) (x'_pat) (x)
             in  match mapped_one with
                 none := none,
                 (some φ') := let mapped_two : option ~Pattern := object_substitute (n) (φ') (ψ) (v)
                              in match mapped_two with
                              none := none,
                              (some φ'') := some (~∃s', (x'_var) . (x'_pat) ~∧s'; ~∃s', (x'_var) . (φ''))
                              end
                end

-- gas parameter is made implicit by giving some default amount of gas.
definition object_substitute_i : ~Pattern → ~Pattern → ~Variable → option ~Pattern := object_substitute 100



-- object_subst_rel v φ ψ τ ; the result of the object_substitution of ψ for all 
-- occurences of v in φ。
-- This is modeled as v → original pattern → object_substituting pattern → object_substitution result.
-- So for the assertion ' the pattern τ properly represents object_substitution of ψ for v 
-- in pattern φ, you would prove 'subst v φ ψ τ' for the appropriate construction.

mutual inductive object_subst, object_subst_list
with object_subst : ~Variable → ~Pattern → ~Pattern → ~Pattern → Prop
| application : ∀ {σ : ~Symbol} {L ζ : ~PatternList} {φ ψ : ~Pattern} {v : ~Variable},
    object_subst_list v L ψ ζ → object_subst v (~apply σ . L) ψ (~apply σ . ζ)
| and : ∀ {s : object_sort} {φ1 φ2 τ1 τ2 ψ: ~Pattern} {v : ~Variable},
    object_subst v φ1 ψ (τ1) → object_subst v φ2 ψ (τ2) → object_subst v (φ1 ~∧s; φ2) ψ (τ1 ~∧s; τ2)
| not : ∀ {s : object_sort} {φ ψ τ : ~Pattern} {v : ~Variable},
    object_subst v φ ψ τ → object_subst v (~¬s φ) ψ (~¬s τ)
| var_eq : ∀ {v : ~Variable} {φ ψ : ~Pattern},
    φ = (~variableAsPattern v) → object_subst v φ ψ ψ
| var_neq : ∀ {v : ~Variable} {φ ψ : ~Pattern},
    (∃ u, ~variableAsPattern u = φ ∧ v ≠ u) → object_subst v φ ψ φ
| exsts : ∀ {s s' : object_sort} {v : ~Variable} {φ ψ τ : ~Pattern},
    -- if the object_substitution φ [ x':s / x:s ] is properly represented in τ,
    object_subst (object_variable.mk "x" s) φ (~variableAsPattern (object_variable.mk "x'" s)) τ
    -- and the object_substitution φ [ ψ / v ] is properly represented in τ, 
    → object_subst (v) φ ψ τ
    -- then the big conjuctive object_substitution result is good.
    → object_subst v (~∃s', "x":s . φ) ψ 
    (~∃s', " x' ":s . (~variableAsPattern $ object_variable.mk (object_fresh_name [φ, ψ,  (~variableAsPattern v)]) (s)) ~∧s; (~∃s', " x' ":s . τ))
with object_subst_list : ~Variable → list ~Pattern → ~Pattern → list ~Pattern → Prop
| nil : ∀ {v : ~Variable} {ψ τ : ~Pattern},
    object_subst_list v [] ψ []
| cons : ∀ {v : ~Variable} {L ζ: list ~Pattern} {φ ψ τ : ~Pattern} ,
    object_subst_list v L ψ ζ 
    → object_subst v φ ψ τ 
    → object_subst_list v (φ :: L) ψ (τ :: ζ)

mutual def object_sc, object_sc_l
with object_sc : object_sort → ~Pattern → ~Pattern → ~Pattern
| carrier (φ) (~apply σ . L) := object_sc_l carrier φ L
| carrier (φ) (ψ) := if φ = ψ then ~⊤ carrier else ~⊥ carrier
with object_sc_l : object_sort → ~Pattern → ~PatternList → ~Pattern
| carrier φ [] := ~⊥ carrier
| carrier φ (hd :: tl) := have 2 < 1 + (1 + (1 + list.sizeof tl)), by {
      intros,
      generalize : (list.sizeof tl = n), 
      simp, 
      apply nat.lt_add_left, 
      apply nat.lt.base,
},
                            have 3 < 1 + (1 + (1 + (1 + list.sizeof tl))), by {
      intros,
      generalize : (list.sizeof tl = n),
      simp,
      apply nat.lt_add_left,
      apply nat.lt.base,},
 if (object_sc carrier φ hd = ~⊤ carrier) then ~⊤ carrier else (object_sc_l carrier φ tl)

-- ####### Coercions/Lifts

-- ~Symbol → ~Pattern
def object_symbol.to_object_pattern : ~Symbol → ~Pattern
| σ := ~apply σ . []

instance object_symbol_to_object_pattern_lift : has_lift ~Symbol ~Pattern := ⟨ object_symbol.to_object_pattern ⟩ 

-- ~SymbolList → ~PatternList
def object_symbol_list.to_object_pattern_list : ~SymbolList → ~PatternList
| L := list.map (λ σ : ~Symbol, lift σ) L

instance object_symbol_list_to_object_pattern_list_lift : has_lift ~SymbolList ~PatternList := ⟨ object_symbol_list.to_object_pattern_list ⟩ 


-- ~Variable → ~Pattern
def object_variable.to_object_pattern_lift : ~Variable → ~Pattern
| v := ~variableAsPattern v

instance object_variable_to_object_pattern_lift : has_lift ~Variable ~Pattern := ⟨ object_variable.to_object_pattern_lift ⟩


instance : is_Pattern object_pattern :=
    ⟨ ~Variable
    , object_sort
    , object_is_top
    , object_is_bottom
    , object_get_fv
    , object_get_fv_from_patterns
    , object_occurs_free
    , object_btop
    , object_sc
    , object_sc_l
    , object_fresh_name
    , object_substitute_i ⟩ 

