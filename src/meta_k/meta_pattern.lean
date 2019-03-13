import .meta_sort
import .meta_var
import .meta_symbol
import term_lemmas

open nat
open has_sort

-- #########################################################
-- #####    meta_pattern    ################################

inductive meta_pattern : Type
| meta_variable_as_pattern : #Variable → meta_pattern
-- ??
| meta_application : #Symbol → list meta_pattern → meta_pattern
| meta_and : #Sort → meta_pattern → meta_pattern → meta_pattern
| meta_not : #Sort → meta_pattern → meta_pattern
| meta_exsts : #Sort → #Variable → meta_pattern → meta_pattern

instance : decidable_eq meta_pattern :=
by tactic.mk_dec_eq_instance

open meta_pattern

notation `#Pattern` := meta_pattern
notation `#variableAsPattern` := meta_variable_as_pattern
notation `#PatternList` := list meta_pattern
notation `#apply` σ . L := meta_application σ L
notation `#and` := meta_and

notation φ `#∧` s `;`  ψ := meta_and s φ ψ 

notation `#∃` s `,` v `:`s `.` φ := meta_exsts s (meta_variable.mk v s) φ
notation `#∃` s `,` v `.` φ := meta_exsts s v φ
notation `#∃*` v `.` φ := meta_exsts (getSort v) v φ
notation `#¬` := meta_not
notation `#¬` := meta_not


-- φ₁ ∨ φ₂ ≣ ¬ (¬ φ₁ ∧ ¬ φ₂)
--| s φ ψ :=  (#¬s φ) #∧s; (#¬s ψ)
notation φ `#∨` s `;` ψ := meta_not s (meta_and s (meta_not s φ) (meta_not s ψ))

-- φ → ψ ≣ ¬ φ ∨ ψ 
notation φ `~` s `~>` ψ :=  (#¬s φ) #∨ s; (ψ)
--notation φ `~` s `~>` ψ :=   

--| s φ ψ := meta_and (s) (meta_implies (s) (φ) (ψ)) (meta_implies (s) (ψ) (φ))
-- φ ↔ ψ ≣ φ →s ψ ∧s ψ →s φ 
notation φ `<~>` s `;` ψ := (φ ~s~> ψ)  #∧s; (ψ ~s~> φ)

notation `#∀` s `,` name `:` sort `.` pat := #¬s (#∃s, name : sort . pat)
notation `#∀` s `,` v `.` φ := #¬s (#∃s, v . #¬s φ)
notation `#∀` v `:` s `.` φ := #∀ (getSort v) , v : s . φ 

-- #'ceil is defined as a symbol.
--  ⌈_⌉ (s1, s2) ∈ Σ s1, s2
def meta_'ceil  : #Sort → #Sort → #Symbol  
| s1 s2 := ⟨ "#'ceil", [s1, s2], [s1], s2 ⟩

notation `#'ceil` (s1, s2) := meta_'ceil s1 s2

notation  `⌈` φ `⌉` (s1, s2) := #apply (meta_'ceil s1 s2) . [φ]
notation `⌊` φ `⌋` (s1, s2) := #¬s2 ⌈#¬s1 φ⌉ (s1, s2)
notation φ1 `#=` (s1, s2) `;` φ2 := ⌊ ((φ1) <~> s1; (φ2)) ⌋ (s1, s2)
notation φ1 `¬#=` (s1, s2) `;` φ2 := meta_not s1 (⌊ ((φ1) <~> s1; (φ2)) ⌋ (s1, s2))
notation φ `#∈` (s1, s2) `;` ψ  := ⌈(φ #∧s1; ψ)⌉ (s1, s2)
--notation φ `#∈` (s1, s2) `;` ψ  := ⌈meta_and s1 φ ψ⌉ (s1, s2)
notation `#⊤` s := meta_exsts s (#variable "⊤" s) (#variableAsPattern (#variable "⊤" s))
notation `#⊥` s := #¬s (#⊤s)

open meta_pattern

definition meta_var_elems_to_pat : string → meta_sort → meta_pattern
| str sort := #variableAsPattern (meta_variable.mk str sort)


definition meta_get_pattern_sort : meta_pattern → meta_sort
| (meta_variable_as_pattern v) := getSort v
| (meta_application (σ) (Sigma)) := getSort σ
| (meta_and s φ₁ φ₂) := s
| (meta_not s φ) := s
| (meta_exsts s v φ) := s
--
instance meta_pattern.has_sort : has_sort meta_pattern meta_sort := ⟨ meta_get_pattern_sort ⟩ 

-- ################ Auxiliary stuff for ⊤ 

-- FIXME The naming of the variable for ⊤ is just so the pretty printer will
-- display it as ⊤ and not as an exists pattern.


def meta_btop : bool → (#Sort → #Pattern)
| tt s := #⊤s
| ff s := #⊥s

def meta_is_top : meta_pattern → bool 
| (meta_exsts _ (#variable "⊤" _) (#variableAsPattern (#variable "⊤" _))) := tt
| _ := ff


def meta_is_bottom : meta_pattern → bool
| (meta_not _ φ) := if meta_is_top φ then tt else ff
| _ := ff

def pat_conj : meta_pattern → meta_pattern → bool
| φ1 φ2 := (meta_is_top φ1) && (meta_is_top φ2)

infix `#&&`: 90 := pat_conj


mutual def meta_pattern_to_string, meta_pattern_list_to_string 
with meta_pattern_to_string : meta_pattern → string
| (#variableAsPattern (v)) := "(var : " ++ (repr v) ++ ")"
| (meta_application σ L) := "(#apply " ++ (repr σ) ++ " . (" ++ (meta_pattern_list_to_string L) ++ ")" ++ ")"
| (meta_and (s) (φ1) (φ2)) := "(" ++ (meta_pattern_to_string φ1) ++ " ∧" ++ (repr s) ++ " " ++ (meta_pattern_to_string φ2) ++ ")"
| (meta_not (s) (φ)) := if meta_is_top φ then ("( ⊥" ++ (repr (getSort φ))) ++ " )"
                     else "( ¬" ++ (repr s) ++ " " ++ (meta_pattern_to_string φ) ++ " )"
| (meta_exsts (s) (v) (φ)) := 
    if (meta_is_top (meta_exsts s v φ)) then ("( ⊤" ++ repr s) ++ " )"
    else "(∃" ++ (repr s) ++ ", (" ++ (repr v) ++ ":" ++ (repr (getSort v))  ++ ") " ++ " . " ++ (meta_pattern_to_string φ) ++ " )"
with meta_pattern_list_to_string : list meta_pattern → string
| [] := ""
| (hd :: tl) := (meta_pattern_to_string hd) ++ ", " ++ meta_pattern_list_to_string tl

instance : has_repr meta_pattern := ⟨ meta_pattern_to_string ⟩ 


-- FIXME delete if poly version works
--def delete_sort_list : #Sort → #SortList → #SortList
--| s [] := []
--| s (hd :: tl) := if s = hd then delete_sort_list s tl else hd :: delete_sort_list s tl


-- FIXME why is this here
-- replace equality

-- FIXME delete?
----symbols (3/7)
--def meta_get_fv_pred : #Symbol := #symbol "#meta_get_fv" [] [%PatternList] %VariableList
--def meta_get_fv_from_patterns_pred : #Symbol := #symbol "#meta_get_fv_from_patterns" [] [%PatternList] %VariableList

-- #apply meta_get_fv . [φ1, φ2, ...]
-- This definition is based on the axioms outlined on p. 33
-- The interesting case is the existential quantifier, which acts
-- as variable binding, and therefore removes the bound variable
-- from the eventual list of free variables.

mutual def meta_get_fv, meta_get_fv_from_patterns
with meta_get_fv : #Pattern → #VariableList
| (#variableAsPattern v) := [v]
| (meta_application σ L) := meta_get_fv_from_patterns L
| (meta_and s φ1 φ2) := meta_get_fv φ1 ++ meta_get_fv φ2
| (meta_not s φ) := meta_get_fv φ
| (meta_exsts s v φ) := delete_variable_list v (meta_get_fv φ)
with meta_get_fv_from_patterns : #PatternList → #VariableList
| [] := []
| (hd :: tl) := meta_get_fv hd ++ meta_get_fv_from_patterns tl


def meta_occurs_free : #Sort → #Variable → #Pattern → #Pattern
| carrier v φ := meta_btop (list.mem v (meta_get_fv φ)) carrier


-- 3/7

def longest_string : list #String → #String
| l := list.foldl (λ s : #String, (λ acc : #String, if string.length (s) > string.length (acc) then s else acc)) ("") (l)

def meta_fresh_name : #PatternList → #String
| l := let longest_varname := longest_string (list.map get_meta_variable_name (meta_get_fv_from_patterns (l)))
         in  (longest_varname ++ "_a")


definition unwrap : option #Pattern → #Pattern
| none := #⊥ %Sort
| (some φ) := φ

-- a decidable definition of variable substitution; uses a gas parameter to ease termination
-- proof, and is wrapped in an option to flag termination via 'out of gas'
--φ [ψ / v]
definition substitute : ℕ → #Pattern → #Pattern → #Variable → option #Pattern 
| zero a b c := a
| (succ n) (#variableAsPattern (u)) (ψ) (v) := if u = v then some ψ else some (#variableAsPattern (u))
--| (succ n) (meta_application (σ) (L)) ψ v :=  #apply σ . (list.map (λ p : meta_pattern, substitute n p ψ v) L)
| (succ n) (meta_application (σ) (L)) ψ v :=  
    let mapped :  list (option #Pattern) := list.map (λ p : meta_pattern, substitute n p ψ v) L,
        terminated : bool := list.any mapped (λ x : option #Pattern, x = none),
        unwrapped : #PatternList := list.map(λ p : option #Pattern, unwrap p) mapped
    in if terminated then none else some (#apply σ . unwrapped)
| (succ n) (meta_and (s) (φ1) (φ2)) (ψ) (v) := 
    let lhs : option #Pattern := substitute n φ1 ψ v,
        rhs : option #Pattern := substitute n φ2 ψ v
    in  match (lhs, rhs) with
        (none, none) := none,
        (some l, none) := none,
        (none, some r) := none,
        (some l, some r) := some (l #∧s; r)
        end
| (succ n) (meta_not (s) (φ)) (ψ) (v) := 
    let mapped : option #Pattern := substitute n φ ψ v
    in  match mapped with
        (some φ') := some (#¬s φ'),
        (none) := none
        end
| (succ n) (meta_exsts (s') (x) φ) (ψ) (v) := 
             let x'_var := meta_variable.mk (meta_fresh_name [φ, ψ, #variableAsPattern v]) s',
                 x'_pat := #variableAsPattern x'_var,
                 mapped_one : option #Pattern := substitute (n) (φ) (x'_pat) (x)
             in  match mapped_one with
                 none := none,
                 (some φ') := let mapped_two : option #Pattern := substitute (n) (φ') (ψ) (v)
                              in match mapped_two with
                              none := none,
                              (some φ'') := some (#∃s', (x'_var) . (x'_pat) #∧s'; #∃s', (x'_var) . (φ''))
                              end
                end
-- in meta_exsts (s') (x'_var) /-such that-/ (meta_and (s') (x'_pat) (meta_exsts (s') (x'_var) (sub_two)))

-- gas parameter is made implicit by giving some default amount of gas.
definition meta_substitute_i : #Pattern → #Pattern → #Variable → option #Pattern := substitute 100



-- subst_rel v φ ψ τ ; the result of the substitution of ψ for all 
-- occurences of v in φ。
-- This is modeled as v → original pattern → substituting pattern → substitution result.
-- So for the assertion ' the pattern τ properly represents substitution of ψ for v 
-- in pattern φ, you would prove 'subst v φ ψ τ' for the appropriate construction.
mutual inductive subst, subst_list
with subst : #Variable → #Pattern → #Pattern → #Pattern → Prop
| application : ∀ {σ : #Symbol} {L ζ : #PatternList} {φ ψ : #Pattern} {v : #Variable},
    subst_list v L ψ ζ → subst v (#apply σ . L) ψ (#apply σ . ζ)
| and : ∀ {s : #Sort} {φ1 φ2 τ1 τ2 ψ: #Pattern} {v : #Variable},
    subst v φ1 ψ (τ1) → subst v φ2 ψ (τ2) → subst v (φ1 #∧s; φ2) ψ (τ1 #∧s; τ2)
| not : ∀ {s : #Sort} {φ ψ τ : #Pattern} {v : #Variable},
    subst v φ ψ τ → subst v (#¬s φ) ψ (#¬s τ)
| var_eq : ∀ {v : #Variable} {φ ψ : #Pattern},
    φ = (#variableAsPattern v) → subst v φ ψ ψ
| var_neq : ∀ {v : #Variable} {φ ψ : #Pattern},
    (∃ u, #variableAsPattern u = φ ∧ v ≠ u) → subst v φ ψ φ
| exsts : ∀ {s s' : #Sort} {v : #Variable} {φ ψ τ : #Pattern},
    -- if the substitution φ [ x':s / x:s ] is properly represented in τ,
    subst (#variable "x" s) φ (#variableAsPattern (#variable "x'" s)) τ
    -- and the substitution φ [ ψ / v ] is properly represented in τ, 
    → subst (v) φ ψ τ
    -- then the big conjuctive substitution result is good.
    → subst v (#∃s', "x":s . φ) ψ 
    (#∃s', " x' ":s . (#variableAsPattern $ #variable (meta_fresh_name [φ, ψ,  (#variableAsPattern v)]) (s)) #∧s; (#∃s', " x' ":s . τ))
with subst_list : #Variable → list #Pattern → #Pattern → list #Pattern → Prop
| nil : ∀ {v : #Variable} {ψ τ : #Pattern},
    subst_list v [] ψ []
| cons : ∀ {v : #Variable} {L ζ: list #Pattern} {φ ψ τ : #Pattern} ,
    subst_list v L ψ ζ 
    → subst v φ ψ τ 
    → subst_list v (φ :: L) ψ (τ :: ζ)



-- This one is subtle; the second relationship of #sc{#s} φ' φ can chase
-- nested context lists forever since it has a sort of transitivity; 
-- if φ' ≠ φ, but φ' is a (σ L) construction
-- that holds some symbol matching φ, #sc{#s} of ψ φ is still satisfied (eventually). 
-- The left hand side of the original conjunction can be left 
-- out since membership in L implicit in the function's construction.
mutual def meta_sc, meta_sc_l
with meta_sc : #Sort → #Pattern → #Pattern → #Pattern
| carrier (φ) (#apply σ . L) := meta_sc_l carrier φ L
| carrier (φ) (ψ) := if φ = ψ then #⊤ carrier else #⊥ carrier
with meta_sc_l : #Sort → #Pattern → #PatternList → #Pattern
| carrier φ [] := #⊥ carrier
| carrier (φ) (hd :: tl) := have 2 < 1 + (1 + (1 + list.sizeof tl)), by {
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
                    if (meta_sc carrier φ hd = #⊤ carrier) then #⊤ carrier else (meta_sc_l carrier φ tl)


-- ####### Coercions/Lifts


-- #Sort → #Pattern
def meta_sort.to_meta_pattern : #Sort → #Pattern
| (#sort name params) := #variableAsPattern (#variable name %Sort)

instance meta_sort_to_meta_pattern_lift : has_lift #Sort #Pattern := ⟨ meta_sort.to_meta_pattern ⟩ 

-- #SortList → #Pattern
def meta_sort_list.to_meta_pattern_list : #SortList → #PatternList
| L := list.map (λ s, lift s) L

instance meta_sort_list_to_meta_pattern_list_lift : has_lift #SortList #PatternList := ⟨ meta_sort_list.to_meta_pattern_list ⟩ 

-- #Symbol → #Pattern
def meta_symbol.to_meta_pattern : #Symbol → #Pattern
| σ := #apply σ . []

instance meta_symbol_to_meta_pattern_lift : has_lift #Symbol #Pattern := ⟨ meta_symbol.to_meta_pattern ⟩ 

-- #SymbolList → #PatternList
def meta_symbol_list.to_meta_pattern_list : #SymbolList → #PatternList
| L := list.map (λ σ : #Symbol, lift σ) L

instance meta_symbol_list_to_meta_pattern_list_lift : has_lift #SymbolList #PatternList := ⟨ meta_symbol_list.to_meta_pattern_list ⟩ 


-- #Variable → #Pattern
def meta_variable.to_meta_pattern_lift : #Variable → #Pattern
| v := #variableAsPattern v

instance meta_variable_to_meta_pattern_lift : has_lift #Variable #Pattern := ⟨ meta_variable.to_meta_pattern_lift ⟩

def meta_sort_variable.to_meta_pattern_lift : meta_sort_variable → #Pattern
| (meta_sort_variable.mk str) := #variableAsPattern (#variable ("#" ++ str) (%Sort))

instance meta_sort_variable_to_meta_pattern_lift : has_lift meta_sort_variable #Pattern :=
    ⟨ meta_sort_variable.to_meta_pattern_lift ⟩ 



def list_meta_sort.to_meta_pattern : #SortList → #Pattern
| [] := #apply (#symbol "#nilSortList" [] [] %SortList) . []
| (hd :: tl) := #apply (#symbol "consSortList" [] [%Sort, %SortList] %SortList) . [list_meta_sort.to_meta_pattern tl]

instance : has_lift (list meta_sort) (meta_pattern) := ⟨ list_meta_sort.to_meta_pattern ⟩  


def list_meta_symbol.to_meta_pattern : #SymbolList → #Pattern
| [] := #apply (#symbol "nilSymbolList" [] [] %SymbolList) . []
| (hd :: tl) := #apply (#symbol "consSymbolList" [] [%Symbol, %SymbolList] %SymbolList) . [list_meta_symbol.to_meta_pattern tl]

instance list_meta_symbol.to_meta_pattern_lift : has_lift (list meta_symbol)  meta_pattern := 
    ⟨list_meta_symbol.to_meta_pattern⟩ 

instance : is_Pattern meta_pattern :=
⟨ #Variable
, #Sort
, meta_is_top
, meta_is_bottom
, meta_get_fv
, meta_get_fv_from_patterns
, meta_occurs_free
, meta_btop
, meta_sc
, meta_sc_l
, meta_fresh_name
, meta_substitute_i ⟩ 