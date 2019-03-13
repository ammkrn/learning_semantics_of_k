import .meta_sort
import .meta_var
import .meta_symbol
import .meta_pattern
import .default_symbols
--import .meta_theory

open meta_pattern
open is_Pattern

structure Theory :=
(S : #SortList)
(Sigma : #SymbolList)
(A : #PatternList)

notation `S_of` := Theory.S
notation `Sigma_of` := Theory.Sigma
notation `A_of` := Theory.A

open Theory

-- new theory begins with foundations of MetaK; ten non-variable sorts Sₖ,
-- and a predefined set of predicate/symbol/axiom schemas
def base_meta_theory : Theory := ⟨ Sₖ, k_list, [], ⟩ 

def Theory_to_string : Theory → string
| T := "\n\n#S : " ++ repr (S T) ++ 
       "\n\n#Σ : " ++ repr (Sigma T) ++ 
       "\n\n#A : " ++ repr (A T)

instance : has_repr Theory := ⟨ Theory_to_string ⟩ 

/-
These end up being decidable for the most part, so if you really want to model them
as Props, you can declare an instance of decidable.
The bottom half of the judgment where you would normally make a triumphant declaration
of `provable _` is replaced here with just returning ⊤ {#s} for some #s ∈ Sₖ
-/

def fold_predicate_results : #Sort → #PatternList → #Pattern
| carrier φs := BtoP (list.all φs (λ x : #Pattern, isTop x))  carrier

def sort_declared_predicate {carrier :#Sort} : #Symbol := 
    #symbol "#sortDeclared" [] [%Sort, %SortList] %Pattern

def symbol_declared_predicate {carrier : #Sort} : #Symbol :=
    #symbol "#symbolDeclared" [] [%Symbol, %SymbolList] %Pattern

def axiom_declared_predicate {carrier : #Sort} : #Symbol  :=
    #symbol "#axiomDeclared" [] [%Pattern, %PatternList] %Pattern


--in lieu of a larger evaluation function that accurately reflects the reduction
-- of pattern application to symbols, we use these decidable functions that
-- have the same behavior as the predicate symbols and return parametric ⊤/⊥ patterns
def axiom_declared  : Theory  → #Sort → #Pattern → #Pattern
| t carrier φ := BtoP (list.mem φ (A_of t)) carrier

def sort_declared  : Theory → #Sort → #Pattern → #Pattern
| t carrier φ := BtoP (list.mem φ (lift (S_of t))) carrier

def symbol_declared  : Theory → #Sort → #Symbol → #Pattern
-- if symbol is ceil, behavior is different
| t carrier (#symbol "#'ceil" [s1, s2] _ _) :=
    let r1 : bool := list.mem (s1 : #Sort) ((S_of t) : #SortList),
        r2 : bool := list.mem (s2 : #Sort) ((S_of t) : #SortList)
    in BtoP (r1 && r2) carrier
| t carrier σ := BtoP (list.mem (getName σ : #String) (list.map (getName) (Sigma_of t))) carrier



def wellFormed_pred {carrier : #Sort} : #Symbol :=
    #symbol "#wellFormed" [] [%Pattern] %Pattern

mutual def wellFormed, wellFormed_list
with wellFormed : Theory → #Sort → #Pattern → #Pattern
| t carrier (#variableAsPattern (#variable str s)) := sort_declared t carrier (lift s)
| t carrier (meta_application σ L) := 
    let p1 : #Pattern := (symbol_declared t carrier σ),
        p2 : #Pattern := wellFormed_list t carrier L,
        p3 : #Pattern := sort_declared t carrier (lift (getSort σ)),
        p4 : #Pattern := BtoP ((list.map (λ x, getSort x) L) = ((getArgumentSorts σ))) carrier
    in fold_predicate_results carrier [p1, p2, p3, p4]
| t carrier (meta_and s φ ψ) :=
    let p1 : #Pattern := wellFormed t carrier φ,
        p2 : #Pattern := wellFormed t carrier ψ,
        s1 : #Pattern := BtoP ((getSort φ = s) && (getSort ψ = s)) carrier
    in fold_predicate_results carrier [p1, p2, s1]
| t carrier (meta_not s φ) := 
    fold_predicate_results carrier [(wellFormed t carrier φ), (BtoP (getSort φ = s) carrier)]
| t carrier (meta_exsts s (#variable str s') φ) :=
    let p1 : #Pattern := sort_declared t carrier (lift s'),
        p2 : #Pattern := wellFormed t carrier φ,
        p3 : #Pattern := BtoP (getSort φ = s) carrier
    in fold_predicate_results carrier [p2, p2, p3]
with wellFormed_list : Theory → #Sort → #PatternList → #Pattern
| t carrier [] := #⊤ carrier
| t carrier (hd :: tl) := have 3 < 1 + (1 + (1 + (1 + list.sizeof tl))), by {
      intros,
      generalize : (list.sizeof tl = n),
      simp,
      apply nat.lt_add_left,
      apply nat.lt.base,},
   BtoP ((wellFormed t carrier hd) #&& (wellFormed_list t carrier tl)) carrier

inductive provable (T : Theory) (carrier : #Sort) : #Sort → #Pattern →  Prop
| propositional_1 : ∀ {φ ψ : #Pattern} {s : #Sort},
    (isTop $ wellFormed T carrier (φ ~s~> (ψ ~s~> φ)))
    → provable carrier (φ ~s~> (ψ ~s~> φ)) 
| propositional_2 : ∀ {φ1 φ2 φ3 : #Pattern} {s : #Sort},
    (isTop $ wellFormed T carrier ((φ1 ~s~> (φ2 ~s~> φ3)) ~s~> ((φ1 ~s~> φ2) ~s~> (φ1 ~s~> φ3))))
    → provable carrier ((φ1 ~s~> (φ2 ~s~> φ3)) ~s~> ((φ1 ~s~> φ2) ~s~> (φ1 ~s~> φ3)))
| propositional_3 : ∀ {φ ψ : #Pattern} {s : #Sort},
    (isTop $ wellFormed T carrier ((#¬s ψ ~s~> #¬s φ) ~s~> (φ ~s~> ψ)))
    → provable carrier ((#¬s ψ ~s~> #¬s φ) ~s~> (φ ~s~> ψ))
| modus_ponens : ∀ {φ ψ : #Pattern} {s : #Sort},
    provable carrier φ  -- wellFormedness can be omitted since components are well formed
    → provable carrier (φ ~s~> ψ)
    → provable carrier ψ
| fol_1 : ∀ {φ ψ: #Pattern} {v : #Variable} {s : #Sort},
    (isBottom $ (meta_occurs_free carrier v φ))
    → (isTop $ wellFormed T carrier ((#∀s, v . (φ ~s~> ψ)) ~s~> ((φ) ~s~> (#∀s, v . ψ))))
    → provable carrier ((#∀s, v . (φ ~s~> ψ)) ~s~> ((φ) ~s~> (#∀s, v . ψ)))
| universal_generalization : ∀ {φ : #Pattern} {v : #Variable} {s : #Sort},
    provable carrier φ
    → (isTop $ wellFormed T carrier (#∀s, v . φ))
    → provable carrier (#∀s, v . φ)
| variable_substitution : ∀ {φ : #Pattern} {u v: #Variable} {s : #Sort},
-- if the computable definition of substitution terminates, AND
-- termination was NOT caused by 'out of gas'...
     substitute_i φ ↑u v ≠ none
     → (isTop $ wellFormed T carrier (#∀s, v . (φ ~s~> (unwrap $ substitute_i φ ↑u v))))
    → provable carrier (#∀s, v . (φ ~s~> (unwrap $ substitute_i φ ↑u v)))
| propagataion_bottom : ∀ {L R : #PatternList} {s : #Sort} {σ : #Symbol},
    (isTop $ wellFormed T carrier ((#apply σ . (L ++ ((#⊥s) :: (R)))) ~s~> (#⊥ s)))
    → provable carrier ((#apply σ . (L ++ ((#⊥s) :: (R)))) ~s~> (#⊥ s))
| propagation_or : ∀ {L R : #PatternList} {s : #Sort} {σ : #Symbol} {φ φ' : #Pattern},
--    L ++ ((φ #∨s; φ') :: (R))
(isTop $ wellFormed T carrier ((#apply σ . (L ++ ((φ #∨s; φ') :: R)))     
                    ~s~>     
                 ((#apply σ . (L ++ (φ :: R))) #∨s; (#apply σ . ( L ++ (φ' :: R))))))
→ provable carrier ((#apply σ . (L ++ ((φ #∨s; φ') :: R)))     
                    ~s~>     
                 ((#apply σ . (L ++ (φ :: R))) #∨s; (#apply σ . ( L ++ (φ' :: R)))))
| propagation_exists : ∀ {L R : #PatternList} {s : #Sort} {v u : #Variable} {σ : #Symbol} {φ φ' : #Pattern},
    (isTop $ meta_occurs_free carrier u (#apply σ . (L ++ ((#∃s, u . φ) :: R))) )
    → (isTop $ wellFormed T carrier ((#apply σ . (L ++ ((#∃s, u . φ) :: R))) 
                       ~s~> 
                       (#∃s, u . (#apply σ . (L ++ ((#∃s, u . φ) :: R))))))
    → provable carrier ((#apply σ . (L ++ ((#∃s, u . φ) :: R))) 
                       ~s~> 
                       (#∃s, u . (#apply σ . (L ++ ((#∃s, u . φ) :: R)))))
| framing : ∀ {L R : #PatternList} {φ φ' : #Pattern} {σ : #Symbol} {s : #Sort},
      provable carrier (φ ~s~> φ')
      → (isTop $ wellFormed T carrier ((#apply σ . (L ++ φ :: R)) ~s~> (#apply σ . (L ++ φ' :: R))))
      → provable carrier ((#apply σ . (L ++ φ :: R)) ~s~> (#apply σ . (L ++ φ' :: R)))
| existence : ∀ {x : #Variable} {s : #Sort},
    (isTop $ wellFormed T carrier (#∃s, x . lift x))
    → provable carrier (#∃s, x . lift x)
| singleton_variables : ∀ {C1 C2 : #Pattern} {x : #Variable} {φ : #Pattern} {s : #Sort},
    (isTop $ meta_sc carrier C1 (#variableAsPattern x #∧s; φ))
    → (isTop $ meta_sc carrier C2 (#variableAsPattern x #∧s; #¬s φ))
    → (isTop $ wellFormed T carrier (#¬s (C1 #∧s; C2)))
    → provable carrier (#¬s (C1 #∧s; C2))
| axiom_rule : ∀ {s : #Sort} {φ : #Pattern},
    (isTop $ axiom_declared T carrier φ)
    → (isTop $ wellFormed T carrier φ)
    → provable carrier φ
| functional_substitution : ∀ {s1 s2 : #Sort} {φ ψ : #Pattern} {u v : #Variable},
    (isTop $ meta_occurs_free carrier u ψ)
    → substitute_i φ ψ v ≠ none
    → (isTop $ wellFormed T carrier (((#∃s2, u . (lift u : #Pattern)) #= (s1, s2); ψ) 
                        #∧s2; (#∀s2, v . φ ~s2~> (unwrap $ substitute_i φ ψ v))))
    → provable carrier (((#∃s2, u . (lift u : #Pattern)) #= (s1, s2); ψ) 
                        #∧s2; (#∀s2, v . φ ~s2~> (unwrap $ substitute_i φ ψ v)))
| functional_variable : ∀ {u v : #Variable} {s1 s2 : #Sort},
    (isTop $ wellFormed T carrier (#∃s2, u . (lift u) #= (s1, s2); (lift v)))
    → provable carrier (#∃s2, u . (lift u) #= (s1, s2); (lift v))
| equality_introduction : ∀ {s1 s2 : #Sort} {φ : #Pattern},
    (isTop $ wellFormed T carrier (φ #= (s1, s2); φ))
    → provable carrier (φ #= (s1, s2); φ)
| equality_elimination : ∀ {φ1 φ2 ψ : #Pattern} {s1 s2 : #Sort} {u v :#Variable},
       substitute_i ψ φ1 v ≠ none
      → substitute_i ψ φ2 v ≠ none
      → (isTop $ wellFormed T carrier ((φ1) #= (s1, s2); φ2) ~s2~> ((unwrap $ substitute_i ψ φ1 v) ~s2~> (unwrap $ substitute_i ψ φ2 v)) )
      → provable carrier (((φ1) #= (s1, s2); φ2) ~s2~> ((unwrap $ substitute_i ψ φ1 v) ~s2~> (unwrap $ substitute_i ψ φ2 v)))
| defined_variable : ∀ {s s' : #Sort} {x : #Variable},
    (isTop $ wellFormed T carrier (⌈(lift x)⌉ (s, s')))
    → provable carrier (⌈(lift x)⌉ (s, s'))
| membership_introduction : ∀ {φ : #Pattern} {s1 s2 : #Sort} {v : #Variable},
    provable carrier φ 
    → (isTop $ wellFormed T carrier ((lift v) #∈ (s1, s2); φ))
    → (isBottom $ meta_occurs_free carrier v φ)
    → provable carrier ((lift v) #∈ (s1, s2); φ)
| membership_elimination : ∀ {φ : #Pattern} {s1 s2 : #Sort} {v : #Variable},
    provable carrier ( (lift v) #∈ (s1, s2); φ)
    → (isTop $ meta_occurs_free carrier v φ)
    → (isTop $ wellFormed T carrier φ)
    → provable carrier φ
| membership_variable : ∀ {u v : #Variable} {s1 s2 s3 : #Sort},
    (isTop $ wellFormed T carrier (((lift v) #∈ (s1, s2); (lift u)) #= (s1, s2); ((lift v) #∈ (s2, s3); (lift u))))
    → provable carrier (((lift v) #∈ (s1, s2); (lift u)) #= (s1, s2); ((lift v) #∈ (s2, s3); (lift u)))
| membership_and : ∀ {v : #Variable} {φ ψ : #Pattern} {s1 s2 s3 : #Sort},
    (isTop $ wellFormed T carrier (((lift v) #∈ (s1, s2); (φ #∧s1; ψ)) #= (s2, s3); (((lift v) #∈ (s1, s2); φ) #∧s2; ((lift v) #∈ (s1, s2); ψ))))
    → provable carrier (((lift v) #∈ (s1, s2); (φ #∧s1; ψ)) #= (s2, s3); (((lift v) #∈ (s1, s2); φ) #∧s2; ((lift v) #∈ (s1, s2); ψ)))
| membership_not : ∀ {v : #Variable} {s1 s2 s3 : #Sort} {φ : #Pattern},
    (isTop $ wellFormed T carrier ((↑v #∈ (s1, s2); #¬s1 φ) #= (s2, s3); (#¬s2 (↑v #∈ (s1, s2); φ))))
    → provable carrier ((↑v #∈ (s1, s2); #¬s1 φ) #= (s2, s3); (#¬s2 (↑v #∈ (s1, s2); φ)))
| membership_forall : ∀ {u v : #Variable} {s1 s2 s3 : #Sort} {φ : #Pattern},
    (v ≠ u) 
    → (isTop $ wellFormed T carrier ((↑v #∈ (s1, s2); #∀s1, u . φ) 
                                      #= (s2, s3); (#∀ s2, u . (↑v #∈ (s1, s2); φ))))
    → provable carrier ((↑v #∈ (s1, s2); #∀s1, u . φ) 
        #= (s2, s3); (#∀ s2, u . (↑v #∈ (s1, s2); φ)))
| membership_symbol : ∀ { φ : #Pattern } {u v : #Variable} {σ : #Symbol} {L R : #PatternList} {s1 s2 s3 s4 : #Sort},
    (u ≠ v)
    → (isBottom $ meta_occurs_free carrier u (#apply σ . (L ++ φ :: R)))
    → (isTop $ wellFormed T carrier ((↑v #∈ (s1, s2); #apply σ . L ++ φ :: R) #= (s2, s3);
    (#∃s2, u . ((↑u #∈ (s2, s4); φ) #∧s2; (↑v #∈ (s1, s2); #apply σ . (L ++ (↑u) :: R))))))
    → provable carrier ((↑v #∈ (s1, s2); #apply σ . L ++ φ :: R) #= (s2, s3);
    (#∃s2, u . ((↑u #∈ (s2, s4); φ) #∧s2; (↑v #∈ (s1, s2); #apply σ . (L ++ (↑u) :: R)))))



