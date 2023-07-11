/-import Project.Classes.ContextFree.Basics.Lifting

variable {T : Type}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def union_grammar (g₁ g₂ : CFGrammar T) : CFGrammar T :=
  CFGrammar.mk (Option (Sum g₁.Nt g₂.Nt)) none
    ((none,
        [Symbol.nonterminal
            (some
              (Sum.inl
                g₁.initial))])::(none,
          [Symbol.nonterminal
              (some
                (Sum.inr
                  g₂.initial))])::List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules)

variable {g₁ g₂ : CFGrammar T}

section LiftedGrammars

private def oN₁_of_N : (unionGrammar g₁ g₂).Nt → Option g₁.Nt
  | none => none
  | some (Sum.inl nonte) => some nonte
  | some (Sum.inr _) => none

private def oN₂_of_N : (unionGrammar g₁ g₂).Nt → Option g₂.Nt
  | none => none
  | some (Sum.inl _) => none
  | some (Sum.inr nonte) => some nonte

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private def g₁g : @LiftedGrammar T :=
  LiftedGrammar.mk g₁ (unionGrammar g₁ g₂) (some ∘ Sum.inl)
    (by
      intro x y h
      apply Sum.inl_injective
      apply Option.some_injective
      exact h)
    (by
      intro r h
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      rw [List.mem_map]
      use r
      constructor
      · exact h
      unfold ruleOfRule₁
      unfold liftRule
      norm_num
      unfold liftString
      unfold lsTNOfLsTN₁
      run_tac
        five_steps)
    oN₁OfN
    (by
      intro x y ass
      cases x
      · right
        rfl
      cases x; swap
      · right
        rfl
      cases y
      · rw [ass]
        right
        rfl
      cases y; swap
      · tauto
      left
      simp only [oN₁_of_N] at ass 
      apply congr_arg
      apply congr_arg
      exact ass)
    (by
      intro r
      rintro ⟨r_in, r_ntype⟩
      cases r_in
      · exfalso
        rw [r_in] at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₀ imposs
        exact Option.noConfusion imposs
      cases r_in
      · exfalso
        rw [r_in] at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₀ imposs
        exact Option.noConfusion imposs
      change r ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules at r_in 
      rw [List.mem_append] at r_in 
      cases r_in
      · rw [List.mem_map] at r_in 
        rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
        use r₁
        constructor
        · exact r₁_in
        rw [← r₁_convert_r]
        simp only [liftRule, ruleOfRule₁, liftString, lsTNOfLsTN₁, Prod.mk.inj_iff,
          eq_self_iff_true, true_and_iff]
        run_tac
          five_steps
      · exfalso
        rw [List.mem_map] at r_in 
        rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
        rw [← r₂_convert_r] at r_ntype 
        unfold ruleOfRule₂ at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₁ contr
        rw [Option.some_inj] at contr 
        exact Sum.noConfusion contr)
    (by intro; rfl)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private def g₂g : @LiftedGrammar T :=
  LiftedGrammar.mk g₂ (unionGrammar g₁ g₂) (some ∘ Sum.inr)
    (by
      intro x y h
      apply Sum.inr_injective
      apply Option.some_injective
      exact h)
    (by
      intro r h
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      rw [List.mem_map]
      use r
      constructor
      · exact h
      unfold ruleOfRule₂
      unfold liftRule
      norm_num
      unfold liftString
      unfold lsTNOfLsTN₂
      run_tac
        five_steps)
    oN₂OfN
    (by
      intro x y ass
      cases x
      · right
        rfl
      cases x
      · right
        rfl
      cases y
      · right
        rw [ass]
        rfl
      cases y
      · tauto
      left
      simp only [oN₂_of_N] at ass 
      apply congr_arg
      apply congr_arg
      exact ass)
    (by
      intro r
      rintro ⟨r_in, r_ntype⟩
      cases' List.eq_or_mem_of_mem_cons r_in with r_eq r_in_
      · exfalso
        rw [r_eq] at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₀ imposs
        exact Option.noConfusion imposs
      cases' List.eq_or_mem_of_mem_cons r_in_ with r_eq_ r_in__
      · exfalso
        rw [r_eq_] at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₀ imposs
        exact Option.noConfusion imposs
      clear r_in r_in_
      rename' r_in__ => r_in
      rw [List.mem_append] at r_in 
      cases r_in
      · exfalso
        rw [List.mem_map] at r_in 
        rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
        rw [← r₁_convert_r] at r_ntype 
        unfold ruleOfRule₁ at r_ntype 
        dsimp only at r_ntype 
        cases' r_ntype with n₂ contr
        rw [Option.some_inj] at contr 
        exact Sum.noConfusion contr
      · rw [List.mem_map] at r_in 
        rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
        use r₂
        constructor
        · exact r₂_in
        rw [← r₂_convert_r]
        simp only [liftRule, ruleOfRule₂, liftString, lsTNOfLsTN₂, Prod.mk.inj_iff,
          eq_self_iff_true, true_and_iff]
        run_tac
          five_steps)
    (by intro; rfl)

end LiftedGrammars

section LemmataSubset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private lemma deri₁_more (w : List (Symbol T g₁.Nt)) :
    CFDerives g₁ [Symbol.nonterminal g₁.initial] w →
      CFDerives (unionGrammar g₁ g₂) (lsTNOfLsTN₁ [Symbol.nonterminal g₁.initial])
        (lsTNOfLsTN₁ w) :=
  by
  intro ass
  let gg₁ := @g₁g T g₁ g₂
  change CFDerives gg₁.g (lsTNOfLsTN₁ [Symbol.nonterminal g₁.initial]) (lsTNOfLsTN₁ w)
  have techni : lsTNOfLsTN₁ = liftString gg₁.lift_nt :=
    by
    unfold lsTNOfLsTN₁
    unfold liftString
    ext1 w
    run_tac
      five_steps
  rw [techni]
  exact lift_deri ass

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private lemma deri₂_more (w : List (Symbol T g₂.Nt)) :
    CFDerives g₂ [Symbol.nonterminal g₂.initial] w →
      CFDerives (unionGrammar g₁ g₂) (lsTNOfLsTN₂ [Symbol.nonterminal g₂.initial])
        (lsTNOfLsTN₂ w) :=
  by
  intro ass
  let gg₂ := @g₂g T g₁ g₂
  change CFDerives gg₂.g (lsTNOfLsTN₂ [Symbol.nonterminal g₂.initial]) (lsTNOfLsTN₂ w)
  have techni : lsTNOfLsTN₂ = liftString gg₂.lift_nt :=
    by
    unfold lsTNOfLsTN₂
    unfold liftString
    ext1 w
    run_tac
      five_steps
  rw [techni]
  exact lift_deri ass

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private lemma in_union_of_in_first (w : List T) :
    w ∈ cFLanguage g₁ → w ∈ cFLanguage (unionGrammar g₁ g₂) :=
  by
  intro assum
  have deri_start :
    CFDerives (union_grammar g₁ g₂) [Symbol.nonterminal none]
      [Symbol.nonterminal (some (Sum.inl g₁.initial))] :=
    by
    apply CF_deri_of_tran
    use (none, [Symbol.nonterminal (some (Sum.inl g₁.initial))])
    constructor
    · change
        (none, [Symbol.nonterminal (some (Sum.inl g₁.initial))]) ∈
          (none,
              [Symbol.nonterminal
                  (some
                    (Sum.inl
                      g₁.initial))])::(none,
                [Symbol.nonterminal
                    (some
                      (Sum.inr
                        g₂.initial))])::List.map ruleOfRule₁ g₁.rules ++
                List.map ruleOfRule₂ g₂.rules
      apply List.mem_cons_self
    use [], []
    simp
  have deri_rest :
    CFDerives (union_grammar g₁ g₂) [Symbol.nonterminal (some (Sum.inl g₁.initial))]
      (List.map Symbol.terminal w) :=
    by
    have beginning :
      [Symbol.nonterminal (some (Sum.inl g₁.initial))] =
        lsTNOfLsTN₁ [Symbol.nonterminal g₁.initial] :=
      by
      unfold lsTNOfLsTN₁
      change
        [Symbol.nonterminal (some (Sum.inl g₁.initial))] =
          [sTNOfSTN₁ (Symbol.nonterminal g₁.initial)]
      unfold sTNOfSTN₁
    have ending : List.map Symbol.terminal w = lsTNOfLsTN₁ (List.map Symbol.terminal w) :=
      by
      ext1
      unfold lsTNOfLsTN₁
      rw [List.get?_map, List.map_map, List.get?_map]
      apply congr_arg
      rfl
    rw [beginning]
    rw [ending]
    exact deri₁_more (List.map Symbol.terminal w) assum
  unfold cFLanguage
  rw [Set.mem_setOf_eq]
  unfold CFGenerates
  unfold CFGeneratesStr
  unfold CFDerives
  apply CF_deri_of_deri_deri deri_start
  exact deri_rest

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private lemma in_union_of_in_second (w : List T) :
    w ∈ cFLanguage g₂ → w ∈ cFLanguage (unionGrammar g₁ g₂) :=
  by
  intro assum
  have deri_start :
    CFDerives (union_grammar g₁ g₂) [Symbol.nonterminal none]
      [Symbol.nonterminal (some (Sum.inr g₂.initial))] :=
    by
    apply CF_deri_of_tran
    use (none, [Symbol.nonterminal (some (Sum.inr g₂.initial))])
    constructor
    · change
        (none, [Symbol.nonterminal (some (Sum.inr g₂.initial))]) ∈
          (none,
              [Symbol.nonterminal
                  (some
                    (Sum.inl
                      g₁.initial))])::(none,
                [Symbol.nonterminal
                    (some
                      (Sum.inr
                        g₂.initial))])::List.map ruleOfRule₁ g₁.rules ++
                List.map ruleOfRule₂ g₂.rules
      apply List.mem_cons_of_mem
      apply List.mem_cons_self
    use [], []
    simp
  have deri_rest :
    CFDerives (union_grammar g₁ g₂) [Symbol.nonterminal (some (Sum.inr g₂.initial))]
      (List.map Symbol.terminal w) :=
    by
    have beginning :
      [Symbol.nonterminal (some (Sum.inr g₂.initial))] =
        lsTNOfLsTN₂ [Symbol.nonterminal g₂.initial] :=
      by
      unfold lsTNOfLsTN₂
      change
        [Symbol.nonterminal (some (Sum.inr g₂.initial))] =
          [sTNOfSTN₂ (Symbol.nonterminal g₂.initial)]
      unfold sTNOfSTN₂
    have ending : List.map Symbol.terminal w = lsTNOfLsTN₂ (List.map Symbol.terminal w) :=
      by
      ext1
      unfold lsTNOfLsTN₂
      rw [List.get?_map, List.map_map, List.get?_map]
      apply congr_arg
      rfl
    rw [beginning]
    rw [ending]
    exact deri₂_more (List.map Symbol.terminal w) assum
  unfold cFLanguage
  rw [Set.mem_setOf_eq]
  unfold CFGenerates
  unfold CFGeneratesStr
  unfold CFDerives
  apply CF_deri_of_deri_deri deri_start
  exact deri_rest

end LemmataSubset

section LemmataSupset

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def good_singleton : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic good_singleton -/
private lemma in_language_left_case_of_union {w : List T}
    (hypo :
      CFDerives (unionGrammar g₁ g₂) [Symbol.nonterminal (some (Sum.inl g₁.initial))]
        (List.map Symbol.terminal w)) :
    w ∈ cFLanguage g₁ := by
  unfold cFLanguage
  rw [Set.mem_setOf_eq]
  unfold CFGenerates
  unfold CFGeneratesStr
  let gg₁ := @g₁g T g₁ g₂
  have bar :
    [Symbol.nonterminal g₁.initial] =
      sinkString gg₁.sink_nt [Symbol.nonterminal (some (Sum.inl g₁.initial))] :=
    by
    unfold sinkString
    rfl
  rw [bar]
  have baz : List.map Symbol.terminal w = sinkString gg₁.sink_nt (List.map Symbol.terminal w) :=
    by
    unfold sinkString
    rw [List.filterMap_map]
    change
      List.map Symbol.terminal w =
        List.filterMap (fun x => (sinkSymbol gg₁.sink_nt ∘ Symbol.terminal) x) w
    convert_to
      List.map Symbol.terminal w = List.filterMap (fun x => Option.some (Symbol.terminal x)) w
    change List.map Symbol.terminal w = List.filterMap (Option.some ∘ Symbol.terminal) w
    clear hypo
    induction' w with d l
    · rfl
    rw [List.map]
    convert_to
      (Symbol.terminal d::List.map Symbol.terminal l) =
        Symbol.terminal d::List.filterMap (some ∘ Symbol.terminal) l
    norm_num
    exact w_ih
  rw [baz]
  exact
    (sink_deri gg₁ [Symbol.nonterminal (some (Sum.inl g₁.initial))] (List.map Symbol.terminal w)
        hypo
        (by
          run_tac
            good_singleton
          use g₁.initial
          rfl)).left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic good_singleton -/
private lemma in_language_right_case_of_union {w : List T}
    (hypo :
      CFDerives (unionGrammar g₁ g₂) [Symbol.nonterminal (some (Sum.inr g₂.initial))]
        (List.map Symbol.terminal w)) :
    w ∈ cFLanguage g₂ := by
  unfold cFLanguage
  rw [Set.mem_setOf_eq]
  unfold CFGenerates
  unfold CFGeneratesStr
  let gg₂ := @g₂g T g₁ g₂
  have bar :
    [Symbol.nonterminal g₂.initial] =
      sinkString gg₂.sink_nt [Symbol.nonterminal (some (Sum.inr g₂.initial))] :=
    by
    unfold sinkString
    rfl
  rw [bar]
  have baz : List.map Symbol.terminal w = sinkString gg₂.sink_nt (List.map Symbol.terminal w) :=
    by
    unfold sinkString
    rw [List.filterMap_map]
    change
      List.map Symbol.terminal w =
        List.filterMap (fun x => (sinkSymbol gg₂.sink_nt ∘ Symbol.terminal) x) w
    convert_to
      List.map Symbol.terminal w = List.filterMap (fun x => Option.some (Symbol.terminal x)) w
    change List.map Symbol.terminal w = List.filterMap (Option.some ∘ Symbol.terminal) w
    clear hypo
    induction' w with d l
    · rfl
    rw [List.map]
    convert_to
      (Symbol.terminal d::List.map Symbol.terminal l) =
        Symbol.terminal d::List.filterMap (some ∘ Symbol.terminal) l
    norm_num
    exact w_ih
  rw [baz]
  exact
    (sink_deri gg₂ [Symbol.nonterminal (some (Sum.inr g₂.initial))] (List.map Symbol.terminal w)
        hypo
        (by
          run_tac
            good_singleton
          use g₂.initial
          rfl)).left

private lemma both_empty (u v : List (Symbol T (unionGrammar g₁ g₂).Nt))
    (a : Symbol T (unionGrammar g₁ g₂).Nt)
    (bef : [Symbol.nonterminal (unionGrammar g₁ g₂).initial] = u ++ [a] ++ v) : u = [] ∧ v = [] :=
  by
  have len := congr_arg List.length bef
  rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at len 
  constructor
  · by_contra
    rw [← List.length_eq_zero] at h 
    exact
      Nat.not_succ_le_self 1
        (by
          calc
            1 = u.length + 1 + v.length := len
            _ = u.length + (1 + v.length) := (add_assoc (List.length u) 1 (List.length v))
            _ ≥ 1 + (1 + v.length) := (add_le_add (nat.one_le_iff_ne_zero.mpr h) (le_of_eq rfl))
            _ = 1 + 1 + v.length := (Eq.symm (add_assoc 1 1 (List.length v)))
            _ ≥ 1 + 1 + 0 := le_self_add
            _ = 2 := rfl)
  · by_contra
    rw [← List.length_eq_zero] at h 
    exact
      Nat.not_succ_le_self 1
        (by
          calc
            1 = u.length + 1 + v.length := len
            _ ≥ u.length + 1 + 1 := (add_le_add (le_of_eq rfl) (nat.one_le_iff_ne_zero.mpr h))
            _ = u.length + (1 + 1) := (add_assoc (List.length u) 1 1)
            _ ≥ 0 + (1 + 1) := le_add_self
            _ = 0 + 1 + 1 := (Eq.symm (add_assoc 0 1 1))
            _ = 2 := rfl)

private lemma in_language_impossible_case_of_union (w : List T)
    (r : (unionGrammar g₁ g₂).Nt × List (Symbol T (unionGrammar g₁ g₂).Nt))
    (u v : List (Symbol T (unionGrammar g₁ g₂).Nt)) (hu : u = []) (hv : v = [])
    (bef : [Symbol.nonterminal (unionGrammar g₁ g₂).initial] = u ++ [Symbol.nonterminal r.fst] ++ v)
    (sbi : r ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules) :
    w ∈ cFLanguage g₁ ∨ w ∈ cFLanguage g₂ := by
  exfalso
  rw [hu, hv] at bef 
  rw [List.nil_append, List.append_nil] at bef 
  change [Symbol.nonterminal none] = [Symbol.nonterminal r.fst] at bef 
  have rule_root : r.fst = none :=
    haveI almost := List.head_eq_of_cons_eq bef
    Symbol.nonterminal.inj almost.symm
  rw [List.mem_append] at sbi 
  cases sbi
  · rw [List.mem_map] at sbi 
    rcases sbi with ⟨r₁, -, imposs⟩
    unfold ruleOfRule₁ at imposs 
    rw [← imposs] at rule_root 
    unfold Prod.fst at rule_root 
    exact Option.noConfusion rule_root
  · rw [List.mem_map] at sbi 
    rcases sbi with ⟨r₂, -, imposs⟩
    unfold ruleOfRule₂ at imposs 
    rw [← imposs] at rule_root 
    unfold Prod.fst at rule_root 
    exact Option.noConfusion rule_root

private lemma in_language_of_in_union (w : List T) :
    w ∈ cFLanguage (unionGrammar g₁ g₂) → w ∈ cFLanguage g₁ ∨ w ∈ cFLanguage g₂ :=
  by
  intro ass
  cases' CF_eq_or_tranDeri_of_deri ass with impossible h
  · exfalso
    have zeroth := congr_arg (fun p => List.get? p 0) impossible
    unfold List.get? at zeroth 
    rw [List.get?_map] at zeroth 
    cases w.nth 0
    · rw [Option.map_none'] at zeroth 
      exact Option.noConfusion zeroth
    · rw [Option.map_some'] at zeroth 
      exact Symbol.noConfusion (Option.some.inj zeroth)
  rcases h with ⟨S₁, deri_head, deri_tail⟩
  rcases deri_head with ⟨rule, ruleok, u, v, h_bef, h_aft⟩
  rw [h_aft] at deri_tail 
  cases' both_empty u v (Symbol.nonterminal rule.fst) h_bef with u_nil v_nil
  cases' ruleok with g₁S r_rest
  · left
    rw [g₁S] at *
    rw [u_nil] at deri_tail 
    rw [v_nil] at deri_tail 
    rw [List.nil_append] at deri_tail 
    exact in_language_left_case_of_union deri_tail
  cases' r_rest with g₂S r_imposs
  · right
    rw [g₂S] at *
    rw [u_nil] at deri_tail 
    rw [v_nil] at deri_tail 
    rw [List.nil_append] at deri_tail 
    exact in_language_right_case_of_union deri_tail
  exact in_language_impossible_case_of_union w rule u v u_nil v_nil h_bef r_imposs

end LemmataSupset

/-- The class of context-free languages is closed under union. -/
lemma CF_of_CF_u_CF {T : Type} (L₁ : Language T) (L₂ : Language T) :
    IsCF L₁ ∧ IsCF L₂ → IsCF (L₁ + L₂) :=
  by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  use union_grammar g₁ g₂
  apply Set.eq_of_subset_of_subset
  · -- prove `L₁ + L₂ ⊇ `
    intro w hyp
    rw [Language.mem_add]
    rw [← eq_L₁]
    rw [← eq_L₂]
    exact in_language_of_in_union w hyp
  · -- prove `L₁ + L₂ ⊆ `
    intro w hyp
    cases' hyp with case₁ case₂
    · rw [← eq_L₁] at case₁ 
      exact in_union_of_in_first w case₁
    · rw [← eq_L₂] at case₂ 
      exact in_union_of_in_second w case₂
-/
