/-import Project.Classes.ContextFree.Basics.Lifting
import Project.Utilities.WrittenByOthers.TrimAssoc

variable {T : Type}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def combined_grammar (gₗ gᵣ : CFG T) : CFG T :=
  CFG.mk (Option (Sum gₗ.nt gᵣ.nt)) none
    ((none,
        [Symbol.nonterminal (some ◩gₗ.initial)),
          Symbol.nonterminal
            (some
              (Sum.inr
                gᵣ.initial))])::List.map ruleOfRule₁ gₗ.rules ++ List.map ruleOfRule₂ gᵣ.rules)

/-- similar to `sink_symbol` -/
private def oN₁_of_N {g₁ g₂ : CFG T} : (combinedGrammar g₁ g₂).nt → Option g₁.nt
  | none => none
  | some ◩n => some n
  | some ◪_ => none

/-- similar to `sink_symbol` -/
private def oN₂_of_N {g₁ g₂ : CFG T} : (combinedGrammar g₁ g₂).nt → Option g₂.nt
  | none => none
  | some ◩_ => none
  | some ◪n => some n

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private def g₁g (g₁ g₂ : CFG T) : @LiftedGrammar T :=
  LiftedGrammar.mk g₁ (combinedGrammar g₁ g₂) (some ∘ Sum.inl)
    (by
      -- prove `function.injective (some ∘ sum.inl)` here
      intro x y h
      apply Sum.inl_injective
      apply Option.some_injective
      exact h)
    (by
      -- prove `∀ r ∈ g₁.rules` we have `lift_rule (some ∘ sum.inl) r ∈ list.map rule_of_rule₁ g₁.rules` here
      intro r h
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
      change r ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules at r_in
      rw [List.mem_append] at r_in
      cases r_in
      · rw [List.mem_map] at r_in
        rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
        use r₁
        constructor
        · exact r₁_in
        rw [←r₁_convert_r]
        simp only [liftRule, ruleOfRule₁, liftString, lsTNOfLsTN₁, Prod.mk.inj_iff,
          eq_self_iff_true, true_and_iff]
        run_tac
          five_steps
      · exfalso
        rw [List.mem_map] at r_in
        rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
        rw [←r₂_convert_r] at r_ntype
        unfold ruleOfRule₂ at r_ntype
        dsimp only at r_ntype
        cases' r_ntype with n₁ contr
        rw [Option.some_inj] at contr
        exact Sum.noConfusion contr)
    (by intro; rfl)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic five_steps -/
private def g₂g (g₁ g₂ : CFG T) : @LiftedGrammar T :=
  LiftedGrammar.mk g₂ (combinedGrammar g₁ g₂) (some ∘ Sum.inr)
    (by
      -- prove `function.injective (some ∘ sum.inr)` here
      intro x y h
      apply Sum.inr_injective
      apply Option.some_injective
      exact h)
    (by
      -- prove `∀ r ∈ g₂.rules` we have `lift_rule (some ∘ sum.inr) r ∈ list.map rule_of_rule₂ g₂.rules` here
      intro r h
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
      cases r_in
      · exfalso
        rw [r_in] at r_ntype
        dsimp only at r_ntype
        cases' r_ntype with n₀ imposs
        exact Option.noConfusion imposs
      change r ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules at r_in
      rw [List.mem_append] at r_in
      cases r_in
      · exfalso
        rw [List.mem_map] at r_in
        rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
        rw [←r₁_convert_r] at r_ntype
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
        rw [←r₂_convert_r]
        simp only [liftRule, ruleOfRule₂, liftString, lsTNOfLsTN₂, Prod.mk.inj_iff,
          eq_self_iff_true, true_and_iff]
        run_tac
          five_steps)
    (by intro; rfl)

private def oT_of_sTN₃ {g₃ : CFG T} : Symbol T g₃.nt → Option T
  | Symbol.terminal t => some t
  | Symbol.nonterminal _ => none

private def liT_of_lsTN₃ {g₃ : CFG T} : List (Symbol T g₃.nt) → List T :=
  List.filterMap oTOfSTN₃

private lemma u_eq_take_map_w {g₁ g₂ : CFG T} (u : List (Symbol T g₁.nt))
    (v : List (Symbol T g₂.nt)) (w : List T) (len : u.length ≤ w.length)
    (hyp :
      List.take u.length (List.map sTNOfSTN₁ u ++ lsTNOfLsTN₂ v) =
        List.take u.length (List.map Symbol.terminal w)) :
    u = List.take u.length (List.map Symbol.terminal w) :=
  by
  ext1
  by_cases n < u.length
  · have ass : List.map sTNOfSTN₁ u = List.take u.length (List.map Symbol.terminal w) :=
      by
      convert hyp
      have takenl := List.take_left (List.map sTNOfSTN₁ u) (lsTNOfLsTN₂ v)
      rw [List.length_map] at takenl
      exact takenl.symm
    have nth_equ := congr_fun (congr_arg List.get? ass) n
    rw [List.get?_take h]
    rw [List.get?_take h] at nth_equ
    have n_lt_wl : n < w.length := gt_of_ge_of_gt len h
    have triv : n < (List.map sTNOfSTN₁ u).length :=
      by
      rw [List.length_map]
      exact h
    have trig : n < (List.map (@Symbol.terminal T g₁.nt) w).length :=
      by
      rw [List.length_map]
      exact n_lt_wl
    have trin : n < (List.map (@Symbol.terminal T (Option (Sum g₁.nt g₂.nt))) w).length :=
      by
      rw [List.length_map]
      exact n_lt_wl
    rw [List.nthLe_get? triv] at nth_equ
    rw [List.nthLe_get? trin] at nth_equ
    rw [Option.some_inj] at nth_equ
    rw [List.nthLe_map] at nth_equ ; swap
    · exact h
    rw [List.nthLe_map] at nth_equ ; swap
    · exact n_lt_wl
    rw [List.nthLe_get?]; swap
    · exact h
    rw [List.nthLe_get?]; swap
    · exact trig
    apply congr_arg
    norm_num
    cases u.nth_le n h
    · unfold sTNOfSTN₁ at nth_equ
      clear * - nth_equ
      finish
    · exfalso
      exact Symbol.noConfusion nth_equ
  convert_to none = none
  · finish
  · push_neg at h
    rw [List.get?_eq_none]
    rw [List.length_take]
    exact min_le_of_left_le h
  rfl

private lemma v_eq_drop_map_w {g₁ g₂ : CFG T} (u : List (Symbol T g₁.nt))
    (v : List (Symbol T g₂.nt)) (w : List T) (total_len : u.length + v.length = w.length)
    (hyp :
      List.drop u.length (List.map sTNOfSTN₁ u ++ List.map sTNOfSTN₂ v) =
        List.drop u.length (List.map Symbol.terminal w)) :
    v = List.drop u.length (List.map Symbol.terminal w) :=
  by
  ext1
  by_cases n < v.length
  · have nth_equ := congr_fun (congr_arg List.get? hyp) n
    rw [List.get?_drop]
    rw [List.get?_drop] at nth_equ
    rw [List.get?_drop] at nth_equ
    have hunltuv : u.length + n < u.length + v.length := by apply add_lt_add_left h
    have hunltw : u.length + n < w.length :=
      by
      rw [←total_len]
      exact hunltuv
    have hlen₁ : u.length + n < (List.map sTNOfSTN₁ u ++ List.map sTNOfSTN₂ v).length :=
      by
      rw [List.length_append]
      rw [List.length_map]
      rw [List.length_map]
      exact hunltuv
    have hlen₂ :
      u.length + n < (List.map (@Symbol.terminal T (Option (Sum g₁.nt g₂.nt))) w).length :=
      by
      rw [List.length_map]
      exact hunltw
    have hlen₂' : u.length + n < (List.map (@Symbol.terminal T g₂.nt) w).length :=
      by
      rw [List.length_map]
      exact hunltw
    rw [List.nthLe_get? hlen₁] at nth_equ
    rw [List.nthLe_get? hlen₂] at nth_equ
    rw [List.nthLe_get? h]
    rw [List.nthLe_get? hlen₂']
    rw [Option.some_inj] at *
    have hlen₀ : (List.map sTNOfSTN₁ u).length ≤ u.length + n :=
      by
      rw [List.length_map]
      exact le_self_add
    have hlen : n < (List.map (@sTNOfSTN₂ T g₁ g₂) v).length :=
      by
      rw [List.length_map]
      exact h
    have nth_equ_simplified :
      (List.map sTNOfSTN₂ v).nthLe n hlen =
        (List.map Symbol.terminal w).nthLe (u.length + n) hlen₂ :=
      by
      rw [List.nthLe_append_right hlen₀] at nth_equ
      convert nth_equ
      rw [List.length_map]
      symm
      apply add_tsub_cancel_left
    rw [List.nthLe_map] at nth_equ_simplified
    cases' v.nth_le n h with x
    · unfold sTNOfSTN₂ at nth_equ_simplified
      rw [List.nthLe_map _ _ hunltw] at nth_equ_simplified
      rw [List.nthLe_map _ _ hunltw]
      injection nth_equ_simplified with hx
      apply congr_arg
      exact hx
    · exfalso
      clear * - nth_equ_simplified
      finish
  convert_to none = none
  · finish
  · rw [List.get?_drop]
    push_neg at h
    rw [List.get?_eq_none]
    rw [List.length_map]
    rw [←total_len]
    apply add_le_add_left h
  rfl

private def sTN₁_of_sTN {g₁ g₂ : CFG T} :
    Symbol T (Option (Sum g₁.nt g₂.nt)) → Option (Symbol T g₁.nt)
  | Symbol.terminal te => some (Symbol.terminal te)
  | Symbol.nonterminal nont => Option.map Symbol.nonterminal (oN₁OfN nont)

private def sTN₂_of_sTN {g₁ g₂ : CFG T} :
    Symbol T (Option (Sum g₁.nt g₂.nt)) → Option (Symbol T g₂.nt)
  | Symbol.terminal te => some (Symbol.terminal te)
  | Symbol.nonterminal nont => Option.map Symbol.nonterminal (oN₂OfN nont)

private def lsTN₁_of_lsTN {g₁ g₂ : CFG T} (lis : List (Symbol T (Option (Sum g₁.nt g₂.nt)))) :
    List (Symbol T g₁.nt) :=
  List.filterMap sTN₁OfSTN lis

private def lsTN₂_of_lsTN {g₁ g₂ : CFG T} (lis : List (Symbol T (Option (Sum g₁.nt g₂.nt)))) :
    List (Symbol T g₂.nt) :=
  List.filterMap sTN₂OfSTN lis

private lemma self_of_sTN₁ {g₁ g₂ : CFG T} (a : Symbol T g₁.nt) :
    sTN₁OfSTN (@sTNOfSTN₁ _ _ g₂ a) = a := by cases a <;> rfl

private lemma self_of_sTN₂ {g₁ g₂ : CFG T} (a : Symbol T g₂.nt) :
    sTN₂OfSTN (@sTNOfSTN₂ _ g₁ _ a) = a := by cases a <;> rfl

private lemma self_of_lsTN₁ {g₁ g₂ : CFG T} (stri : List (Symbol T g₁.nt)) :
    lsTN₁OfLsTN (@lsTNOfLsTN₁ _ _ g₂ stri) = stri :=
  by
  unfold lsTNOfLsTN₁
  unfold lsTN₁_of_lsTN
  rw [List.filterMap_map]
  change List.filterMap (fun x => sTN₁_of_sTN (sTNOfSTN₁ x)) stri = stri
  convert_to List.filterMap (fun x => some x) stri = stri
  · have equal_functions :
      (fun x : Symbol T g₁.nt => sTN₁_of_sTN (sTNOfSTN₁ x)) = fun x => some x :=
      by
      ext1
      apply self_of_sTN₁
    rw [←equal_functions]
    apply congr_fun
    apply congr_arg
    ext1
    apply congr_fun
    rfl
  apply List.filterMap_some

private lemma self_of_lsTN₂ {g₁ g₂ : CFG T} (stri : List (Symbol T g₂.nt)) :
    lsTN₂OfLsTN (@lsTNOfLsTN₂ _ g₁ _ stri) = stri :=
  by
  unfold lsTNOfLsTN₂
  unfold lsTN₂_of_lsTN
  rw [List.filterMap_map]
  change List.filterMap (fun x => sTN₂_of_sTN (sTNOfSTN₂ x)) stri = stri
  convert_to List.filterMap (fun x => some x) stri = stri
  · have equal_functions :
      (fun x : Symbol T g₂.nt => sTN₂_of_sTN (sTNOfSTN₂ x)) = fun x => some x :=
      by
      ext1
      apply self_of_sTN₂
    rw [←equal_functions]
    apply congr_fun
    apply congr_arg
    ext1
    apply congr_fun
    rfl
  apply List.filterMap_some

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[] -/
private lemma in_concatenated_of_in_combined {g₁ g₂ : CFG T} {w : List T}
    (hyp : w ∈ cFLanguage (combinedGrammar g₁ g₂)) : w ∈ cFLanguage g₁ * cFLanguage g₂ :=
  by
  rw [Language.mem_mul]
  change
    CFDerives (combined_grammar g₁ g₂) [Symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (List.map Symbol.terminal w) at
    hyp
  cases CF_eq_or_tran_deri_of_deri hyp
  · rename' h => refl_contr
    exfalso
    have hh := congr_fun (congr_arg List.get? refl_contr) 0
    rw [List.get?] at hh
    by_cases (List.map (@Symbol.terminal T (combined_grammar g₁ g₂).nt) w).length = 0
    · have empty_none : (List.map Symbol.terminal w).get? 0 = none := by finish
      rw [empty_none] at hh
      exact Option.noConfusion hh
    rw [List.get?_map] at hh
    have hw0 : ∃ s, w.nth 0 = some s := by
      cases w.nth 0
      · exfalso
        exact Option.noConfusion hh
      use val
    rcases hw0 with ⟨s, hs⟩
    rw [hs] at hh
    rw [Option.map_some'] at hh
    rw [Option.some_inj] at hh
    exact Symbol.noConfusion hh
  rcases h with ⟨y, first_step, derivation⟩
  clear hyp
  have only_option :
    y =
      [Symbol.nonterminal (some ◩g₁.initial)),
        Symbol.nonterminal (some ◪g₂.initial))] :=
    by
    rcases first_step with ⟨first_rule, first_rule_in, p, q, bef, aft⟩
    have len_bef := congr_arg List.length bef
    rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at
      len_bef
    have p_nil : p = [] := by
      have p0 : p.length = 0 := by linarith
      rw [List.length_eq_zero] at p0
      exact p0
    have q_nil : q = [] := by
      have q0 : q.length = 0 := by linarith
      rw [List.length_eq_zero] at q0
      exact q0
    have initial : first_rule.fst = none :=
      by
      apply Symbol.nonterminal.inj
      rw [p_nil] at bef
      rw [q_nil] at bef
      rw [List.append_nil] at bef
      rw [List.nil_append] at bef
      exact List.head_eq_of_cons_eq (Eq.symm bef)
    have only_rule :
      first_rule =
        (none,
          [Symbol.nonterminal (some ◩g₁.initial)),
            Symbol.nonterminal (some ◪g₂.initial))]) :=
      by
      change
        first_rule ∈
          (none,
              [Symbol.nonterminal (some ◩g₁.initial)),
                Symbol.nonterminal
                  (some
                    (Sum.inr
                      g₂.initial))])::List.map ruleOfRule₁ g₁.rules ++
              List.map ruleOfRule₂ g₂.rules at
        first_rule_in
      cases first_rule_in
      · exact first_rule_in
      exfalso
      change first_rule ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules at
        first_rule_in
      rw [List.mem_append] at first_rule_in
      cases first_rule_in
      · delta ruleOfRule₁ at first_rule_in
        have rfst :
          first_rule.fst ∈
            List.map Prod.fst
              (List.map
                (fun r : g₁.nt × List (Symbol T g₁.nt) => (some ◩r.fst), lsTNOfLsTN₁ r.snd))
                g₁.rules) :=
          List.mem_map_of_mem Prod.fst first_rule_in
        rw [initial] at rfst
        convert rfst
        simp
      · delta ruleOfRule₂ at first_rule_in
        have rfst :
          first_rule.fst ∈
            List.map Prod.fst
              (List.map
                (fun r : g₂.nt × List (Symbol T g₂.nt) => (some ◪r.fst), lsTNOfLsTN₂ r.snd))
                g₂.rules) :=
          List.mem_map_of_mem Prod.fst first_rule_in
        rw [initial] at rfst
        convert rfst
        simp
    rw [p_nil, q_nil, only_rule] at aft
    rw [List.append_nil] at aft
    rw [List.nil_append] at aft
    exact aft
  clear first_step
  rw [only_option] at derivation
  clear only_option y
  have complicated_induction :
    ∀ x : List (Symbol T (combined_grammar g₁ g₂).nt),
      CFDerives (combined_grammar g₁ g₂)
          [Symbol.nonterminal (some ◩g₁.initial)),
            Symbol.nonterminal (some ◪g₂.initial))]
          x →
        ∃ u : List (Symbol T g₁.nt),
          ∃ v : List (Symbol T g₂.nt),
            And (CFDerives g₁ [Symbol.nonterminal g₁.initial] u)
                (CFDerives g₂ [Symbol.nonterminal g₂.initial] v) ∧
              lsTNOfLsTN₁ u ++ lsTNOfLsTN₂ v = x :=
    by
    intro x ass
    induction' ass with a b trash orig ih
    · use [Symbol.nonterminal g₁.initial], [Symbol.nonterminal g₂.initial]
      constructor
      · constructor <;> apply CF_deri_self
      · rfl
    clear trash
    rcases orig with ⟨orig_rule, orig_in, c, d, bef, aft⟩
    rcases ih with ⟨u, v, ⟨ih₁, ih₂⟩, ih_concat⟩
    cases orig_in
    · exfalso
      rw [←ih_concat] at bef
      rw [orig_in] at bef
      clear * - bef
      dsimp only at bef
      have init_nt_in_bef_right : Symbol.nonterminal none ∈ c ++ [Symbol.nonterminal none] ++ d :=
        by
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_singleton_self
      have init_nt_notin_bef_left : Symbol.nonterminal none ∉ lsTNOfLsTN₁ u ++ lsTNOfLsTN₂ v :=
        by
        rw [List.mem_append]
        push_neg
        constructor
        · rw [List.mem_iff_nthLe]
          push_neg
          unfold lsTNOfLsTN₁
          intro n hn
          rw [List.nthLe_map]
          · cases' u.nth_le n _ with t s
            · apply Symbol.noConfusion
            · unfold sTNOfSTN₁
              intro hypo
              have impossible := Symbol.nonterminal.inj hypo
              exact Option.noConfusion impossible
          · rw [List.length_map] at hn
            exact hn
        · rw [List.mem_iff_nthLe]
          push_neg
          unfold lsTNOfLsTN₂
          intro n hn
          rw [List.nthLe_map]
          · cases' v.nth_le n _ with t s
            · apply Symbol.noConfusion
            · unfold sTNOfSTN₂
              intro hypo
              have impossible := Symbol.nonterminal.inj hypo
              exact Option.noConfusion impossible
          · rw [List.length_map] at hn
            exact hn
      rw [bef] at init_nt_notin_bef_left
      exact init_nt_notin_bef_left init_nt_in_bef_right
    clear derivation w
    change orig_rule ∈ List.map ruleOfRule₁ g₁.rules ++ List.map ruleOfRule₂ g₂.rules at orig_in
    rw [List.mem_append] at orig_in
    cases orig_in
    · rw [List.mem_map] at orig_in
      rcases orig_in with ⟨r₁, r₁_in, r₁_conv⟩
      rw [aft]
      rw [bef] at ih_concat
      clear bef aft a b
      rw [←r₁_conv] at ih_concat ⊢
      clear r₁_conv orig_rule
      have part_for_u := congr_arg (List.take (@lsTNOfLsTN₁ T g₁ g₂ u).length) ih_concat
      have part_for_v := congr_arg (List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length) ih_concat
      rw [List.take_left] at part_for_u
      rw [List.drop_left] at part_for_v
      have h_len : (@lsTNOfLsTN₁ T g₁ g₂ u).length > c.length :=
        by
        by_contra contra
        push_neg at contra
        have not_in : Symbol.nonterminal (ruleOfRule₁ r₁).fst ∉ lsTNOfLsTN₂ v :=
          by
          unfold lsTNOfLsTN₂
          rw [List.mem_map]
          rintro ⟨s, -, imposs⟩
          cases s
          · exact Symbol.noConfusion imposs
          · have inr_eq_inl := Option.some.inj (Symbol.nonterminal.inj imposs)
            exact Sum.noConfusion inr_eq_inl
        have yes_in : Symbol.nonterminal (@ruleOfRule₁ T g₁ g₂ r₁).fst ∈ lsTNOfLsTN₂ v :=
          by
          have lcth := congr_fun (congr_arg List.get? ih_concat) c.length
          rw [List.append_assoc c] at lcth
          have clength :
            (c ++ ([Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d)).get? c.length =
              some (Symbol.nonterminal (@ruleOfRule₁ T g₁ g₂ r₁).fst) :=
            by
            rw [List.get?_append_right]; swap
            · rfl
            rw [Nat.sub_self]
            rfl
          rw [clength] at lcth
          rw [List.get?_append_right contra] at lcth
          exact List.get?_mem lcth
        exact not_in yes_in
      -- nonterminal was rewritten in the left half of `a` ... upgrade `u`
      let d' : List (Symbol T (combined_grammar g₁ g₂).nt) :=
        List.take ((@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1)) d
      let u' := lsTN₁_of_lsTN (c ++ (ruleOfRule₁ r₁).snd ++ d')
      use u'
      use v
      constructor
      · constructor
        · change
            CFDerives g₁ [Symbol.nonterminal g₁.initial]
              (lsTN₁_of_lsTN
                (c ++ (ruleOfRule₁ r₁).snd ++
                  List.take ((lsTNOfLsTN₁ u).length - (c.length + 1)) d))
          apply CF_deri_of_deri_tran ih₁
          convert_to
            CFTransforms g₁
              (lsTN₁_of_lsTN
                (List.take (lsTNOfLsTN₁ u).length
                  (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d)))
              (lsTN₁_of_lsTN
                (c ++ (ruleOfRule₁ r₁).snd ++
                  List.take ((lsTNOfLsTN₁ u).length - (c.length + 1)) d))
          · rw [←part_for_u]
            rw [self_of_lsTN₁]
          use r₁
          constructor
          · exact r₁_in
          use lsTN₁_of_lsTN c
          use lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d)
          constructor
          · convert_to
              lsTN₁_of_lsTN
                  (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++
                    List.take (u.length - (c.length + 1)) d) =
                lsTN₁_of_lsTN c ++ [Symbol.nonterminal r₁.fst] ++
                  lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d)
            · apply congr_arg
              have trivi_len : (lsTNOfLsTN₁ u).length = u.length :=
                by
                unfold lsTNOfLsTN₁
                rw [List.length_map]
              rw [trivi_len]
              have another_trivi_len :
                c.length + 1 = (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length :=
                by
                rw [List.length_append]
                rw [List.length_singleton]
              rw [another_trivi_len]
              have borrow_and_return :
                u.length =
                  (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length +
                    (u.length - (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length) :=
                by
                symm
                clear * - h_len
                apply Nat.add_sub_of_le
                rw [List.length_append]
                rw [List.length_singleton]
                unfold lsTNOfLsTN₁ at h_len
                rw [List.length_map] at h_len
                rw [Nat.succ_le_iff]
                exact h_len
              convert_to
                List.take
                    ((c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length +
                      (u.length - (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length))
                    (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d) =
                  c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++
                    List.take (u.length - (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length) d
              · apply congr_fun
                apply congr_arg
                exact borrow_and_return
              rw [List.take_append]
            unfold lsTN₁_of_lsTN
            rw [List.filterMap_append_append]
            rfl
          · convert_to
              lsTN₁_of_lsTN (c ++ (ruleOfRule₁ r₁).snd ++ List.take (u.length - (c.length + 1)) d) =
                lsTN₁_of_lsTN c ++ r₁.snd ++ lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d)
            · apply congr_arg
              trace
                "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
              unfold lsTNOfLsTN₁
              rw [List.length_map]
            unfold lsTN₁_of_lsTN
            rw [List.filterMap_append_append]
            change
              List.filterMap sTN₁_of_sTN c ++ lsTN₁_of_lsTN (lsTNOfLsTN₁ r₁.snd) ++
                  List.filterMap sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d) =
                List.filterMap sTN₁_of_sTN c ++ r₁.snd ++
                  List.filterMap sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d)
            rw [self_of_lsTN₁]
        · exact ih₂
      · have trivi_min :
          min ((@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1)) d.length =
            (@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1) :=
          by
          apply min_eq_left
          unfold lsTNOfLsTN₁
          rw [List.length_map]
          clear * - part_for_u
          unfold lsTNOfLsTN₁ at part_for_u
          have lengs := congr_arg List.length part_for_u
          rw [List.length_map] at lengs
          rw [List.length_take] at lengs
          rw [List.length_append] at lengs
          rw [List.length_append] at lengs
          rw [List.length_singleton] at lengs
          have uleng_le : u.length ≤ c.length + 1 + d.length :=
            by
            rw [←min_eq_left_iff]
            exact lengs.symm
          clear * - uleng_le
          omega
        have c_converted_and_back : List.map sTNOfSTN₁ (List.filterMap sTN₁_of_sTN c) = c :=
          by
          /-
            Simplified schema of this conversion (applies to some other conversions, too):
            we have `g ∘ f = id` but `f ∘ g` does not annihilate (in general)
            we need `(f ∘ g)(c) = c` for a specific `c`
            which we can express as `c = f(x)` and then
            we calculate `f(g(c)) = f(g(f(x))) = f(x) = c` hooray!
          -/
          have taken_c_from_u := congr_arg (List.take c.length) part_for_u
          rw [List.take_take] at taken_c_from_u
          rw [min_eq_left (le_of_lt h_len)] at taken_c_from_u
          rw [List.append_assoc] at taken_c_from_u
          rw [List.take_left] at taken_c_from_u
          convert_to
            List.map sTNOfSTN₁ (List.filterMap sTN₁_of_sTN (List.take c.length (lsTNOfLsTN₁ u))) = c
          · rw [taken_c_from_u]
          unfold lsTNOfLsTN₁
          rw [←List.map_take]
          change List.map sTNOfSTN₁ (lsTN₁_of_lsTN (lsTNOfLsTN₁ (List.take c.length u))) = _
          rw [self_of_lsTN₁]
          rw [List.map_take]
          exact taken_c_from_u
        have d_converted_and_back :
          List.map sTNOfSTN₁
              (List.filterMap sTN₁_of_sTN
                (List.take ((List.map (@sTNOfSTN₁ T g₁ g₂) u).length - (c.length + 1)) d)) =
            List.take ((List.map (@sTNOfSTN₁ T g₁ g₂) u).length - (c.length + 1)) d :=
          by
          have taken_d_from_dropped_u := congr_arg (List.drop (c.length + 1)) part_for_u
          have for_the_decomposition :
            (@lsTNOfLsTN₁ T g₁ g₂ u).length =
              c.length + 1 + ((@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1)) :=
            by
            symm
            apply Nat.add_sub_of_le
            exact Nat.succ_le_of_lt h_len
          rw [for_the_decomposition] at taken_d_from_dropped_u
          rw [List.drop_take] at taken_d_from_dropped_u
          have translate_counts :
            c.length + 1 = (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length :=
            by
            rw [List.length_append]
            rw [List.length_singleton]
          rw [translate_counts] at taken_d_from_dropped_u
          rw [List.drop_left] at taken_d_from_dropped_u
          rw [←translate_counts] at taken_d_from_dropped_u
          change
            List.map sTNOfSTN₁
                (List.filterMap sTN₁_of_sTN
                  (List.take ((@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1)) d)) =
              _
          rw [←taken_d_from_dropped_u]
          change
            List.map sTNOfSTN₁ (lsTN₁_of_lsTN (List.drop (c.length + 1) (List.map sTNOfSTN₁ u))) = _
          rw [←List.map_drop]
          change List.map sTNOfSTN₁ (lsTN₁_of_lsTN (lsTNOfLsTN₁ (List.drop (c.length + 1) u))) = _
          rw [self_of_lsTN₁]
          rw [List.map_drop]
          exact taken_d_from_dropped_u
        have len_u' : u'.length = c.length + (@ruleOfRule₁ T g₁ g₂ r₁).snd.length + d'.length :=
          by
          change
            (lsTN₁_of_lsTN (c ++ (ruleOfRule₁ r₁).snd ++ d')).length =
              c.length + (ruleOfRule₁ r₁).snd.length + d'.length
          unfold lsTN₁_of_lsTN
          rw [List.filterMap_append_append]
          convert_to
            (List.map sTNOfSTN₁
                  (List.filterMap sTN₁_of_sTN c ++
                      List.filterMap sTN₁_of_sTN (ruleOfRule₁ r₁).snd ++
                    List.filterMap sTN₁_of_sTN d')).length =
              c.length + (ruleOfRule₁ r₁).snd.length + d'.length
          · rw [List.length_map]
          rw [List.map_append_append]
          rw [c_converted_and_back]
          change
            (c ++ _ ++
                  List.map sTNOfSTN₁
                    (List.filterMap sTN₁_of_sTN
                      (List.take ((List.map (@sTNOfSTN₁ T g₁ g₂) u).length - (c.length + 1))
                        d))).length =
              _
          rw [d_converted_and_back]
          change (c ++ List.map sTNOfSTN₁ (lsTN₁_of_lsTN (lsTNOfLsTN₁ r₁.snd)) ++ d').length = _
          rw [self_of_lsTN₁]
          rw [List.length_append]
          rw [List.length_append]
          rfl
        have express_u'_as_crd :
          lsTNOfLsTN₁ u' =
            List.take (@lsTNOfLsTN₁ T g₁ g₂ u').length (c ++ (ruleOfRule₁ r₁).snd ++ d) :=
          by
          change
            lsTNOfLsTN₁
                (lsTN₁_of_lsTN
                  (c ++ (ruleOfRule₁ r₁).snd ++
                    List.take ((lsTNOfLsTN₁ u).length - (c.length + 1)) d)) =
              List.take (lsTNOfLsTN₁ u').length (c ++ (ruleOfRule₁ r₁).snd ++ d)
          convert_to
            c ++ (ruleOfRule₁ r₁).snd ++ List.take ((lsTNOfLsTN₁ u).length - (c.length + 1)) d =
              List.take (lsTNOfLsTN₁ u').length (c ++ (ruleOfRule₁ r₁).snd ++ d)
          · unfold lsTN₁_of_lsTN
            rw [List.filterMap_append_append]
            unfold lsTNOfLsTN₁
            rw [List.map_append_append]
            rw [c_converted_and_back]
            rw [d_converted_and_back]
            change c ++ List.map sTNOfSTN₁ (lsTN₁_of_lsTN (lsTNOfLsTN₁ r₁.snd)) ++ _ = _
            rw [self_of_lsTN₁]
            rfl
          have len_add_sub :
            (@lsTNOfLsTN₁ T g₁ g₂ u').length =
              (c ++ (ruleOfRule₁ r₁).snd).length +
                ((@lsTNOfLsTN₁ T g₁ g₂ u').length - (c ++ (ruleOfRule₁ r₁).snd).length) :=
            by
            symm
            apply Nat.add_sub_of_le
            unfold lsTNOfLsTN₁
            rw [List.length_map]
            rw [len_u']
            rw [List.length_append]
            apply le_self_add
          rw [len_add_sub]
          rw [List.take_append]
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
          rw [List.length_append]
          apply congr_arg₂; swap
          · rfl
          rw [lsTNOfLsTN₁, List.length_map, List.length_map, len_u', List.length_take,
            Nat.add_sub_cancel_left, trivi_min, lsTNOfLsTN₁, List.length_map]
        rw [express_u'_as_crd]
        have identity_of_suffixes :
          List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length
              (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d) =
            List.drop (@lsTNOfLsTN₁ T g₁ g₂ u').length (c ++ (ruleOfRule₁ r₁).snd ++ d) :=
          by
          clear * - h_len trivi_min len_u'
          have h_len_ :
            (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length ≤
              (@lsTNOfLsTN₁ T g₁ g₂ u).length :=
            by
            rw [List.length_append]
            rw [List.length_singleton]
            apply Nat.succ_le_of_lt
            exact h_len
          have intermediate :
            List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length
                (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d) =
              List.drop ((@lsTNOfLsTN₁ T g₁ g₂ u).length - (c.length + 1)) d :=
            by
            convert_to
              List.drop
                  ((c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length +
                    ((lsTNOfLsTN₁ u).length -
                      (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst]).length))
                  (c ++ [Symbol.nonterminal (ruleOfRule₁ r₁).fst] ++ d) =
                List.drop ((lsTNOfLsTN₁ u).length - (c.length + 1)) d
            · symm
              apply congr_arg₂; swap
              · rfl
              apply Nat.add_sub_of_le
              exact h_len_
            rw [List.drop_append]
            apply congr_arg₂; swap
            · rfl
            rw [List.length_append]
            rw [List.length_singleton]
          rw [intermediate]
          change _ = List.drop (List.map sTNOfSTN₁ u').length (c ++ (ruleOfRule₁ r₁).snd ++ d)
          rw [List.length_map]
          rw [len_u']
          rw [←List.length_append]
          rw [List.drop_append]
          rw [List.length_take]
          rw [trivi_min]
        rw [part_for_v]
        rw [identity_of_suffixes]
        apply List.take_append_drop
    · rw [List.mem_map] at orig_in
      rcases orig_in with ⟨r₂, r₂_in, r₂_conv⟩
      rw [aft]
      rw [bef] at ih_concat
      clear bef aft a b
      rw [←r₂_conv] at ih_concat ⊢
      clear r₂_conv orig_rule
      have part_for_u := congr_arg (List.take (@lsTNOfLsTN₁ T g₁ g₂ u).length) ih_concat
      have part_for_v := congr_arg (List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length) ih_concat
      rw [List.take_left] at part_for_u
      rw [List.drop_left] at part_for_v
      have hlen_vd : (@lsTNOfLsTN₂ T g₁ g₂ v).length > d.length :=
        by
        by_contra contra
        push_neg at contra
        have not_in : Symbol.nonterminal (ruleOfRule₂ r₂).fst ∉ lsTNOfLsTN₁ u :=
          by
          unfold lsTNOfLsTN₁
          rw [List.mem_map]
          rintro ⟨s, -, imposs⟩
          cases s
          · exact Symbol.noConfusion imposs
          · have inl_eq_inr := Option.some.inj (Symbol.nonterminal.inj imposs)
            exact Sum.noConfusion inl_eq_inr
        have yes_in : Symbol.nonterminal (ruleOfRule₂ r₂).fst ∈ lsTNOfLsTN₁ u :=
          by
          have ih_backwards := congr_arg List.reverse ih_concat
          repeat rw [List.reverse_append] at ih_backwards
          have ldth := congr_fun (congr_arg List.get? ih_backwards) d.length
          have dlengthth :
            (d.reverse ++ ([Symbol.nonterminal (ruleOfRule₂ r₂).fst].reverse ++ c.reverse)).get?
                d.length =
              some (Symbol.nonterminal (ruleOfRule₂ r₂).fst) :=
            by
            rw [List.get?_append_right]; swap
            · rw [List.length_reverse]
            rw [List.length_reverse]
            rw [Nat.sub_self]
            rfl
          rw [dlengthth] at ldth
          rw [←List.length_reverse] at contra
          rw [List.get?_append_right contra] at ldth
          have rrr := List.get?_mem ldth
          rw [List.mem_reverse'] at rrr
          exact rrr
        exact not_in yes_in
      have total_length := congr_arg List.length ih_concat
      repeat rw [List.length_append] at total_length
      rw [List.length_singleton] at total_length
      have hlen_uc : (@lsTNOfLsTN₁ T g₁ g₂ u).length ≤ c.length :=
        by
        by_contra too_long
        push_neg at too_long
        have imposs_gt_self : c.length + 1 + d.length > c.length + 1 + d.length := by
          calc
            c.length + 1 + d.length =
                (@lsTNOfLsTN₁ T g₁ g₂ u).length + (@lsTNOfLsTN₂ T g₁ g₂ v).length :=
              total_length.symm
            _ > (@lsTNOfLsTN₁ T g₁ g₂ u).length + d.length := (add_lt_add_left hlen_vd _)
            _ ≥ c.length + d.length + 1 := by apply Nat.succ_le_of_lt;
              apply add_lt_add_right too_long
            _ = c.length + 1 + d.length := Nat.add_right_comm _ _ _
        exact Nat.lt_irrefl _ imposs_gt_self
      have hlen_uc_orig : u.length ≤ c.length :=
        by
        unfold lsTNOfLsTN₁ at hlen_uc
        rw [List.length_map] at hlen_uc
        exact hlen_uc
      -- nonterminal was rewritten in the right half of `a` ... upgrade `v`
      let c' : List (Symbol T (combined_grammar g₁ g₂).nt) :=
        List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length c
      let v' := lsTN₂_of_lsTN (c' ++ (ruleOfRule₂ r₂).snd ++ d)
      use u
      use v'
      constructor
      · constructor
        · exact ih₁
        · change
            CFDerives g₂ [Symbol.nonterminal g₂.initial]
              (@lsTN₂_of_lsTN T g₁ g₂
                (List.drop (lsTNOfLsTN₁ u).length c ++ (ruleOfRule₂ r₂).snd ++ d))
          apply CF_deri_of_deri_tran ih₂
          convert_to
            CFTransforms g₂
              (lsTN₂_of_lsTN
                (List.drop (lsTNOfLsTN₁ u).length
                  (c ++ [Symbol.nonterminal (ruleOfRule₂ r₂).fst] ++ d)))
              (lsTN₂_of_lsTN (List.drop (lsTNOfLsTN₁ u).length c ++ (ruleOfRule₂ r₂).snd ++ d))
          · rw [←part_for_v]
            rw [self_of_lsTN₂]
          use r₂
          constructor
          · exact r₂_in
          use lsTN₂_of_lsTN c'
          use lsTN₂_of_lsTN d
          have eq_c' : List.drop u.length c = c' :=
            by
            change List.drop u.length c = List.drop (List.map (@sTNOfSTN₁ T g₁ g₂) u).length c
            rw [List.length_map]
          constructor
          · unfold lsTNOfLsTN₁
            rw [List.length_map]
            unfold lsTN₂_of_lsTN
            rw [List.append_assoc]
            rw [List.drop_append_of_le_length hlen_uc_orig]
            rw [←List.append_assoc]
            rw [List.filterMap_append_append]
            rw [eq_c']
            rfl
          · unfold lsTNOfLsTN₁
            rw [List.length_map]
            unfold lsTN₂_of_lsTN
            rw [List.filterMap_append_append]
            change
              List.filterMap sTN₂_of_sTN (List.drop u.length c) ++
                    lsTN₂_of_lsTN (lsTNOfLsTN₂ r₂.snd) ++
                  List.filterMap sTN₂_of_sTN d =
                List.filterMap sTN₂_of_sTN c' ++ r₂.snd ++ List.filterMap sTN₂_of_sTN d
            rw [self_of_lsTN₂]
            rw [eq_c']
      · have identity_of_prefixes :
          List.take (@lsTNOfLsTN₁ T g₁ g₂ u).length
              (c ++ [Symbol.nonterminal (ruleOfRule₂ r₂).fst] ++ d) =
            List.take (@lsTNOfLsTN₁ T g₁ g₂ u).length (c ++ (ruleOfRule₂ r₂).snd ++ d) :=
          by-- both are equal to `list.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length c`
          repeat
            rw [List.append_assoc]
            rw [List.take_append_of_le_length hlen_uc]
        have express_v'_as_crd :
          lsTNOfLsTN₂ v' =
            List.drop (@lsTNOfLsTN₁ T g₁ g₂ u).length (c ++ (ruleOfRule₂ r₂).snd ++ d) :=
          by
          change
            List.map sTNOfSTN₂
                (List.filterMap sTN₂_of_sTN
                  (List.drop (lsTNOfLsTN₁ u).length c ++ (ruleOfRule₂ r₂).snd ++ d)) =
              List.drop (lsTNOfLsTN₁ u).length (c ++ (ruleOfRule₂ r₂).snd ++ d)
          rw [List.filterMap_append_append]
          rw [List.map_append_append]
          rw [List.append_assoc c]
          rw [List.drop_append_of_le_length hlen_uc]
          rw [←List.append_assoc]
          apply congr_arg₂; apply congr_arg₂
          · have aux_plus_minus :
              (lsTNOfLsTN₁ u).length + (c.length - (lsTNOfLsTN₁ u).length) = c.length :=
              by
              rw [←Nat.add_sub_assoc hlen_uc]
              rw [Nat.add_sub_cancel_left]
            have taken_c_from_v :=
              congr_arg (List.take (c.length - (@lsTNOfLsTN₁ T g₁ g₂ u).length)) part_for_v
            rw [←List.drop_take] at taken_c_from_v
            rw [List.append_assoc] at taken_c_from_v
            rw [List.take_append_of_le_length (le_of_eq aux_plus_minus)] at taken_c_from_v
            rw [aux_plus_minus] at taken_c_from_v
            rw [List.take_length] at taken_c_from_v
            rw [←taken_c_from_v]
            unfold lsTNOfLsTN₂
            rw [←List.map_take]
            change
              lsTNOfLsTN₂
                  (lsTN₂_of_lsTN (lsTNOfLsTN₂ (List.take (c.length - (lsTNOfLsTN₁ u).length) v))) =
                lsTNOfLsTN₂ (List.take (c.length - (lsTNOfLsTN₁ u).length) v)
            rw [self_of_lsTN₂]
          · unfold ruleOfRule₂
            change lsTNOfLsTN₂ (lsTN₂_of_lsTN (lsTNOfLsTN₂ r₂.snd)) = lsTNOfLsTN₂ r₂.snd
            rw [self_of_lsTN₂]
          · have taken_d_from_v :=
              congr_arg (List.drop ((@lsTNOfLsTN₂ T g₁ g₂ v).length - d.length)) part_for_v
            rw [List.drop_drop] at taken_d_from_v
            have dropped_exactly_length :
              (@lsTNOfLsTN₂ T g₁ g₂ v).length - d.length + (@lsTNOfLsTN₁ T g₁ g₂ u).length =
                (c ++ [Symbol.nonterminal (ruleOfRule₂ r₂).fst]).length :=
              by
              rw [List.length_append]
              rw [List.length_singleton]
              have reorder_sum :
                (lsTNOfLsTN₂ v).length - d.length + (lsTNOfLsTN₁ u).length =
                  (lsTNOfLsTN₁ u).length + (lsTNOfLsTN₂ v).length - d.length :=
                by
                rw [Nat.add_sub_assoc]
                apply Nat.add_comm
                apply le_of_lt
                exact hlen_vd
              rw [reorder_sum]
              rw [total_length]
              apply Nat.add_sub_cancel
            rw [dropped_exactly_length] at taken_d_from_v
            rw [List.drop_left] at taken_d_from_v
            rw [←taken_d_from_v]
            unfold lsTNOfLsTN₂
            rw [←List.map_drop]
            change
              lsTNOfLsTN₂
                  (lsTN₂_of_lsTN
                    (lsTNOfLsTN₂ (List.drop ((List.map sTNOfSTN₂ v).length - d.length) v))) =
                lsTNOfLsTN₂ (List.drop ((List.map sTNOfSTN₂ v).length - d.length) v)
            rw [self_of_lsTN₂]
        rw [part_for_u]
        rw [identity_of_prefixes]
        rw [express_v'_as_crd]
        apply List.take_append_drop
  specialize complicated_induction (List.map Symbol.terminal w) Derivation
  rcases complicated_induction with ⟨u, v, ⟨hu, hv⟩, hw⟩
  use liT_of_lsTN₃ u
  use liT_of_lsTN₃ v
  have huvw :
    @liT_of_lsTN₃ T (combined_grammar g₁ g₂) (lsTNOfLsTN₁ u ++ lsTNOfLsTN₂ v) =
      liT_of_lsTN₃ (List.map Symbol.terminal w) :=
    congr_arg liT_of_lsTN₃ hw
  constructor
  · change CFDerives _ _ _
    unfold liT_of_lsTN₃
    convert hu
    have u_from_terminals : ∃ uₜ : List T, u = List.map Symbol.terminal uₜ :=
      by
      unfold lsTNOfLsTN₁ at hw
      use List.take u.length w
      rw [List.map_take]
      exact
        u_eq_take_map_w u v w
          (by
            have hwlen := congr_arg List.length hw
            rw [List.length_append] at hwlen
            rw [List.length_map] at hwlen
            rw [List.length_map] at hwlen
            exact Nat.le.intro hwlen)
          (congr_arg (List.take u.length) hw)
    cases' u_from_terminals with uₜ hut
    rw [hut]
    rw [List.filterMap_map]
    convert_to List.map Symbol.terminal (List.filterMap some uₜ) = List.map Symbol.terminal uₜ
    rw [List.filterMap_some]
  constructor
  · change CFDerives _ _ _
    unfold liT_of_lsTN₃
    convert hv
    have v_from_terminals : ∃ vₜ : List T, v = List.map Symbol.terminal vₜ :=
      by
      unfold lsTNOfLsTN₁ at hw
      unfold lsTNOfLsTN₂ at hw
      use List.drop u.length w
      rw [List.map_drop]
      have hwlen := congr_arg List.length hw
      rw [List.length_append] at hwlen
      repeat rw [List.length_map] at hwlen
      exact v_eq_drop_map_w u v w hwlen (congr_arg (List.drop u.length) hw)
    cases' v_from_terminals with vₜ hvt
    rw [hvt]
    rw [List.filterMap_map]
    convert_to List.map Symbol.terminal (List.filterMap some vₜ) = List.map Symbol.terminal vₜ
    rw [List.filterMap_some]
  unfold liT_of_lsTN₃ at huvw
  rw [List.filterMap_append] at huvw
  unfold lsTNOfLsTN₁ at huvw
  unfold lsTNOfLsTN₂ at huvw
  repeat rw [List.filterMap_map] at huvw
  have disappear_sTN_of_sTN₁ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTNOfSTN₁ = oT_of_sTN₃ :=
    by
    ext1
    cases x <;> rfl
  have disappear_sTN_of_sTN₂ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTNOfSTN₂ = oT_of_sTN₃ :=
    by
    ext1
    cases x <;> rfl
  rw [disappear_sTN_of_sTN₁] at huvw
  rw [disappear_sTN_of_sTN₂] at huvw
  unfold liT_of_lsTN₃
  convert huvw
  have bundle_unbundle : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ Symbol.terminal = Option.some :=
    by
    ext1
    rfl
  rw [bundle_unbundle]
  rw [List.filterMap_some]

private lemma in_combined_of_in_concatenated {g₁ g₂ : CFG T} {w : List T}
    (hyp : w ∈ cFLanguage g₁ * cFLanguage g₂) : w ∈ cFLanguage (combinedGrammar g₁ g₂) :=
  by
  rw [Language.mem_mul] at hyp
  rcases hyp with ⟨u, v, hu, hv, hw⟩
  unfold cFLanguage at *
  change
    CFDerives (combined_grammar g₁ g₂) [Symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (List.map Symbol.terminal w)
  apply
    @CF_deri_of_tran_deri T (combined_grammar g₁ g₂) _
      [Symbol.nonterminal (some ◩g₁.initial)),
        Symbol.nonterminal (some ◪g₂.initial))]
      _
  · use
      (none,
        [Symbol.nonterminal (some ◩g₁.initial)),
          Symbol.nonterminal (some ◪g₂.initial))])
    constructor
    · apply List.mem_cons_self
    use [], []
    constructor <;> rfl
  rw [←hw]
  rw [List.map_append]
  apply
    @CF_deri_of_deri_deri T (combined_grammar g₁ g₂) _
      (List.map Symbol.terminal u ++ [Symbol.nonterminal (some ◪g₂.initial))]) _
  · change
      CFDerives (combined_grammar g₁ g₂)
        ([Symbol.nonterminal (some ◩g₁.initial))] ++
          [Symbol.nonterminal (some ◪g₂.initial))])
        (List.map Symbol.terminal u ++ [Symbol.nonterminal (some ◪g₂.initial))])
    apply CF_deri_append
    change CFDerives g₁ [Symbol.nonterminal g₁.initial] (List.map Symbol.terminal u) at hu
    let gg₁ := g₁g g₁ g₂
    change
      CFDerives gg₁.g [Symbol.nonterminal (some ◩g₁.initial))] (List.map Symbol.terminal u)
    have ini_equ :
      [Symbol.nonterminal (some ◩g₁.initial))] =
        List.map (liftSymbol gg₁.lift_nt) [Symbol.nonterminal g₁.initial] :=
      by apply List.singleton_eq
    rw [ini_equ]
    have baz :
      List.map Symbol.terminal u = List.map (liftSymbol gg₁.lift_nt) (List.map Symbol.terminal u) :=
      by
      rw [List.map_map]
      apply congr_fun
      apply congr_arg
      rfl
    rw [baz]
    exact lift_deri hu
  · apply CF_append_deri
    change CFDerives g₂ [Symbol.nonterminal g₂.initial] (List.map Symbol.terminal v) at hv
    let gg₂ := g₂g g₁ g₂
    change
      CFDerives gg₂.g [Symbol.nonterminal (some ◪g₂.initial))] (List.map Symbol.terminal v)
    have ini_equ :
      [Symbol.nonterminal (some ◪g₂.initial))] =
        List.map (liftSymbol gg₂.lift_nt) [Symbol.nonterminal g₂.initial] :=
      by apply List.singleton_eq
    rw [ini_equ]
    have baz :
      List.map Symbol.terminal v = List.map (liftSymbol gg₂.lift_nt) (List.map Symbol.terminal v) :=
      by
      rw [List.map_map]
      apply congr_fun
      apply congr_arg
      rfl
    rw [baz]
    exact lift_deri hv

/-- The class of context-free languages is closed under concatenation. -/
lemma CF_of_CF_c_CF (L₁ : Language T) (L₂ : Language T) : L₁.IsCF ∧ L₂.IsCF → (L₁ * L₂).IsCF :=
  by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  use combined_grammar g₁ g₂
  apply Set.eq_of_subset_of_subset
  · -- prove `L₁ * L₂ ⊇ ` here
    intro w hyp
    rw [←eq_L₁]
    rw [←eq_L₂]
    exact in_concatenated_of_in_combined hyp
  · -- prove `L₁ * L₂ ⊆ ` here
    intro w hyp
    rw [←eq_L₁] at hyp
    rw [←eq_L₂] at hyp
    exact in_combined_of_in_concatenated hyp
-/
