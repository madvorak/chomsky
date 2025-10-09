/-import Project.Classes.ContextFree.Basics.Pumping
import Project.Classes.ContextFree.Basics.Elementary
import Project.Classes.ContextFree.ClosureProperties.Concatenation
import Project.Classes.ContextFree.ClosureProperties.Permutation

section DefsOverFin3

private def a_ : Fin 3 :=
  0

private def b_ : Fin 3 :=
  1

private def c_ : Fin 3 :=
  2

private def a : Symbol (Fin 3) (Fin 1) :=
  Symbol.terminal a_

private def b : Symbol (Fin 3) (Fin 1) :=
  Symbol.terminal b_

private def c : Symbol (Fin 3) (Fin 1) :=
  Symbol.terminal c_

private lemma neq_ab : a_ ≠ b_ := by decide

private lemma neq_ba : b_ ≠ a_ :=
  neq_ab.symm

private lemma neq_ac : a_ ≠ c_ := by decide

private lemma neq_ca : c_ ≠ a_ :=
  neq_ac.symm

private lemma neq_bc : b_ ≠ c_ := by decide

private lemma neq_cb : c_ ≠ b_ :=
  neq_bc.symm

private def lang_eq_any : Language (Fin 3) := fun w =>
  ∃ n m : ℕ, w = List.replicate n a_ ++ List.replicate n b_ ++ List.replicate m c_

private def lang_any_eq : Language (Fin 3) := fun w =>
  ∃ n m : ℕ, w = List.replicate n a_ ++ List.replicate m b_ ++ List.replicate m c_

private def lang_eq_eq : Language (Fin 3) := fun w =>
  ∃ n : ℕ, w = List.replicate n a_ ++ List.replicate n b_ ++ List.replicate n c_

end DefsOverFin3

section NotCF

private lemma false_of_uvvxyyz {_a _b _c : Fin 3} {n : ℕ} {u v x y z : List (Fin 3)}
    (elimin : ∀ s : Fin 3, s ≠ _a → s ≠ _b → s ≠ _c → False) (no_a : _a ∉ v ++ y)
    (nonempty : (v ++ y).length > 0)
    (counts_ab : ∀ w : List (Fin 3), w ∈ langEqEq → List.countIn w _a = List.countIn w _b)
    (counts_ac : ∀ w : List (Fin 3), w ∈ langEqEq → List.countIn w _a = List.countIn w _c)
    (counted_a :
      List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _a = n + 1 + List.countIn (v ++ y) _a)
    (counted_b :
      List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _b = n + 1 + List.countIn (v ++ y) _b)
    (counted_c :
      List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _c = n + 1 + List.countIn (v ++ y) _c)
    (pumping : u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z ∈ langEqEq) : False :=
  by
  have extra_not_a : _b ∈ v ++ y ∨ _c ∈ v ++ y :=
    by
    let first_letter := (v ++ y).nthLe 0 Nonempty
    have first_letter_b_or_c : first_letter = _b ∨ first_letter = _c :=
      by
      have first_letter_not_a : first_letter ≠ _a :=
        by
        by_contra contra
        have yes_a : _a ∈ v ++ y := by
          rw [← contra]
          apply List.nthLe_mem
        exact no_a yes_a
      by_contra contr
      push_neg at contr
      cases' contr with first_letter_not_b first_letter_not_c
      exact
        elimin ((v ++ y).nthLe 0 Nonempty) first_letter_not_a first_letter_not_b first_letter_not_c
    cases' first_letter_b_or_c with first_letter_b first_letter_c
    · left
      rw [← first_letter_b]
      apply List.nthLe_mem
    · right
      rw [← first_letter_c]
      apply List.nthLe_mem
  have hab := counts_ab (u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z) pumping
  have hac := counts_ac (u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z) pumping
  cases' pumping with n' pump'
  have count_a : List.countIn (u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z) _a = n + 1 :=
    by
    unfold List.nTimes
    simp [-List.append_assoc]
    repeat' rw [List.countIn_append]
    have rearrange :
      List.countIn u _a + (List.countIn v _a + List.countIn v _a) + List.countIn x _a +
            (List.countIn y _a + List.countIn y _a) +
          List.countIn z _a =
        List.countIn u _a + List.countIn v _a + List.countIn x _a + List.countIn y _a +
            List.countIn z _a +
          (List.countIn v _a + List.countIn y _a) :=
      by ring
    have zero_in_v : List.countIn v _a = 0 :=
      by
      rw [List.mem_append] at no_a
      push_neg at no_a
      exact List.countIn_zero_of_notin no_a.left
    have zero_in_y : List.countIn y _a = 0 :=
      by
      rw [List.mem_append] at no_a
      push_neg at no_a
      exact List.countIn_zero_of_notin no_a.right
    rw [rearrange]
    repeat' rw [← List.countIn_append]
    rw [counted_a]
    rw [List.countIn_append]
    rw [zero_in_v]
    rw [zero_in_y]
  cases' extra_not_a with extra_b extra_c
  · have count_b : List.countIn (u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z) _b > n + 1 :=
      by
      unfold List.nTimes
      simp [-List.append_assoc]
      repeat' rw [List.countIn_append]
      have big_equality :
        List.countIn u _b + (List.countIn v _b + List.countIn v _b) + List.countIn x _b +
              (List.countIn y _b + List.countIn y _b) +
            List.countIn z _b =
          List.countIn u _b + List.countIn v _b + List.countIn x _b + List.countIn y _b +
              List.countIn z _b +
            (List.countIn v _b + List.countIn y _b) :=
        by ring
      rw [big_equality]
      repeat' rw [← List.countIn_append]
      rw [counted_b]
      have at_least_one_b : List.countIn (v ++ y) _b > 0 := List.countIn_pos_of_in extra_b
      linarith
    rw [count_a] at hab
    rw [hab] at count_b
    exact LT.lt.false count_b
  · have count_c : List.countIn (u ++ v ^^ 2 ++ x ++ y ^^ 2 ++ z) _c > n + 1 :=
      by
      unfold List.nTimes
      simp [-List.append_assoc]
      repeat' rw [List.countIn_append]
      have big_equality :
        List.countIn u _c + (List.countIn v _c + List.countIn v _c) + List.countIn x _c +
              (List.countIn y _c + List.countIn y _c) +
            List.countIn z _c =
          List.countIn u _c + List.countIn v _c + List.countIn x _c + List.countIn y _c +
              List.countIn z _c +
            (List.countIn v _c + List.countIn y _c) :=
        by ring
      rw [big_equality]
      repeat' rw [← List.countIn_append]
      rw [counted_c]
      have at_least_one_c : List.countIn (v ++ y) _c > 0 := List.countIn_pos_of_in extra_c
      linarith
    rw [count_a] at hac
    rw [hac] at count_c
    exact LT.lt.false count_c

private lemma notCF_lang_eq_eq : ¬langEqEq.IsCF :=
  by
  intro h
  have pum := CF_pumping h
  cases' pum with n pump
  specialize
    pump (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_)
  specialize
    pump (by use n + 1)
      (by
        rw [List.length_append]
        rw [List.length_replicate]
        calc
          (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_).length + (n + 1) ≥ n + 1 :=
            le_add_self
          _ ≥ n := Nat.le_succ n)
  rcases pump with ⟨u, v, x, y, z, concatenating, nonempty, vxy_short, pumping⟩
  specialize pumping 2
  have not_all_letters : a_ ∉ v ++ y ∨ b_ ∉ v ++ y ∨ c_ ∉ v ++ y :=
    by
    by_contra contr
    push_neg at contr
    rcases contr with ⟨hva, -, hvc⟩
    have vxy_long : (v ++ x ++ y).length > n :=
      by
      by_contra contr
      push_neg at contr
      have total_length_exactly : u.length + (v ++ x ++ y).length + z.length = 3 * n + 3 :=
        by
        have total_length := congr_arg List.length concatenating
        repeat' rw [List.length_append] at total_length
        repeat' rw [List.length_replicate] at total_length
        ring_nf at total_length
        rw [← add_assoc x.length] at total_length
        rw [← add_assoc v.length] at total_length
        rw [← add_assoc v.length] at total_length
        rw [← add_assoc u.length] at total_length
        rw [← List.length_append_append] at total_length
        exact total_length.symm
      have u_short : u.length ≤ n :=
        by
        -- in contradiction with `hva: a_ ∈ v ++ y`
        by_contra u_too_much
        push_neg at u_too_much
        have relaxed_a : a_ ∈ v ++ x ++ y ++ z :=
          by
          cases' List.mem_append.1 hva with a_in_v a_in_y
          · rw [List.append_assoc]
            rw [List.append_assoc]
            rw [List.mem_append]
            left
            exact a_in_v
          · have a_in_yz : a_ ∈ y ++ z := by
              rw [List.mem_append]
              left
              exact a_in_y
            rw [List.append_assoc]
            rw [List.mem_append]
            right
            exact a_in_yz
        repeat' rw [List.append_assoc] at concatenating
        rcases List.nthLe_of_mem relaxed_a with ⟨nₐ, hnₐ, h_nthₐ⟩
        obtain ⟨h_nth_a_pr, h_nth_a⟩ :
          ∃ proofoo, (v ++ x ++ y ++ z).nthLe (nₐ + u.length - u.length) proofoo = a_ :=
          by
          rw [Nat.add_sub_cancel nₐ u.length]
          use hnₐ
          exact h_nthₐ
        have lt_len : nₐ + u.length < (u ++ (v ++ x ++ y ++ z)).length :=
          by
          rw [List.length_append]
          linarith
        rw [← List.nthLe_append_right le_add_self lt_len] at h_nth_a
        have orig_nth_le_eq_a :
          ∃ proofoo,
            (List.replicate (n + 1) a_ ++
                    (List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_)).nthLe
                (nₐ + u.length) proofoo =
              a_ :=
          by
          have rebracket : u ++ (v ++ (x ++ (y ++ z))) = u ++ (v ++ x ++ y ++ z) := by
            simp only [List.append_assoc]
          rw [concatenating]
          rw [rebracket]
          use lt_len
          exact h_nth_a
        cases' orig_nth_le_eq_a with rrr_nth_le_eq_a_pr rrr_nth_le_eq_a
        rw [@List.nthLe_append_right (Fin 3) (List.replicate (n + 1) a_)
            (List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_) (nₐ + u.length)
            (by
              rw [List.length_replicate]
              calc
                n + 1 ≤ u.length := u_too_much
                _ ≤ nₐ + u.length := le_add_self)
            (by
              rw [concatenating]
              rw [← List.append_assoc x]
              rw [← List.append_assoc v]
              rw [← List.append_assoc v]
              exact lt_len)] at
          rrr_nth_le_eq_a
        have a_in_rb_rc : a_ ∈ List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_ :=
          by
          rw [← rrr_nth_le_eq_a]
          apply List.nthLe_mem
        rw [List.mem_append] at a_in_rb_rc
        cases a_in_rb_rc
        · rw [List.mem_replicate] at a_in_rb_rc
          exact neq_ab a_in_rb_rc.right
        · rw [List.mem_replicate] at a_in_rb_rc
          exact neq_ac a_in_rb_rc.right
      have z_short : z.length ≤ n :=
        by
        have our_bound : 2 * n + 2 < (u ++ v ++ x ++ y).length :=
          by
          have relaxed_c : c_ ∈ u ++ v ++ x ++ y :=
            by
            cases' List.mem_append.1 hvc with c_in_v c_in_y
            · have c_in_uv : c_ ∈ u ++ v := by
                rw [List.mem_append]
                right
                exact c_in_v
              rw [List.append_assoc]
              rw [List.mem_append]
              left
              exact c_in_uv
            · rw [List.mem_append]
              right
              exact c_in_y
          repeat' rw [List.append_assoc] at concatenating
          rcases List.nthLe_of_mem relaxed_c with ⟨m, hm, mth_is_c⟩
          have m_big : m ≥ 2 * n + 2 :=
            by
            have orig_mth_is_c :
              ∃ proofoo,
                (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_ ++
                        List.replicate (n + 1) c_).nthLe
                    m proofoo =
                  c_ :=
              by
              repeat' rw [← List.append_assoc] at concatenating
              rw [concatenating]
              have m_small : m < (u ++ v ++ x ++ y ++ z).length :=
                by
                rw [List.length_append]
                linarith
              rw [← @List.nthLe_append _ _ z m m_small] at mth_is_c
              use m_small
              exact mth_is_c
            cases' orig_mth_is_c with trash mth_is_c
            by_contra mle
            push_neg at mle
            have m_lt_len : m < (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_).length :=
              by
              rw [List.length_append]
              rw [List.length_replicate]
              rw [List.length_replicate]
              ring_nf
              exact mle
            rw [List.nthLe_append _ m_lt_len] at mth_is_c
            · have c_in_ra_rb : c_ ∈ List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_ :=
                by
                rw [← mth_is_c]
                apply List.nthLe_mem
              rw [List.mem_append] at c_in_ra_rb
              cases' c_in_ra_rb with c_in_ra c_in_rb
              · rw [List.mem_replicate] at c_in_ra
                exact neq_ca c_in_ra.right
              · rw [List.mem_replicate] at c_in_rb
                exact neq_cb c_in_rb.right
          linarith
        rw [← List.length_append] at total_length_exactly
        rw [← List.append_assoc] at total_length_exactly
        rw [← List.append_assoc] at total_length_exactly
        linarith
      linarith
    exact not_le_of_gt vxy_long vxy_short
  have counts_ab : ∀ w ∈ lang_eq_eq, List.countIn w a_ = List.countIn w b_ :=
    by
    intro w w_in
    cases' w_in with w_n w_prop
    rw [w_prop]
    repeat' rw [List.countIn_append]
    rw [List.countIn_replicate_neq neq_ab]
    rw [List.countIn_replicate_neq neq_ba]
    rw [List.countIn_replicate_neq neq_ca]
    rw [List.countIn_replicate_neq neq_cb]
    rw [List.countIn_replicate_eq a_]
    rw [List.countIn_replicate_eq b_]
    repeat' rw [add_zero]
    rw [zero_add]
  have counts_ac : ∀ w ∈ lang_eq_eq, List.countIn w a_ = List.countIn w c_ :=
    by
    intro w w_in
    cases' w_in with w_n w_prop
    rw [w_prop]
    repeat' rw [List.countIn_append]
    rw [List.countIn_replicate_neq neq_ac]
    rw [List.countIn_replicate_neq neq_ca]
    rw [List.countIn_replicate_neq neq_ba]
    rw [List.countIn_replicate_neq neq_bc]
    rw [List.countIn_replicate_eq a_]
    rw [List.countIn_replicate_eq c_]
    repeat' rw [add_zero]
    rw [zero_add]
  have counts_bc : ∀ w ∈ lang_eq_eq, List.countIn w b_ = List.countIn w c_ :=
    by
    intro w w_in
    rw [← counts_ab w w_in]
    exact counts_ac w w_in
  have counts_ba : ∀ w ∈ lang_eq_eq, List.countIn w b_ = List.countIn w a_ :=
    by
    intro w w_in
    symm
    exact counts_ab w w_in
  have counts_ca : ∀ w ∈ lang_eq_eq, List.countIn w c_ = List.countIn w a_ :=
    by
    intro w w_in
    symm
    exact counts_ac w w_in
  have counts_cb : ∀ w ∈ lang_eq_eq, List.countIn w c_ = List.countIn w b_ :=
    by
    intro w w_in
    symm
    exact counts_bc w w_in
  have counted_letter :
    ∀ s,
      List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) s =
        List.countIn (List.replicate (n + 1) a_) s + List.countIn (List.replicate (n + 1) b_) s +
            List.countIn (List.replicate (n + 1) c_) s +
          List.countIn (v ++ y) s :=
    by
    intro s
    rw [← concatenating]
    repeat' rw [List.countIn_append]
  have counted_a :
    List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) a_ = n + 1 + List.countIn (v ++ y) a_ :=
    by
    rw [counted_letter]
    rw [List.countIn_replicate_eq a_]
    rw [List.countIn_replicate_neq neq_ba]
    rw [List.countIn_replicate_neq neq_ca]
  have counted_b :
    List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) b_ = n + 1 + List.countIn (v ++ y) b_ :=
    by
    rw [counted_letter]
    rw [List.countIn_replicate_eq b_]
    rw [List.countIn_replicate_neq neq_cb]
    rw [List.countIn_replicate_neq neq_ab]
    rw [zero_add]
  have counted_c :
    List.countIn (u ++ v ++ x ++ y ++ z ++ (v ++ y)) c_ = n + 1 + List.countIn (v ++ y) c_ :=
    by
    rw [counted_letter]
    rw [List.countIn_replicate_eq c_]
    rw [List.countIn_replicate_neq neq_ac]
    rw [List.countIn_replicate_neq neq_bc]
    rw [zero_add]
  have elimin_abc : ∀ s : Fin 3, s ≠ a_ → s ≠ b_ → s ≠ c_ → False :=
    by
    intro s hsa hsb hsc
    fin_cases s
    · rw [a_] at hsa
      exact hsa rfl
    · rw [b_] at hsb
      exact hsb rfl
    · rw [c_] at hsc
      exact hsc rfl
  cases' not_all_letters with no_a foo
  ·
    exact
      false_of_uvvxyyz elimin_abc no_a Nonempty counts_ab counts_ac counted_a counted_b counted_c
        pumping
  cases' foo with no_b no_c
  · have elimin_bca : ∀ s : Fin 3, s ≠ b_ → s ≠ c_ → s ≠ a_ → False :=
      by
      intro s hsb hsc hsa
      exact elimin_abc s hsa hsb hsc
    exact
      false_of_uvvxyyz elimin_bca no_b Nonempty counts_bc counts_ba counted_b counted_c counted_a
        pumping
  · have elimin_cab : ∀ s : Fin 3, s ≠ c_ → s ≠ a_ → s ≠ b_ → False :=
      by
      intro s hsc hsa hsb
      exact elimin_abc s hsa hsb hsc
    exact
      false_of_uvvxyyz elimin_cab no_c Nonempty counts_ca counts_cb counted_c counted_a counted_b
        pumping

end NotCF

section YesCF

private def lang_aux_ab : Language (Fin 3) := fun w =>
  ∃ n : ℕ, w = List.replicate n a_ ++ List.replicate n b_

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic split_ile -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic split_ile -/
private lemma CF_lang_aux_ab : langAuxAb.IsCF :=
  by
  let S_ : Fin 1 := 0
  let S : Symbol (Fin 3) (Fin 1) := Symbol.nonterminal S_
  let g := CFG.mk (Fin 1) S_ [(S_, [a, S, b]), (S_, ([] : List (Symbol (Fin 3) (Fin 1))))]
  use g
  apply Set.eq_of_subset_of_subset
  · intro w ass
    change CFDerives g [S] (List.map Symbol.terminal w) at ass
    have indu :
      ∀ v : List (Symbol (Fin 3) (Fin 1)),
        CFDerives g [S] v →
          ∃ n : ℕ,
            v = List.replicate n a ++ List.replicate n b ∨
              v = List.replicate n a ++ [S] ++ List.replicate n b :=
      by
      intro v hyp
      induction' hyp with u u' trash orig hyp_ih
      · use 0
        right
        rfl
      rcases orig with ⟨r, rin, p, q, bef, aft⟩
      cases' hyp_ih with k ih
      cases ih
      · exfalso
        rw [ih] at bef
        have yes_in : Symbol.nonterminal r.fst ∈ p ++ [Symbol.nonterminal r.fst] ++ q :=
          by
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_cons_self
        have not_in : Symbol.nonterminal r.fst ∉ List.replicate k a ++ List.replicate k b :=
          by
          rw [List.mem_append_eq]
          push_neg
          constructor <;>
            · rw [List.mem_replicate]
              push_neg
              intro trash
              apply Symbol.noConfusion
        rw [bef] at not_in
        exact not_in yes_in
      have both_rule_rewrite_S : Symbol.nonterminal r.fst = S :=
        by
        cases rin
        · rw [rin]
        cases rin
        · rw [rin]
        cases rin
      rw [bef] at ih
      rw [both_rule_rewrite_S] at ih
      have p_len : p.length = k := by
        by_contra contra
        have kth_eq := congr_fun (congr_arg List.get? ih) p.length
        have plengthth_is_S : (p ++ [S] ++ q).get? p.length = some S :=
          by
          rw [List.append_assoc]
          rw [List.get?_append_right (le_of_eq rfl)]
          · rw [Nat.sub_self]
            rfl
        rw [plengthth_is_S] at kth_eq
        cases lt_or_gt_of_ne contra
        · have plengthth_is_a :
            (List.replicate k a ++ [S] ++ List.replicate k b).get? p.length = some a :=
            by
            rw [List.append_assoc]
            have plength_small : p.length < (List.replicate k a).length :=
              by
              rw [List.length_replicate]
              exact h
            rw [List.get?_append plength_small]
            rw [List.nthLe_get? plength_small]
            apply congr_arg
            exact List.nthLe_replicate a plength_small
          rw [plengthth_is_a] at kth_eq
          have S_neq_a : S ≠ a := by apply Symbol.noConfusion
          rw [Option.some_inj] at kth_eq
          exact S_neq_a kth_eq
        · have plengthth_is_b :
            (List.replicate k a ++ [S] ++ List.replicate k b).get? p.length = some b :=
            by
            have plength_big : (List.replicate k a ++ [S]).length ≤ p.length :=
              by
              rw [List.length_append]
              rw [List.length_replicate]
              exact nat.succ_le_iff.mpr h
            rw [List.get?_append_right plength_big]
            have len_within_list :
              p.length - (List.replicate k a ++ [S]).length < (List.replicate k b).length :=
              by
              have ihlen := congr_arg List.length ih
              simp only [List.length_replicate, List.length_append, List.length_singleton] at *
              have ihlen' : p.length + 1 ≤ k + 1 + k := Nat.le.intro ihlen
              have ihlen'' : p.length < k + 1 + k := nat.succ_le_iff.mp ihlen'
              rw [← tsub_lt_iff_left plength_big] at ihlen''
              exact ihlen''
            rw [List.nthLe_get? len_within_list]
            apply congr_arg
            exact List.nthLe_replicate b len_within_list
          rw [plengthth_is_b] at kth_eq
          have S_neq_b : S ≠ b := by apply Symbol.noConfusion
          rw [Option.some_inj] at kth_eq
          exact S_neq_b kth_eq
      have ihl_len : (p ++ [Symbol.nonterminal S_]).length = k + 1 :=
        by
        rw [List.length_append]
        rw [p_len]
        rfl
      have ihr_len : (List.replicate k a ++ [S]).length = k + 1 :=
        by
        rw [List.length_append]
        rw [List.length_replicate]
        rfl
      have qb : q = List.replicate k b :=
        by
        apply List.append_inj_right ih
        rw [ihl_len]
        rw [ihr_len]
      have ih_reduced : p ++ [Symbol.nonterminal S_] = List.replicate k a ++ [S] :=
        by
        rw [qb] at ih
        rw [List.append_left_inj] at ih
        exact ih
      have pa : p = List.replicate k a :=
        by
        rw [List.append_left_inj] at ih_reduced
        exact ih_reduced
      cases rin
      · use k + 1
        right
        rw [aft]
        rw [rin]
        convert_to
          p ++ (S_, [a, S, b]).snd ++ q =
            List.replicate k a ++ [a] ++ [S] ++ [b] ++ List.replicate k b
        · rw [List.replicate_add]
          rw [add_comm]
          rw [List.replicate_add]
          simp only [List.replicate, List.append_assoc]
        rw [pa, qb]
        simp only [List.append_assoc, List.cons_append, List.singleton_append]
      cases rin
      · use k
        left
        rw [aft]
        rw [rin]
        rw [List.append_nil]
        rw [pa, qb]
      exfalso
      exact rin
    cases' indu (List.map Symbol.terminal w) ass with n instantiated
    clear indu
    cases instantiated
    · use n
      have foo :=
        congr_arg
          (List.filterMap fun z : Symbol (Fin 3) (Fin 1) =>
            match z with
            | Symbol.terminal t => some t
            | Symbol.nonterminal _ => none)
          instantiated
      rw [List.filterMap_append] at foo
      rw [List.filterMap_map] at foo
      rw [List.filterMap_some] at foo
      rw [foo, a, b]
      clear foo
      apply congr_arg₂ <;>
        · clear instantiated
          induction' n with n ih
          · rfl
          rw [List.replicate_succ]
          rw [List.replicate_succ]
          rw [List.filterMap_cons]
          simp only [eq_self_iff_true, true_and_iff, ih]
    exfalso
    have yes_in : S ∈ List.replicate n a ++ [S] ++ List.replicate n b :=
      by
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_cons_self
    have not_in : S ∉ List.map Symbol.terminal w :=
      by
      intro hyp
      have S_isnt_terminal : ¬∃ x, S = Symbol.terminal x := by tauto
      rw [List.mem_map] at hyp
      cases' hyp with y hypo
      push_neg at S_isnt_terminal
      exact S_isnt_terminal y hypo.right.symm
    rw [instantiated] at not_in
    exact not_in yes_in
  · intro w ass
    cases' ass with n hw
    change CFDerives g [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)
    rw [hw, List.map_append, List.map_replicate, List.map_replicate, ← a, ← b]
    clear hw
    induction' n with n ih
    · convert_to CFDerives g [Symbol.nonterminal g.initial] []
      apply CF_deri_of_tran
      use (S_, ([] : List (Symbol (Fin 3) (Fin 1))))
      run_tac
        split_ile
      use [], []
      constructor <;> rfl
    convert_to
      CFDerives g [Symbol.nonterminal g.initial]
        (List.map Symbol.terminal ([a_] ++ (List.replicate n a_ ++ List.replicate n b_) ++ [b_]))
    · convert_to
        List.replicate (1 + n) a ++ List.replicate (n + 1) b =
          List.map Symbol.terminal ([a_] ++ (List.replicate n a_ ++ List.replicate n b_) ++ [b_])
      · rw [add_comm]
      rw [List.map_append_append, List.map_singleton, List.map_singleton, List.replicate_add,
        List.replicate_add, a, b]
      simp only [List.replicate, List.append_assoc, List.map_append, List.map_replicate]
    apply CF_deri_of_tran_deri
    · use (S_, [a, S, b])
      run_tac
        split_ile
      use [], []
      constructor <;> rfl
    rw [List.map_append_append]
    change
      CFDerives g ([a] ++ [S] ++ [b])
        ([a] ++ List.map Symbol.terminal (List.replicate n a_ ++ List.replicate n b_) ++ [b])
    apply CF_append_deri_and_postfix
    convert ih
    rw [List.map_append, List.map_replicate, List.map_replicate, a, b]

private def lang_aux_c : Language (Fin 3) := fun w => ∃ n : ℕ, w = List.replicate n c_

private lemma CF_lang_aux_c : langAuxC.IsCF :=
  by
  use cfgSymbolStar c_
  unfold lang_aux_c
  apply language_of_cfgSymbolStar

private lemma CF_lang_eq_any : langEqAny.IsCF :=
  by
  have concatenated : lang_eq_any = lang_aux_ab * lang_aux_c :=
    by
    ext1 w
    constructor
    · rintro ⟨n, m, hnm⟩
      fconstructor
      use List.replicate n a_ ++ List.replicate n b_
      use List.replicate m c_
      constructor
      · use n
      constructor
      · use m
      exact hnm.symm
    · rintro ⟨u, v, ⟨n, u_eq⟩, ⟨m, v_eq⟩, eq_w⟩
      use n
      use m
      rw [← eq_w, ← u_eq, ← v_eq]
  rw [concatenated]
  apply CF_of_CF_c_CF
  exact And.intro CF_lang_aux_ab CF_lang_aux_c

private def lang_aux_a : Language (Fin 3) := fun w => ∃ n : ℕ, w = List.replicate n a_

private lemma CF_lang_aux_a : langAuxA.IsCF :=
  by
  use cfgSymbolStar a_
  unfold lang_aux_a
  apply language_of_cfgSymbolStar

private def lang_aux_bc : Language (Fin 3) := fun w =>
  ∃ n : ℕ, w = List.replicate n b_ ++ List.replicate n c_

private def permut : Equiv.Perm (Fin 3) :=
  Equiv.mk (fun x => ite (x = 2) 0 (x + 1)) (fun x => ite (x = 0) 2 (x - 1))
    (by
      intro x
      fin_cases x <;> rfl)
    (by
      intro x
      fin_cases x <;> rfl)

private lemma CF_lang_aux_bc : langAuxBc.IsCF :=
  by
  have permuted : lang_aux_bc = permuteLang lang_aux_ab permut :=
    by
    have compos : permut.to_fun ∘ permut.inv_fun = id := by simp
    ext1 w
    constructor <;>
      · intro h
        cases' h with n hn
        use n
        try rw [hn]
        try
          have other_case := congr_arg (List.map permut.to_fun) hn
          rw [List.map_map] at other_case
          rw [compos] at other_case
          rw [List.map_id] at other_case
          rw [other_case]
        rw [List.map_append]
        rw [List.map_replicate]
        rw [List.map_replicate]
        apply congr_arg₂ <;> rfl
  rw [permuted]
  exact CF_of_permute_CF permut lang_aux_ab CF_lang_aux_ab

private lemma CF_lang_any_eq : langAnyEq.IsCF :=
  by
  have concatenated : lang_any_eq = lang_aux_a * lang_aux_bc :=
    by
    ext1 w
    constructor
    · rintro ⟨n, m, hnm⟩
      fconstructor
      use List.replicate n a_
      use List.replicate m b_ ++ List.replicate m c_
      constructor
      · use n
      constructor
      · use m
      rw [← List.append_assoc]
      exact hnm.symm
    · rintro ⟨u, v, ⟨n, hu⟩, ⟨m, hv⟩, h⟩
      use n
      use m
      rw [List.append_assoc, ← h, ← hu, ← hv]
  rw [concatenated]
  apply CF_of_CF_c_CF
  exact And.intro CF_lang_aux_a CF_lang_aux_bc

end YesCF

section IntersectionInclusions

private lemma intersection_of_lang_eq_eq {w : List (Fin 3)} :
    w ∈ langEqEq → w ∈ langEqAny ⊓ langAnyEq :=
  by
  intro h
  cases' h with n hyp
  constructor <;>
    · use n
      use n
      exact hyp

private lemma doubled_le_singled (n₁ m₁ n₂ m₂ : ℕ) (n₁pos : n₁ > 0) (a_ b_ c_ : Fin 3)
    (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      List.replicate n₁ a_ ++ List.replicate n₁ b_ ++ List.replicate m₁ c_ =
        List.replicate n₂ a_ ++ List.replicate m₂ b_ ++ List.replicate m₂ c_) :
    n₁ ≤ n₂ := by
  by_contra contr
  push_neg at contr
  have n₁_le_len₁ :
    n₁ - 1 < (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).length :=
    by
    rw [← List.append_assoc]
    rw [List.length_append]
    rw [List.length_append]
    rw [List.length_replicate]
    rw [add_assoc]
    apply Nat.lt_add_right
    exact Nat.sub_lt n₁pos (Nat.succ_pos 0)
  have n₁_le_len₂ :
    n₁ - 1 < (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).length :=
    by
    rw [← List.append_assoc]
    have equ_len := congr_arg List.length equ
    rw [← equ_len]
    rw [List.append_assoc]
    exact n₁_le_len₁
  have n₁th :
    (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).nthLe (n₁ - 1)
        n₁_le_len₁ =
      (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).nthLe (n₁ - 1)
        n₁_le_len₂ :=
    by
    rw [List.append_assoc] at equ
    rw [List.append_assoc] at equ
    exact List.nthLe_of_eq equ n₁_le_len₁
  have n₁th₁ :
    (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).nthLe (n₁ - 1)
        n₁_le_len₁ =
      a_ :=
    by
    have foo : n₁ - 1 < (List.replicate n₁ a_).length :=
      by
      rw [List.length_replicate]
      exact Nat.sub_lt n₁pos (Nat.succ_pos 0)
    rw [List.nthLe_append n₁_le_len₁ foo]
    exact List.nthLe_replicate a_ foo
  have n₁th₂ :
    (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).nthLe (n₁ - 1)
        n₁_le_len₂ ≠
      a_ :=
    by
    have foo : (List.replicate n₂ a_).length ≤ n₁ - 1 :=
      by
      rw [List.length_replicate]
      exact Nat.le_pred_of_lt contr
    rw [List.nthLe_append_right foo n₁_le_len₂]
    by_contra
    have a_in_bc : a_ ∈ List.replicate m₂ b_ ++ List.replicate m₂ c_ :=
      by
      rw [← h]
      apply List.nthLe_mem
    rw [List.mem_append] at a_in_bc
    cases a_in_bc
    · rw [List.mem_replicate] at a_in_bc
      exact a_neq_b a_in_bc.right
    · rw [List.mem_replicate] at a_in_bc
      exact a_neq_c a_in_bc.right
  rw [n₁th₁] at n₁th
  rw [← n₁th] at n₁th₂
  exact false_of_ne n₁th₂

private lemma doubled_ge_singled (n₁ m₁ n₂ m₂ : ℕ) (n₂pos : n₂ > 0) (a_ b_ c_ : Fin 3)
    (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      List.replicate n₁ a_ ++ List.replicate n₁ b_ ++ List.replicate m₁ c_ =
        List.replicate n₂ a_ ++ List.replicate m₂ b_ ++ List.replicate m₂ c_) :
    n₁ ≥ n₂ := by
  by_contra contr
  push_neg at contr
  have n₂_le_len₂ :
    n₂ - 1 < (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).length :=
    by
    rw [← List.append_assoc]
    rw [List.length_append]
    rw [List.length_append]
    rw [List.length_replicate]
    rw [add_assoc]
    apply Nat.lt_add_right
    exact Nat.sub_lt n₂pos (Nat.succ_pos 0)
  have n₂_le_len₁ :
    n₂ - 1 < (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).length :=
    by
    rw [← List.append_assoc]
    have equ_len := congr_arg List.length equ
    rw [equ_len]
    rw [List.append_assoc]
    exact n₂_le_len₂
  have n₂th :
    (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).nthLe (n₂ - 1)
        n₂_le_len₁ =
      (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).nthLe (n₂ - 1)
        n₂_le_len₂ :=
    by
    rw [List.append_assoc] at equ
    rw [List.append_assoc] at equ
    exact List.nthLe_of_eq equ n₂_le_len₁
  have n₂th₂ :
    (List.replicate n₂ a_ ++ (List.replicate m₂ b_ ++ List.replicate m₂ c_)).nthLe (n₂ - 1)
        n₂_le_len₂ =
      a_ :=
    by
    have foo : n₂ - 1 < (List.replicate n₂ a_).length :=
      by
      rw [List.length_replicate]
      exact Nat.sub_lt n₂pos (Nat.succ_pos 0)
    rw [List.nthLe_append n₂_le_len₂ foo]
    exact List.nthLe_replicate a_ foo
  have n₂th₁ :
    (List.replicate n₁ a_ ++ (List.replicate n₁ b_ ++ List.replicate m₁ c_)).nthLe (n₂ - 1)
        n₂_le_len₁ ≠
      a_ :=
    by
    have foo : (List.replicate n₁ a_).length ≤ n₂ - 1 :=
      by
      rw [List.length_replicate]
      exact Nat.le_pred_of_lt contr
    rw [List.nthLe_append_right foo n₂_le_len₁]
    by_contra
    have a_in_bc : a_ ∈ List.replicate n₁ b_ ++ List.replicate m₁ c_ :=
      by
      rw [← h]
      apply List.nthLe_mem
    rw [List.mem_append] at a_in_bc
    cases a_in_bc
    · rw [List.mem_replicate] at a_in_bc
      exact a_neq_b a_in_bc.right
    · rw [List.mem_replicate] at a_in_bc
      exact a_neq_c a_in_bc.right
  rw [n₂th₂] at n₂th
  rw [n₂th] at n₂th₁
  exact false_of_ne n₂th₁

private lemma lang_eq_eq_of_intersection {w : List (Fin 3)} :
    w ∈ langEqAny ⊓ langAnyEq → w ∈ langEqEq :=
  by
  rintro ⟨⟨n₁, m₁, w_eq₁⟩, ⟨n₂, m₂, w_eq₂⟩⟩
  have equ := Eq.trans w_eq₁.symm w_eq₂
  by_cases hn₁ : n₁ = 0
  · have hn₂ : n₂ = 0 := by
      by_contra
      have pos := Nat.pos_of_ne_zero h
      clear h
      have a_in_equ := congr_arg (fun lis => a_ ∈ lis) equ
      clear equ
      rw [hn₁] at a_in_equ
      have a_yes : a_ ∈ List.replicate n₂ a_ :=
        by
        rw [List.mem_replicate]
        exact And.intro (ne_of_lt Pos).symm rfl
      simp [a_yes] at a_in_equ
      rw [List.mem_replicate] at a_in_equ
      exact neq_ac a_in_equ.right
    have hm₂ : m₂ = 0 := by
      by_contra
      have pos := Nat.pos_of_ne_zero h
      clear h
      have b_in_equ := congr_arg (fun lis => b_ ∈ lis) equ
      clear equ
      rw [hn₁] at b_in_equ
      have b_yes : b_ ∈ List.replicate m₂ b_ :=
        by
        rw [List.mem_replicate]
        exact And.intro (ne_of_lt Pos).symm rfl
      simp [b_yes] at b_in_equ
      rw [List.mem_replicate] at b_in_equ
      exact neq_bc b_in_equ.right
    use 0
    rw [hn₂] at w_eq₂
    rw [hm₂] at w_eq₂
    exact w_eq₂
  have n₁pos : n₁ > 0 := pos_iff_ne_zero.mpr hn₁
  have n₂pos : n₂ > 0 := by
    by_contra
    have n₂zero : n₂ = 0 := by
      push_neg at h
      rw [le_zero_iff] at h
      exact h
    clear h
    rw [n₂zero] at equ
    simp only [List.replicate_zero, List.nil_append] at equ
    have a_in_equ := congr_arg (fun lis => a_ ∈ lis) equ
    clear equ
    simp only [List.mem_append, eq_iff_iff, List.mem_replicate, or_assoc'] at a_in_equ
    have rs_false : (m₂ ≠ 0 ∧ a_ = b_ ∨ m₂ ≠ 0 ∧ a_ = c_) = False :=
      by
      apply eq_false
      push_neg
      constructor
      · intro trash
        exact neq_ab
      · intro trash
        exact neq_ac
    rw [← rs_false]
    rw [← a_in_equ]
    left
    constructor
    · exact hn₁
    · rfl
  have m₂pos : m₂ > 0 := by
    by_contra
    have m₂zero : m₂ = 0 := by
      push_neg at h
      rw [le_zero_iff] at h
      exact h
    clear h
    rw [m₂zero] at equ
    simp only [List.replicate_zero, List.append_nil] at equ
    have b_in_equ := congr_arg (fun lis => b_ ∈ lis) equ
    clear equ
    simp only [List.mem_append, eq_iff_iff, List.mem_replicate] at b_in_equ
    have := neq_ba
    tauto
  have m₁pos : m₁ > 0 := by
    by_contra
    have m₁zero : m₁ = 0 := by
      push_neg at h
      rw [le_zero_iff] at h
      exact h
    clear h
    rw [m₁zero] at equ
    simp only [List.replicate_zero, List.append_nil] at equ
    have c_in_equ := congr_arg (fun lis => c_ ∈ lis) equ
    clear equ
    simp only [List.mem_append, eq_iff_iff, List.mem_replicate, or_assoc'] at c_in_equ
    have ls_false : (n₁ ≠ 0 ∧ c_ = a_ ∨ n₁ ≠ 0 ∧ c_ = b_) = False :=
      by
      apply eq_false
      push_neg
      constructor
      · intro trash
        exact neq_ca
      · intro trash
        exact neq_cb
    rw [ls_false] at c_in_equ
    rw [c_in_equ]
    right
    right
    constructor
    · exact ne_of_gt m₂pos
    · rfl
  have n_ge : n₁ ≥ n₂ := doubled_ge_singled n₁ m₁ n₂ m₂ n₂pos a_ b_ c_ neq_ab neq_ac equ
  have n_le : n₁ ≤ n₂ := doubled_le_singled n₁ m₁ n₂ m₂ n₁pos a_ b_ c_ neq_ab neq_ac equ
  have m_ge : m₁ ≥ m₂ := by
    have rev := congr_arg List.reverse equ
    clear equ
    repeat' rw [List.reverse_append] at rev
    repeat' rw [List.reverse_replicate] at rev
    rw [← List.append_assoc] at rev
    rw [← List.append_assoc] at rev
    exact doubled_le_singled m₂ n₂ m₁ n₁ m₂pos c_ b_ a_ neq_cb neq_ca rev.symm
  have m_le : m₁ ≤ m₂ := by
    have rev := congr_arg List.reverse equ
    clear equ
    repeat' rw [List.reverse_append] at rev
    repeat' rw [List.reverse_replicate] at rev
    rw [← List.append_assoc] at rev
    rw [← List.append_assoc] at rev
    exact doubled_ge_singled m₂ n₂ m₁ n₁ m₁pos c_ b_ a_ neq_cb neq_ca rev.symm
  have eqn : n₁ = n₂ := le_antisymm n_le n_ge
  have eqm : m₁ = m₂ := le_antisymm m_le m_ge
  have sum_lengs : n₁ + n₁ + m₁ = n₂ + m₂ + m₂ :=
    by
    have lengs := congr_arg List.length equ
    repeat' rw [List.length_append] at lengs
    repeat' rw [List.length_replicate] at lengs
    exact lengs
  have eq₂ : n₂ = m₂ := by
    rw [eqn] at sum_lengs
    rw [eqm] at sum_lengs
    rw [add_left_inj] at sum_lengs
    rw [add_right_inj] at sum_lengs
    exact sum_lengs
  rw [eq₂] at w_eq₂
  use m₂
  exact w_eq₂

end IntersectionInclusions

/-- The class of context-free languages isn't closed under intersection. -/
lemma nnyCF_of_CF_i_CF :
    ¬∀ T : Type, ∀ L₁ : Language T, ∀ L₂ : Language T, L₁.IsCF ∧ L₂.IsCF → (L₁ ⊓ L₂).IsCF :=
  by
  by_contra contra
  specialize contra (Fin 3) lang_eq_any lang_any_eq ⟨CF_lang_eq_any, CF_lang_any_eq⟩
  apply notCF_lang_eq_eq
  convert contra
  apply Set.eq_of_subset_of_subset
  · apply intersection_of_lang_eq_eq
  · apply lang_eq_eq_of_intersection
-/
