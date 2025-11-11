import Chomsky.Classes.Unrestricted.Basics.Lifting
import Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation


-- new nonterminal type
private def nn (N : Type) : Type :=
  Sum N (Fin 3)

-- new symbol type
private abbrev ns (T N : Type) : Type :=
  Symbol T (nn N)

variable {T : Type}


section specific_symbols

private def Z {N : Type} : ns T N :=
  Symbol.nonterminal ◪0

private def H {N : Type} : ns T N :=
  Symbol.nonterminal ◪1

private def R {N : Type} : ns T N :=
  Symbol.nonterminal ◪2

private def S {g : Grammar T} : ns T g.nt :=
  Symbol.nonterminal ◩g.initial

private lemma Z_neq_H {N : Type} : Z ≠ @H T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have zero_ne_one : (0 : Fin 3) ≠ (1 : Fin 3)
  · decide
  exact zero_ne_one imposs

private lemma Z_neq_R {N : Type} : Z ≠ @R T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have zero_ne_two : (0 : Fin 3) ≠ (2 : Fin 3)
  · decide
  exact zero_ne_two imposs

private lemma H_neq_R {N : Type} : H ≠ @R T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have one_ne_two : (1 : Fin 3) ≠ (2 : Fin 3)
  · decide
  exact one_ne_two imposs

end specific_symbols


section construction

private def wrapSym {N : Type} : Symbol T N → ns T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal ◩n

private def wrapGr {N : Type} (r : Grule T N) : Grule T (nn N) :=
  Grule.mk (r.inputL.map wrapSym) ◩r.inputN (r.inputR.map wrapSym) (r.output.map wrapSym)

private def rulesThatScanTerminals (g : Grammar T) : List (Grule T (nn g.nt)) :=
  (allUsedTerminals g).map (fun t : T => Grule.mk [] ◪2 [Symbol.terminal t] [Symbol.terminal t, R])

-- grammar for iteration of `g.language`
private def Grammar.star (g : Grammar T) : Grammar T :=
  Grammar.mk (nn g.nt) ◪0 (
    Grule.mk [] ◪0 [] [Z, S, H] :: (
    Grule.mk [] ◪0 [] [R, H] :: (
    Grule.mk [] ◪2 [H] [R] :: (
    Grule.mk [] ◪2 [H] [] :: (
    g.rules.map wrapGr ++
    rulesThatScanTerminals g)))))

end construction


section easy_direction

private lemma short_induction {g : Grammar T} {w : List (List T)}
    (hwg : ∀ wᵢ ∈ w.reverse, wᵢ ∈ g.language) :
  g.star.Derives
    [Z]
    (Z :: List.flatten ((w.reverse.map (List.map Symbol.terminal)).map (· ++ [H]))) ∧
  ∀ p ∈ w, ∀ t ∈ p, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten :=
by
  induction' w with v x ih
  · constructor
    · apply gr_deri_self
    · intro p pin
      exfalso
      exact List.not_mem_nil p pin
  have vx_reverse : (v::x).reverse = x.reverse ++ [v]
  · apply List.reverse_cons
  rw [vx_reverse] at hwg
  specialize ih (by
      intro wᵢ in_reversed
      apply hwg
      apply List.mem_append_left
      exact in_reversed)
  specialize hwg v (by
      apply List.mem_append_right
      apply List.mem_singleton_self)
  constructor
  · apply gr_deri_of_tran_deri
    · use g.star.rules.get ⟨0, Nat.zero_lt_succ _⟩
      constructor
      · apply List.get_mem
      use [], []
      constructor <;> rfl
    rw [List.nil_append, List.append_nil]
    show g.star.Derives [Z, S, H] _
    have ih_plus := gr_deri_append ([S, H] : List (Symbol T g.star.nt)) ih.left
    apply gr_deri_of_deri_deri ih_plus
    have hgSv : g.star.Derives [S] (v.map Symbol.terminal)
    · clear * - hwg
      have wrap_eq_lift : @wrapSym T g.nt = liftSymbol Sum.inl
      · ext x
        cases x <;> rfl
      let G : LiftedGrammar T :=
        LiftedGrammar.mk g g.star Sum.inl Sum.getLeft?
          (by
            intro x y hyp
            exact Sum.inl.inj hyp)
          (by
            intro x y hyp
            cases x
            · cases y
              · simp [Sum.getLeft?] at hyp
                left
                exact congr_arg Sum.inl hyp
              · simp [Sum.getLeft?] at hyp
            · cases y
              · simp [Sum.getLeft?] at hyp
              · right
                rfl)
          (by
            intro x
            rfl)
          (by
            intro r rin
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_append_left
            rw [List.mem_map]
            use r
            constructor
            · exact rin
            unfold wrapGr
            unfold liftRule
            unfold liftString
            rw [wrap_eq_lift])
          (by
            rintro r ⟨rin, n, nrn⟩
            cases rin with
            | head => exact Sum.noConfusion nrn
            | tail _ rin =>
              cases rin with
              | head => exact Sum.noConfusion nrn
              | tail _ rin =>
                cases rin with
                | head => exact Sum.noConfusion nrn
                | tail _ rin =>
                  cases rin with
                  | head => exact Sum.noConfusion nrn
                  | tail _ rin =>
                    change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
                    rw [List.mem_append] at rin
                    cases rin with
                    | inl rin =>
                      rw [List.mem_map] at rin
                      exact rin
                    | inr rin =>
                      exfalso
                      unfold rulesThatScanTerminals at rin
                      rw [List.mem_map] at rin
                      rcases rin with ⟨t, tin, r_of_tg⟩
                      rw [← r_of_tg] at nrn
                      exact Sum.noConfusion nrn)
      convert_to G.g.Derives [Symbol.nonterminal ◩g.initial] (liftString G.liftNt (v.map Symbol.terminal))
      · unfold liftString
        rw [List.map_map]
        congr
      exact lift_deri G hwg
    have ass_postf := gr_deri_append [H] hgSv
    simp only [vx_reverse, ←List.cons_append,
      List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact gr_append_deri _ ass_postf
  · intro p pin t tin
    cases pin with
    | head =>
      cases' grammar_generates_only_legit_terminals hwg (Symbol.terminal t)
          (show Symbol.terminal t ∈ v.map Symbol.terminal by rw [List.mem_map]; use t) with rule_exists imposs
      · rcases rule_exists with ⟨r, rin, stirn⟩
        rw [List.mem_flatten]
        use r.output
        constructor
        · rw [List.mem_map]
          use r
        · exact stirn
      · exfalso
        exact Symbol.noConfusion imposs
    | tail b pin => exact ih.right p pin t tin

private lemma terminal_scan_ind {g : Grammar T} {w : List (List T)} (n : ℕ)
    (n_lt_wl : n ≤ w.length)
    (terminals : ∀ v ∈ w, ∀ t ∈ v, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten) :
  g.star.Derives
    (((w.take (w.length - n)).map (List.map Symbol.terminal)).flatten ++ [R] ++
     ((w.drop (w.length - n)).map (fun v => [H] ++ v.map Symbol.terminal)).flatten ++ [H])
    (w.flatten.map Symbol.terminal ++ [R, H]) :=
by
  induction' n with k ih
  · rw [Nat.sub_zero, List.drop_length, List.map_nil, List.flatten, List.append_nil, List.take_length, List.map_flatten, List.append_assoc]
    apply gr_deri_self
  specialize ih (Nat.le_of_succ_le n_lt_wl)
  apply gr_deri_of_deri_deri _ ih
  clear ih
  have wlk_succ : w.length - k = (w.length - k.succ).succ
  · omega
  have lt_wl : w.length - k.succ < w.length
  · omega
  have split_ldw : w.drop (w.length - k.succ) = (w[w.length - k.succ]?).toList ++ w.drop (w.length - k)
  · rw [wlk_succ]
    generalize substit : w.length - k.succ = q
    rw [substit] at lt_wl
    rw [← List.take_append_drop q w]
    rw [List.getElem?_append_right]
    swap; · apply List.length_take_le
    have eq_q : (w.take q).length = q
    · rw [List.length_take]
      exact min_eq_left_of_lt lt_wl
    rw [eq_q]
    rw [Nat.sub_self]
    have drop_q_succ : (w.take q ++ w.drop q).drop q.succ = (w.drop q).drop 1
    · rw [List.drop_drop, List.take_append_drop]
    rw [drop_q_succ, List.drop_left' eq_q, List.drop_drop]
    rw [← List.take_append_drop (1 + q) w]
    have q_lt : q < (w.take (1 + q)).length
    · rw [List.length_take]
      exact lt_min (lt_one_add q) lt_wl
    rw [List.drop_append_of_le_length (le_of_lt q_lt)]
    apply congr_arg₂
    · rw [List.getElem?_append, List.getElem?_drop, add_zero, List.getElem?_take, add_comm, list_drop_take_succ lt_wl]
      simp [*]
    · rw [List.take_append_drop, add_comm]
  apply gr_deri_append
  rw [split_ldw, List.map_append, List.flatten_append, ← List.append_assoc]
  apply gr_deri_append
  rw [wlk_succ, List.take_succ, List.map_append, List.flatten_append, List.append_assoc,
    List.append_assoc]
  apply gr_append_deri
  clear * - terminals lt_wl
  specialize terminals (w.get ⟨w.length - k.succ, lt_wl⟩) (w.get_mem ⟨w.length - k.succ, lt_wl⟩)
  simp
  have hw : 0 < w.length
  · linarith
  simp [hw]
  apply gr_deri_of_tran_deri
  · use g.star.rules[2]'(List.isSome_getElem?.→ rfl), List.getElem_mem (List.isSome_getElem?.→ rfl), [],
        (w[w.length - k.succ]'lt_wl).map Symbol.terminal, rfl
  rw [List.nil_append]
  have scan_segment :
    ∀ m : ℕ,
      m ≤ (w[w.length - k.succ]'lt_wl).length →
        g.star.Derives
          ([R] ++ (w[w.length - k.succ]'lt_wl).map Symbol.terminal)
          (((w[w.length - k.succ]'lt_wl).take m).map Symbol.terminal ++ ([R] ++
           ((w[w.length - k.succ]'lt_wl).drop m).map Symbol.terminal))
  · intro m small
    induction m with
    | zero => apply gr_deri_self
    | succ n ih =>
      apply gr_deri_of_deri_tran (ih (Nat.le_of_succ_le small))
      rw [Nat.succ_le_iff] at small
      use ⟨[], Sum.inr 2,
        [Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small)],
        [Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small), R]⟩
      constructor
      · apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        unfold rulesThatScanTerminals
        rw [List.mem_map]
        use (w[w.length - k.succ]'lt_wl)[n]'small
        constructor
        · unfold allUsedTerminals
          rw [List.mem_filterMap]
          use Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small)
          constructor
          · apply terminals
            exact List.getElem_mem small
          · rfl
        · rfl
      use ((w[w.length - k.succ]'lt_wl).take n).map Symbol.terminal
      use ((w[w.length - k.succ]'lt_wl).drop n.succ).map Symbol.terminal
      constructor
      · simp
        constructor
        · rfl
        · rw [←List.map_drop]
          rw [←(((w[w.length - k.succ]'lt_wl).drop n).map Symbol.terminal).take_append_drop 1]
          rw [←List.singleton_append]
          apply congr_arg₂
          · rewrite [←List.map_take, list_take_one_drop small]
            rfl
          · simp
      · rw [List.take_succ, List.map_append]
        simp [*]
  convert scan_segment (w[w.length - k.succ]'lt_wl).length (by rfl) using 2
  · rw [List.take_length]
  · rewrite [List.drop_length, List.map_nil]
    rfl

private lemma terminal_scan_aux {g : Grammar T} {w : List (List T)}
    (terminals : ∀ v ∈ w, ∀ t ∈ v, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten) :
  g.star.Derives
    ([R] ++ ((w.map (List.map Symbol.terminal)).map ([H] ++ ·)).flatten ++ [H])
    (w.flatten.map Symbol.terminal ++ [R, H]) :=
by
  rw [List.map_map]
  convert terminal_scan_ind w.length (by rfl) terminals using 1
  rewrite [Nat.sub_self, List.take_zero]
  rfl

end easy_direction


section hard_direction

lemma zero_of_not_ge_one {n : ℕ} (not_pos : ¬n ≥ 1) : n = 0 := by
  push_neg at not_pos
  rwa [Nat.lt_one_iff] at not_pos

lemma length_ge_one_of_not_nil {α : Type _} {l : List α} (lnn : l ≠ []) : l.length ≥ 1 := by
  by_contra contra
  have llz := zero_of_not_ge_one contra
  rw [List.length_eq_zero_iff] at llz
  exact lnn llz

private lemma nat_eq_tech {a b c : ℕ} (b_lt_c : b < c) (c_eq : c = a.succ + c - b.succ) : a = b := by
  omega

private lemma wrap_never_outputs_nt_inr {N : Type} {a : Symbol T N} (i : Fin 3) :
  wrapSym a ≠ Symbol.nonterminal ◪i :=
by
  cases a <;> unfold wrapSym
  · apply Symbol.noConfusion
  intro contr
  have inl_eq_inr := Symbol.nonterminal.inj contr
  exact Sum.noConfusion inl_eq_inr

private lemma wrap_never_outputs_Z {N : Type} {a : Symbol T N} : wrapSym a ≠ Z :=
  wrap_never_outputs_nt_inr 0

private lemma wrap_never_outputs_H {N : Type} {a : Symbol T N} : wrapSym a ≠ H :=
  wrap_never_outputs_nt_inr 1

private lemma wrap_never_outputs_R {N : Type} {a : Symbol T N} : wrapSym a ≠ R :=
  wrap_never_outputs_nt_inr 2

private lemma map_wrap_never_contains_nt_inr {N : Type} {l : List (Symbol T N)} (i : Fin 3) :
  Symbol.nonterminal ◪i ∉ l.map wrapSym :=
by
  intro contra
  rw [List.mem_map] at contra
  rcases contra with ⟨s, -, imposs⟩
  exact wrap_never_outputs_nt_inr i imposs

private lemma map_wrap_never_contains_Z {N : Type} {l : List (Symbol T N)} :
  Z ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 0

private lemma map_wrap_never_contains_H {N : Type} {l : List (Symbol T N)} :
  H ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 1

private lemma map_wrap_never_contains_R {N : Type} {l : List (Symbol T N)} :
  R ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 2

private lemma wrapSym_inj {N : Type} {a b : Symbol T N} (wrap_eq : wrapSym a = wrapSym b) :
  a = b :=
by
  cases a
  · cases b
    · congr
      exact Symbol.terminal.inj wrap_eq
    · exfalso
      exact Symbol.noConfusion wrap_eq
  · cases b
    · exfalso
      exact Symbol.noConfusion wrap_eq
    · congr
      unfold wrapSym at wrap_eq
      exact Sum.inl.inj (Symbol.nonterminal.inj wrap_eq)

private lemma map_wrapSym_inj {N : Type} {x y : List (Symbol T N)}
    (wrap_eqs : x.map wrapSym = y.map wrapSym) :
  x = y :=
by
  ext1 n
  have eqnth := congr_arg (·[n]?) wrap_eqs
  dsimp only at eqnth
  rw [List.getElem?_map, List.getElem?_map] at eqnth
  cases' hxn : x[n]? with xₙ
  · cases' hyn : y[n]? with yₙ
    · rfl
    · exfalso
      simp_all
  · cases' hyn : y[n]? with yₙ
    · exfalso
      simp_all
    · congr
      apply wrapSym_inj
      simp_all

private lemma H_not_in_rule_input {g : Grammar T} {r : Grule T g.nt} :
  H ∉ r.inputL.map wrapSym ++ [Symbol.nonterminal ◩r.inputN] ++ r.inputR.map wrapSym :=
by
  intro contra
  rw [List.mem_append] at contra
  cases contra with
  | inl hHrLN =>
    rw [List.mem_append] at hHrLN
    cases hHrLN with
    | inl hHrL => exact map_wrap_never_contains_H hHrL
    | inr hHrN =>
      rw [List.mem_singleton] at hHrN
      exact Sum.noConfusion (Symbol.nonterminal.inj hHrN)
  | inr hHrR => exact map_wrap_never_contains_H hHrR

private lemma snsri_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} {i : Fin 3}
    (snsri_neq_H : Symbol.nonterminal ◪i ≠ @H T g.nt) :
  Symbol.nonterminal ◪i ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
by
  intro contra
  rw [List.mem_flatten, List.map_map] at contra
  rcases contra with ⟨l, l_in, in_l⟩
  rw [List.mem_map] at l_in
  rcases l_in with ⟨y, -, eq_l⟩
  rw [← eq_l] at in_l
  rw [Function.comp_apply, List.mem_append] at in_l
  cases in_l with
  | inl hiy => exact map_wrap_never_contains_nt_inr i hiy
  | inr hiH =>
    rw [List.mem_singleton] at hiH
    exact snsri_neq_H hiH

private lemma Z_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} :
  Z ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
snsri_not_in_join_mpHmmw Z_neq_H

private lemma R_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} :
  R ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
snsri_not_in_join_mpHmmw H_neq_R.symm

private lemma zero_Rs_in_the_long_part {g : Grammar T} {x : List (List (Symbol T g.nt))} [DecidableEq (ns T g.nt)] :
  ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.countIn R = 0 :=
List.countIn_zero_of_notin R_not_in_join_mpHmmw

private lemma cases_1_and_2_and_3a_match_aux {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} (xnn : x ≠ [])
    (hyp :
      ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten :=
by
  have hypp : ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym) ++ v
  · simpa [List.append_assoc] using hyp
  have mid_brack :
    ∀ u' v' : List (Symbol T g.nt),
      u' ++  r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR  ++ v' =
      u' ++ (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR) ++ v'
  · intro _ _
    simp only [List.append_assoc]
  simp_rw [mid_brack]
  clear hyp mid_brack
  classical
  have count_Hs := congr_arg (·.countIn H) hypp
  dsimp only at count_Hs
  rw [List.countIn_append, List.countIn_append, List.countIn_zero_of_notin H_not_in_rule_input,
      add_zero, List.countIn_flatten, List.map_map, List.map_map] at count_Hs
  have lens := congr_arg List.length hypp
  rw [List.length_append_append, List.length_append_append, List.length_singleton] at lens
  have ul_lt : u.length < ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.length
  · clear * - lens
    linarith
  rcases List.take_flatten_of_lt ul_lt with ⟨m, k, mlt, klt, init_ul⟩
  have vnn : v ≠ []
  · by_contra v_nil
    rw [v_nil, List.append_nil] at hypp
    clear * - hypp xnn
    have hlast := congr_arg (fun l : List (ns T g.nt) => l.reverse[0]?) hypp
    dsimp only at hlast
    rw [List.reverse_flatten, List.reverse_append, List.reverse_append_append, List.reverse_singleton] at hlast
    have hhh : some H =
        ((r₀.inputR.map wrapSym).reverse ++ [Symbol.nonterminal ◩r₀.inputN] ++ (r₀.inputL.map wrapSym).reverse ++ u.reverse)[0]?
    · convert hlast
      rw [List.map_map]
      show
        some H =
        ((x.map (List.map wrapSym)).map (fun l : List (ns T g.nt) => List.reverse (l ++ [H]))).reverse.flatten[0]?
      simp_rw [List.reverse_append]
      rw [List.map_map]
      show
        some H =
        (x.map (fun l : List (Symbol T g.nt) => [H].reverse ++ (l.map wrapSym).reverse)).reverse.flatten[0]?
      rw [← List.map_reverse]
      have xrnn : x.reverse ≠ []
      · intro xr_nil
        rw [List.reverse_eq_iff] at xr_nil
        exact xnn xr_nil
      cases' hx : x.reverse with d l
      · exfalso
        exact xrnn hx
      rw [List.map_cons, List.flatten, List.append_assoc, List.getElem?_append]
      simp
    rw [← List.map_reverse] at hhh
    cases hr₀ : r₀.inputR.reverse
    · rw [hr₀] at hhh
      simp at hhh
      exact Sum.noConfusion (Symbol.nonterminal.inj hhh)
    · rw [hr₀] at hhh
      simp at hhh
      exact wrap_never_outputs_H hhh.symm
  have urrrl_lt : (u ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym)).length <
      ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.length
  · have vl_pos : v.length > 0 := List.length_pos_of_ne_nil vnn
    clear * - lens vl_pos
    rw [List.length_append]
    rw [List.length_append_append]
    rw [List.length_singleton]
    linarith
  rcases List.drop_flatten_of_lt urrrl_lt with ⟨m', k', mlt', klt', last_vl⟩
  have mxl : m < x.length
  · rw [List.length_map] at mlt
    rw [List.length_map] at mlt
    exact mlt
  have mxl' : m' < x.length
  · rw [List.length_map] at mlt'
    rw [List.length_map] at mlt'
    exact mlt'
  have mxlmm : m < (x.map (List.map wrapSym)).length
  · rwa [List.length_map]
  have mxlmm' : m' < (x.map (List.map wrapSym)).length
  · rwa [List.length_map]
  use m, (x.get ⟨m, mxl⟩).take k, (x.get ⟨m', mxl'⟩).drop k'
  have hyp_u := congr_arg (List.take u.length) hypp
  rw [List.append_assoc, List.take_left, init_ul] at hyp_u
  simp only [List.map_map, List.get_eq_getElem, Function.comp_apply] at hyp_u
  rw [List.getElem_map] at hyp_u
  have hyp_v :=
    congr_arg
      (List.drop
        (u ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym)).length)
      hypp
  rw [List.drop_left, last_vl] at hyp_v
  rw [←hyp_u, ←hyp_v] at count_Hs
  have hmm : m = m'
  · clear * - count_Hs mxl mxl' klt klt'
    simp [List.countIn_append, List.countIn_flatten] at count_Hs
    have inside_wrap : ∀ y : List (Symbol T g.nt), (y.map wrapSym).countIn H = 0
    · intro
      rw [List.countIn_zero_of_notin]
      apply map_wrap_never_contains_H
    have inside_one :
      ∀ z : List (Symbol T g.nt),
        (z.map wrapSym).countIn (@H T g.nt) + [@H T g.nt].countIn (@H T g.nt) = 1
    · intro
      rw [List.countIn_singleton_eq H, inside_wrap]
    have inside_take : (((x[m]'mxl).map wrapSym).take k).countIn H = 0
    · rw [← List.map_take, inside_wrap]
    have inside_drop : (((x[m']'mxl').map wrapSym).drop k').countIn H + [@H T g.nt].countIn H = 1
    · rw [← List.map_drop, inside_wrap, List.countIn_singleton_eq (@H T g.nt)]
    have counted_Hs : x.length = (m + 0) + (1 + (x.length - m'.succ))
    · convert count_Hs using 3
      · show x.length = (x.map (fun l : List (Symbol T g.nt) => (l.map wrapSym ++ [H]).countIn H)).sum
        simp [List.countIn_append, inside_one]
      · show m = ((x.map (fun l : List (Symbol T g.nt) => (l.map wrapSym ++ [H]).countIn H)).take m).sum
        simp [List.countIn_append, inside_one, Nat.le_of_succ_le mxl]
      · rw [List.take_append_of_le_length, inside_take]
        apply Nat.le_of_lt_succ
        simpa using klt
      · rw [List.drop_append_of_le_length, List.countIn_append, inside_drop]
        apply Nat.le_of_lt_succ
        simpa using klt'
      · show x.length - m'.succ = ((x.map (fun l : List (Symbol T g.nt) => (l.map wrapSym ++ [H]).countIn H)).drop m'.succ).sum
        simp [List.countIn_append, inside_one]
    omega
  constructor
  · convert hyp_u.symm using 1
    simp_all
    exact Nat.le_of_lt_succ klt
  constructor
  · have x_eq : x = x.take m ++ [x[m]'mxl] ++ x.drop m.succ
    · simp
    have hyppp :
      (((x.take m ++ [x[m]'mxl] ++ x.drop m.succ).map (List.map wrapSym)).map (· ++ [H])).flatten =
      (((x.map (List.map wrapSym)).map (· ++ [H])).take m).flatten ++
        ((x.map (List.map wrapSym))[m]'mxlmm).take k ++
        (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym) ++
        (((x.map (List.map wrapSym))[m]'mxlmm).drop k' ++ [H] ++
          (((x.map (List.map wrapSym)).map (· ++ [H])).drop m.succ).flatten)
    · convert hypp
      · exact x_eq.symm
      · convert hyp_u using 1
        simp
        apply Nat.le_of_lt_succ
        simpa using klt
      · convert hyp_v using 1
        simp
        rw [←List.singleton_append, ←List.append_assoc, List.drop_append_of_le_length]
        simp [hmm]
        apply Nat.le_of_lt_succ
        simpa using klt'
    rw [List.map_append_append, List.map_append_append, List.flatten_append_append, List.append_assoc,
        List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
        List.map_take, List.map_take, List.append_right_inj, ←List.append_assoc, ←List.append_assoc,
        ←List.append_assoc, ←List.append_assoc, ←List.append_assoc, List.map_drop, List.map_drop,
        List.append_left_inj, List.map_singleton, List.map_singleton, List.flatten_singleton,
        List.append_left_inj] at hyppp
    rw [List.get?_eq_some]
    use mxl
    apply map_wrapSym_inj
    rw [hyppp]
    simp [hmm]
    rfl
  · convert hyp_v.symm using 1
    simp
    rw [←List.singleton_append, ←List.append_assoc, List.drop_append_of_le_length, hmm]
    simpa using Nat.le_of_lt_succ (by simpa using klt')

private lemma case_1_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp :
      (Z :: ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (Z :: (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten) ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten :=
by
  by_cases is_x_nil : x = []
  · exfalso
    rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at hyp
    have hyp_len := congr_arg List.length hyp
    rw [List.length_singleton] at hyp_len
    repeat rw [List.length_append] at hyp_len
    rw [List.length_singleton] at hyp_len
    have left_nil : u ++ r₀.inputL.map wrapSym = []
    · rw [← List.length_eq_zero_iff, List.length_append]
      omega
    have right_nil : r₀.inputR.map wrapSym ++ v = []
    · rw [← List.length_eq_zero_iff, List.length_append]
      omega
    rw [left_nil, List.nil_append, List.append_assoc, right_nil, List.append_nil] at hyp
    have imposs := List.head_eq_of_cons_eq hyp
    unfold Z at imposs
    simp_all
  have unn : u ≠ []
  · by_contra u_nil
    rw [u_nil, List.nil_append] at hyp
    cases' hr₀ : r₀.inputL with d l
    · rw [hr₀, List.map_nil, List.nil_append] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      exact Sum.noConfusion inr_eq_inl
    · rw [hr₀, List.map_cons] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      cases d
      · unfold wrapSym at imposs
        exact Symbol.noConfusion imposs
      · unfold wrapSym at imposs
        have inr_eq_inl := Symbol.nonterminal.inj imposs
        exact Sum.noConfusion inr_eq_inl
  have hypr := congr_arg List.tail hyp
  rw [List.tail] at hypr
  repeat rw [List.append_assoc] at hypr
  rw [List.tail_append_of_ne_nil unn] at hypr
  repeat rw [← List.append_assoc] at hypr
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hypr with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
  use m, u₁, v₁
  constructor
  · cases' u with d l
    · exfalso
      exact unn rfl
    have headZ : d = Z
    · repeat rw [List.cons_append] at hyp
      exact List.head_eq_of_cons_eq hyp.symm
    rw [headZ]
    rw [List.tail] at u_eq
    rw [u_eq]
    apply List.cons_append
  constructor
  · simp_all
  · exact v_eq

private lemma star_case_1 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp :
      ∃ x : List (List (Symbol T g.nt)),
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
          α = [Z] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = [Z] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
      α' = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :=
by
  rcases hyp with ⟨x, valid, cat⟩
  have no_R_in_alpha : R ∉ α
  · intro contr
    rw [cat] at contr
    clear * - contr
    rw [List.mem_append] at contr
    cases contr with
    | inl hRZ => exact Z_neq_R.symm (List.mem_singleton.→ hRZ)
    | inr hRH => exact R_not_in_join_mpHmmw hRH
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    dsimp only at *
    rw [List.append_nil, List.append_nil] at bef
    left
    use [Symbol.nonterminal g.initial] :: x
    constructor
    · intro xᵢ xin
      cases xin with
      | head => apply gr_deri_self
      | tail _ xin => exact valid xᵢ xin
    have u_nil : u = []
    · clear * - bef cat
      rw [← List.length_eq_zero_iff]
      by_contra
      have ul_pos : 0 < u.length
      · rwa [pos_iff_ne_zero]
      have bef_tail := congr_arg List.tail bef
      cases' u with d l
      · rw [List.length] at ul_pos
        exact Nat.lt_irrefl 0 ul_pos
      · have Z_in_tail : Z ∈ l ++ [Symbol.nonterminal ◪0] ++ v
        · apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_singleton_self
        rw [cat, List.singleton_append, List.tail_cons, List.cons_append, List.cons_append, List.tail_cons] at bef_tail
        rw [← bef_tail] at Z_in_tail
        exact Z_not_in_join_mpHmmw Z_in_tail
    have v_rest : v = ((x.map (List.map wrapSym)).map (· ++ [H])).flatten
    · rw [u_nil, cat] at bef
      convert congr_arg List.tail bef.symm
    rewrite [aft, u_nil, v_rest, List.nil_append, List.map_cons]
    rfl
  | tail _ rin =>
    cases rin with
    | head =>
      right
      dsimp only at *
      use x
      constructor
      · exact valid
      have u_nil : u = []
      · clear * - bef cat
        rw [← List.length_eq_zero_iff]
        by_contra
        have ul_pos : 0 < u.length
        · rwa [pos_iff_ne_zero]
        have bef_tail := congr_arg List.tail bef
        cases' u with d l
        · rw [List.length] at ul_pos
          exact Nat.lt_irrefl 0 ul_pos
        · have Z_in_tail : Z ∈ l ++ [Symbol.nonterminal ◪0] ++ v
          · apply List.mem_append_left
            apply List.mem_append_right
            apply List.mem_singleton_self
          rw [cat, List.singleton_append, List.tail_cons,
            List.cons_append, List.cons_append, List.append_nil, List.append_nil, List.cons_append, List.tail_cons
          ] at bef_tail
          rw [← bef_tail] at Z_in_tail
          exact Z_not_in_join_mpHmmw Z_in_tail
      have v_rest : v = ((x.map (List.map wrapSym)).map (· ++ [H])).flatten
      · rw [cat, u_nil] at bef
        convert congr_arg List.tail bef.symm
      rw [aft, u_nil, v_rest]
      rfl
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        apply no_R_in_alpha
        rw [bef]
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_singleton]
        rfl
      | tail _ rin =>
        cases rin with
        | head =>
          exfalso
          apply no_R_in_alpha
          rw [bef]
          apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_append_right
          rw [List.mem_singleton]
          rfl
        | tail _ rin =>
          have rin' : r ∈ rulesThatScanTerminals g ∨ r ∈ g.rules.map wrapGr
          · rwa [or_comm, ← List.mem_append]
          clear rin
          cases' rin' with rin' rin'
          · exfalso
            apply no_R_in_alpha
            rw [bef]
            apply List.mem_append_left
            apply List.mem_append_left
            apply List.mem_append_right
            rw [List.mem_singleton]
            unfold rulesThatScanTerminals at rin'
            rw [List.mem_map] at rin'
            rcases rin' with ⟨t, -, form⟩
            rw [← form]
            rfl
          · left
            rw [List.mem_map] at rin'
            rcases rin' with ⟨r₀, orig_in, wrap_orig⟩
            rw [cat, ←wrap_orig] at bef
            obtain ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩ := case_1_match_rule bef
            clear bef
            rw [u_eq, v_eq] at aft
            use x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ x.drop m.succ
            constructor
            · intro xᵢ xiin
              rw [List.mem_append_append] at xiin
              cases xiin with
              | inl xiin =>
                apply valid
                exact List.mem_of_mem_take xiin
              | inr xiin =>
                cases xiin with
                | inl xiin =>
                  rw [List.mem_singleton] at xiin
                  rw [xiin]
                  have last_step :
                    g.Transforms
                      (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                      (u₁ ++ r₀.output ++ v₁)
                  · use r₀, orig_in, u₁, v₁
                  apply gr_deri_of_deri_tran _ last_step
                  apply valid (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                  exact List.mem_of_getElem? xm_eq
                | inr xiin =>
                  apply valid
                  exact List.mem_of_mem_drop xiin
            rw [List.singleton_append, aft]
            simp [←wrap_orig, wrapGr]

private lemma uv_nil_of_RH_eq {g : Grammar T} {u v : List (ns T g.nt)}
    (ass : [R, H] = u ++ [] ++ [Symbol.nonterminal ◪2] ++ [H] ++ v) :
  u = [] ∧ v = [] :=
by
  rw [List.append_nil] at ass
  have lens := congr_arg List.length ass
  simp only [List.length_append, List.length, zero_add] at lens
  constructor <;>
    · rw [← List.length_eq_zero_iff]
      omega

private lemma u_nil_when_RH {g : Grammar T} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (ass :
      [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [] ++ [Symbol.nonterminal ◪2] ++ [H] ++ v) :
  u = [] :=
by
  cases' u with d l
  · rfl
  rw [List.append_nil] at ass
  exfalso
  by_cases hdR : d = R
  · rw [H] at ass
    classical
    have imposs := congr_arg (fun c : List (ns T g.nt) => c.countIn R) ass
    simp only [List.countIn_append, List.countIn_cons, List.countIn_nil, hdR, ite_true] at imposs
    have h0 : 0 = if Symbol.nonterminal ◪1 = @R T g.nt then 1 else 0
    · rfl
    have one_imposs : 1 + (0 + 0) + 0 = 1 + l.countIn R + (1 + 0) + (0 + 0) + v.countIn R
    · convert imposs
      · convert h0
      · symm
        apply zero_Rs_in_the_long_part
      · simp [R]
      · convert h0
    clear * - one_imposs
    linarith
  · simp_all

private lemma case_2_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp :
      R :: H :: ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (R :: H :: (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten) ++ List.map wrapSym u₁ ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten :=
by
  by_cases is_x_nil : x = []
  · exfalso
    rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at hyp
    have imposs : Symbol.nonterminal ◩r₀.inputN = R ∨ Symbol.nonterminal ◩r₀.inputN = H
    · simpa using congr_arg (Symbol.nonterminal ◩r₀.inputN ∈ ·) hyp
    cases' imposs with imposs imposs <;> exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
  have unn : u ≠ [] := by
    by_contra u_nil
    rw [u_nil, List.nil_append] at hyp
    cases hrL : r₀.inputL with
    | nil =>
      rw [hrL] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      exact Sum.noConfusion inr_eq_inl
    | cons d l =>
      rw [hrL, List.map_cons] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      cases d
      · exact Symbol.noConfusion imposs
      · have inr_eq_inl := Symbol.nonterminal.inj imposs
        exact Sum.noConfusion inr_eq_inl
  have hypt := congr_arg List.tail hyp
  rw [List.tail] at hypt
  repeat rw [List.append_assoc] at hypt
  rw [List.tail_append_of_ne_nil unn] at hypt
  have utnn : u.tail ≠ []
  · by_contra ut_nil
    rw [ut_nil, List.nil_append] at hypt
    cases hrL : r₀.inputL with
    | nil =>
      rw [hrL, List.map_nil, List.nil_append] at hypt
      have imposs := List.head_eq_of_cons_eq hypt
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      exact Sum.noConfusion inr_eq_inl
    | cons d l =>
      rw [hrL, List.map_cons] at hypt
      have imposs := List.head_eq_of_cons_eq hypt
      cases d
      · unfold wrapSym at imposs
        exact Symbol.noConfusion imposs
      · unfold wrapSym at imposs
        have inr_eq_inl := Symbol.nonterminal.inj imposs
        exact Sum.noConfusion inr_eq_inl
  have hyptt := congr_arg List.tail hypt
  rw [List.tail, List.tail_append_of_ne_nil utnn] at hyptt
  repeat rw [← List.append_assoc] at hyptt
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hyptt with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
  use m, u₁, v₁
  constructor
  · cases' u with d l
    · exfalso
      exact unn rfl
    have headR : d = R
    · repeat rw [List.cons_append] at hyp
      exact List.head_eq_of_cons_eq hyp.symm
    rw [List.tail] at u_eq hypt
    cases' l with d' l'
    · exfalso
      exact utnn rfl
    have tailHead : d' = H
    · repeat rw [List.cons_append] at hypt
      exact List.head_eq_of_cons_eq hypt.symm
    rw [List.tail] at u_eq
    rw [headR, tailHead, u_eq, List.cons_append, List.cons_append]
  constructor
  · exact xm_eq
  · exact v_eq

private lemma star_case_2 {g : Grammar T} {α α' : List (Symbol T g.star.nt)}
    (hαα : g.star.Transforms α α')
    (hgg : ∃ x : List (List (Symbol T g.nt)),
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
        α = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α' = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hgg with ⟨x, valid, cat⟩
  have no_Z_in_alpha : Z ∉ α
  · intro contr
    rw [cat, List.mem_append] at contr
    refine contr.casesOn (fun ZRH => ?_) Z_not_in_join_mpHmmw
    rw [List.mem_pair] at ZRH
    exact ZRH.casesOn Z_neq_R Z_neq_H
  rcases hαα with ⟨r, rin, u, v, bef, aft⟩
  simp only [Grammar.star, List.mem_cons, List.mem_append, List.mem_map] at rin
  rcases rin with rinputZ | rinputZ | RH_R | RH_nil | original | Rt_tR
  iterate 2
    · exfalso
      apply no_Z_in_alpha
      rw [bef, rinputZ, List.mem_append_append, List.mem_append_append]
      left; right; right
      rw [List.mem_singleton]
      rfl
  · cases' x with x₀ L
    · right; right; right; left
      have empty_string : u = [] ∧ v = []
      · rw [RH_R, cat] at bef
        exact uv_nil_of_RH_eq bef
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft
      use []
      rw [aft, List.map_nil, List.nil_append, RH_R]
    · right; left
      use [], [], x₀, L
      constructor
      · intro wᵢ wiin
        exfalso
        rw [List.mem_nil_iff] at wiin
        exact wiin
      constructor
      · rw [List.map_nil, List.nil_append]
        exact valid x₀ (List.mem_cons_self x₀ L)
      constructor
      · intro xᵢ xiin
        exact valid xᵢ (List.mem_cons_of_mem x₀ xiin)
      rw [aft, List.map_nil, List.append_nil, List.flatten, List.map_nil, List.nil_append]
      rw [RH_R] at bef ⊢
      rw [cat] at bef
      have u_nil := u_nil_when_RH bef
      rw [u_nil, List.nil_append] at bef ⊢
      rw [← List.append_inj_right bef (by rfl), List.map_cons, List.map_cons, List.flatten, ← List.append_assoc, ← List.append_assoc]
  · cases hx : x with
    | nil =>
      right; right; left
      rw [cat, hx, List.map_nil, List.map_nil, List.flatten, List.append_nil] at bef
      have empty_string : u = [] ∧ v = []
      · rw [RH_nil] at bef
        exact uv_nil_of_RH_eq bef
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft
      use []
      constructor
      · use []
        constructor
        · rfl
        · intro y imposs
          exfalso
          exact List.not_mem_nil y imposs
      · rw [aft]
        rw [List.map_nil]
        rw [RH_nil]
    | cons x₀ L =>
      right; right; right; right
      rw [cat, RH_nil] at bef
      dsimp only at bef
      have u_nil := u_nil_when_RH bef
      rw [u_nil, List.nil_append] at bef
      have v_eq := Eq.symm (List.append_inj_right bef (by rfl))
      rw [u_nil, List.nil_append, v_eq, RH_nil, List.nil_append, hx, List.map_cons, List.map_cons,
          List.flatten, List.append_assoc, List.append_flatten_map_append, ← List.append_assoc] at aft
      constructor
      · use x₀.map wrapSym ++ ((L.map (List.map wrapSym)).map ([H] ++ ·)).flatten
      rw [List.append_assoc, ← List.append_flatten_map_append] at aft
      rw [aft]
      constructor <;> intro contra <;> rw [List.mem_append] at contra
      · refine contra.casesOn map_wrap_never_contains_Z (fun contr => ?_)
        rw [List.mem_append] at contr
        refine contr.casesOn (fun hR => ?_) Z_not_in_join_mpHmmw
        simp_rw [List.mem_cons, List.not_mem_nil, or_false] at hR
        exact Z_neq_H hR
      · refine contra.casesOn map_wrap_never_contains_R (fun contr => ?_)
        rw [List.mem_append] at contr
        refine contr.casesOn (fun hR => ?_) R_not_in_join_mpHmmw
        simp_rw [List.mem_cons, List.not_mem_nil, or_false] at hR
        exact H_neq_R hR.symm
  · left
    rcases original with ⟨r₀, orig_in, wrap_orig⟩
    unfold wrapGr at wrap_orig
    rw [cat, ←wrap_orig] at bef
    change R :: H :: List.flatten _ = _ at bef
    rcases case_2_match_rule bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
    clear bef
    rw [u_eq, v_eq] at aft
    use x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ List.drop m.succ x
    constructor
    · intro xᵢ xiin
      rw [List.mem_append_append] at xiin
      cases xiin with
      | inl xiin =>
        apply valid
        exact List.mem_of_mem_take xiin
      | inr xiin =>
        cases xiin with
        | inr xiin =>
          apply valid
          exact List.mem_of_mem_drop xiin
        | inl xiin =>
          rw [List.mem_singleton] at xiin
          rw [xiin]
          have last_step :
            g.Transforms
              (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
              (u₁ ++ r₀.output ++ v₁)
          · use r₀, orig_in, u₁, v₁
          apply gr_deri_of_deri_tran _ last_step
          apply valid (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
          exact List.mem_of_getElem? xm_eq
    rw [aft, ←wrap_orig]
    simp
  · exfalso
    unfold rulesThatScanTerminals at Rt_tR
    rw [List.mem_map] at Rt_tR
    rcases Rt_tR with ⟨t, -, form⟩
    rw [← form] at bef
    dsimp only at bef
    rw [List.append_nil] at bef
    have u_nil : u = []
    · cases' u with d l
      · rfl
      exfalso
      rw [cat] at bef
      repeat rw [List.cons_append] at bef
      rw [List.nil_append] at bef
      have btail := List.tail_eq_of_cons_eq bef
      have imposs := congr_arg (fun l => R ∈ l) btail
      dsimp only at imposs
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_singleton_self
      · rw [false_iff]
        intro hyp
        rw [List.mem_cons] at hyp
        cases hyp with
        | inl hRH => exact H_neq_R hRH.symm
        | inr Rin =>
          rw [List.mem_flatten] at Rin
          rcases Rin with ⟨p, pin, Rinp⟩
          rw [List.mem_map] at pin
          rcases pin with ⟨q, qin, eq_p⟩
          rw [← eq_p] at Rinp
          rw [List.mem_append] at Rinp
          cases Rinp with
          | inl hRq =>
            rw [List.mem_map] at qin
            rcases qin with ⟨p', -, eq_q⟩
            rw [← eq_q] at hRq
            exact map_wrap_never_contains_R hRq
          | inr hRH =>
            rw [List.mem_singleton] at hRH
            exact H_neq_R hRH.symm
    rw [u_nil, cat] at bef
    have second_symbol := (congr_arg (·[1]?) bef)
    simp [H] at second_symbol

private lemma case_3_ni_wb {g : Grammar T} {w : List (List T)} {β : List T} {i : Fin 3} :
  @Symbol.nonterminal T (nn g.nt) ◪i ∉
    w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map (@Symbol.terminal T (nn g.nt)) :=
by
  intro contra
  rw [List.mem_append] at contra
  cases' contra with contra contra <;> rw [List.mem_map] at contra <;> rcases contra with ⟨t, -, imposs⟩ <;> exact Symbol.noConfusion imposs

private lemma case_3_ni_u {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {s : ns T g.nt}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        (List.map (· ++ [H]) (x.map (List.map wrapSym))).flatten =
      u ++ [R] ++ [s] ++ v) :
  R ∉ u :=
by
  intro R_in_u
  classical
  have count_R := congr_arg (·.countIn R) ass
  dsimp only at count_R
  repeat rw [List.countIn_append] at count_R
  have R_ni_wb : @R T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
  · apply case_3_ni_wb
  rw [List.countIn_singleton_eq, List.countIn_singleton_neq H_neq_R, add_zero,
      ←List.countIn_append, List.countIn_zero_of_notin R_ni_wb, zero_add,
      List.countIn_zero_of_notin map_wrap_never_contains_R, add_zero,
      zero_Rs_in_the_long_part, add_zero
  ] at count_R
  have ucR_pos := List.countIn_pos_of_in R_in_u
  clear * - count_R ucR_pos
  linarith

private lemma case_3_u_eq_left_side {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {s : ns T g.nt}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [Symbol.nonterminal ◪2] ++ [s] ++ v) :
  u = w.flatten.map Symbol.terminal ++ β.map (@Symbol.terminal T (nn g.nt)) :=
by
  have R_ni_u : R ∉ u := case_3_ni_u ass
  have R_ni_wb : R ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
  · apply @case_3_ni_wb T g
  repeat rw [List.append_assoc] at ass
  convert congr_arg (List.take u.length) ass.symm using 1
  · rw [List.take_left]
  rw [←List.append_assoc, List.take_left']
  classical
  have index_of_first_R := congr_arg (List.idxOf R) ass
  rwa [List.idxOf_append_of_not_mem R_ni_u, @List.singleton_append _ _ ([s] ++ v), ←R, List.idxOf_cons_self, add_zero,
      ←List.append_assoc, List.idxOf_append_of_not_mem R_ni_wb, List.singleton_append, List.idxOf_cons_self, add_zero
  ] at index_of_first_R

private lemma case_3_gamma_nil {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [Symbol.nonterminal ◪2] ++ [H] ++ v) :
  γ = [] :=
by
  have R_ni_wb : @R T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
  · apply case_3_ni_wb
  have H_ni_wb : @H T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
  · apply case_3_ni_wb
  have H_ni_wbrg : H ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym
  · intro contra
    rw [List.mem_append] at contra
    refine contra.casesOn (fun hH => ?_) map_wrap_never_contains_H
    rw [List.mem_append] at hH
    refine hH.casesOn H_ni_wb (fun hHR => ?_)
    rw [List.mem_singleton] at hHR
    exact H_neq_R hHR
  have R_ni_u : @Symbol.nonterminal T (nn g.nt) ◪2 ∉ u := case_3_ni_u ass
  have H_ni_u : H ∉ u := case_3_u_eq_left_side ass ▸ H_ni_wb
  classical
  have first_R := congr_arg (List.idxOf R) ass
  have first_H := congr_arg (List.idxOf H) ass
  simp only [List.append_assoc (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal)] at first_R
  simp only [List.append_assoc (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym)] at first_H
  rw [List.idxOf_append_of_not_mem R_ni_wb] at first_R
  rw [List.idxOf_append_of_not_mem H_ni_wbrg] at first_H
  rw [List.cons_append, List.cons_append, List.cons_append, R, List.idxOf_cons_self, add_zero] at first_R
  rw [List.cons_append, List.idxOf_cons_self, add_zero] at first_H
  rw [List.append_assoc u, List.append_assoc u] at first_R first_H
  rw [List.idxOf_append_of_not_mem R_ni_u] at first_R
  rw [List.idxOf_append_of_not_mem H_ni_u] at first_H
  rw [List.append_assoc _ [H], List.singleton_append, List.idxOf_cons_self, add_zero] at first_R
  rw [List.append_assoc _ [H], List.singleton_append, ← R, List.idxOf_cons_ne _ H_neq_R.symm,
      List.singleton_append, H, List.idxOf_cons_self, ← first_R
  ] at first_H
  rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
      ←add_zero ((w.flatten.map Symbol.terminal).length + (β.map Symbol.terminal).length + 1)
  ] at first_H
  simpa using first_H

private lemma case_3_v_nil {g : Grammar T} {w : List (List T)} {β : List T} {u v : List (ns T g.nt)}
    (ass : w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ [H] = u ++ [R] ++ [H] ++ v) :
  v = [] :=
by
  have rev := congr_arg List.reverse ass
  simp only [List.reverse_append, List.reverse_singleton] at rev
  rw [← List.reverse_nil]
  cases hv : v.reverse with
  | nil => exact List.reverse_eq_iff.→ hv
  | cons d l =>
    exfalso
    rw [hv, List.singleton_append] at rev
    have brt := List.tail_eq_of_cons_eq rev
    have brtt := congr_arg List.tail brt
    rw [List.singleton_append] at brtt
    rw [List.tail_cons] at brtt
    cases hl : l with
    | nil =>
      rw [hl] at brtt
      change (β.map Symbol.terminal).reverse ++ (w.flatten.map Symbol.terminal).reverse = [R] ++ u.reverse at brtt
      have imposs := congr_arg (R ∈ ·) brtt
      dsimp only at imposs
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_left
        apply List.mem_singleton_self
      · rw [false_iff, List.mem_append]
        push_neg
        constructor <;> unfold H at * <;> aesop
    | cons e l' =>
      rw [hl] at brtt
      have imposs := congr_arg (H ∈ ·) brtt
      dsimp only at imposs
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_right
        apply List.mem_append_left
        apply List.mem_singleton_self
      · rw [false_iff]
        rw [List.mem_append]
        push_neg
        constructor <;> unfold H at * <;> aesop

private lemma case_3_false_of_wbr_eq_urz {g : Grammar T} {r₀ : Grule T g.nt} {w : List (List T)}
    {β : List T} {u z : List (ns T g.nt)}
    (contradictory_equality :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ z) :
  False :=
by
  apply false_of_true_eq_false
  convert congr_arg ((Symbol.nonterminal ◩r₀.inputN ∈ ·)) contradictory_equality.symm
  · rw [true_iff]
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_singleton_self
  · rw [false_iff]
    intro hyp_N_in
    rw [List.mem_append] at hyp_N_in
    cases hyp_N_in with
    | inl hr₀ =>
      rw [List.mem_append] at hr₀
      cases hr₀ with
      | inl hw =>
        rw [List.mem_map] at hw
        rcases hw with ⟨t, -, impos⟩
        exact Symbol.noConfusion impos
      | inr hβ =>
        rw [List.mem_map] at hβ
        rcases hβ with ⟨t, -, impos⟩
        exact Symbol.noConfusion impos
    | inr hR =>
      rw [List.mem_singleton] at hR
      exact Sum.noConfusion (Symbol.nonterminal.inj hR)

private lemma case_3_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {w : List (List T)} {β : List T} {γ : List (Symbol T g.nt)}
    (hyp :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  (∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        (List.map (· ++ [H]) ((x.map (List.map wrapSym)).take m)).flatten ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten) ∨
  (∃ u₁ v₁ : List (Symbol T g.nt),
    u = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ u₁.map wrapSym ∧
    γ = u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁ ∧
    v = v₁.map wrapSym ++ [H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :=
by
  repeat rw [List.append_assoc u] at hyp
  rw [List.append_eq_append_iff] at hyp
  cases hyp with
  | inl hypl =>
    rcases hypl with ⟨u', u_eq, xj_eq⟩
    left
    repeat rw [← List.append_assoc] at xj_eq
    by_cases is_x_nil : x = []
    · exfalso
      rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at xj_eq
      have imposs := congr_arg List.length xj_eq
      rw [List.length, List.length_append_append, List.length_append_append, List.length_singleton] at imposs
      clear * - imposs
      linarith
    rcases cases_1_and_2_and_3a_match_aux is_x_nil xj_eq with ⟨m, u₁, v₁, u'_eq, xm_eq, v_eq⟩
    use m, u₁, v₁
    constructor
    · rw [u_eq, u'_eq, ←List.append_assoc]
    constructor
    · exact xm_eq
    · exact v_eq
  | inr hypr =>
    rcases hypr with ⟨v', left_half, right_half⟩
    have very_middle : [@Symbol.nonterminal T _ ◩r₀.inputN] = List.map wrapSym [Symbol.nonterminal r₀.inputN]
    · apply List.map_singleton
    rw [List.append_assoc _ (γ.map wrapSym)] at left_half
    have v'_from_left := congr_arg (List.drop u.length) left_half
    simp only [List.drop_left'] at v'_from_left
    have le_u_len : (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length ≤ u.length
    · by_contra! contr
      have contr' : u.length ≤ (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal).length
      · simp only [List.length_append] at contr ⊢
        rw [List.length_singleton] at contr
        exact Nat.le_of_lt_succ contr
      rw [List.append_assoc _ [R], List.drop_append_of_le_length contr'] at v'_from_left
      rw [←v'_from_left] at right_half
      have right_half' :
        r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym ++ v =
        ((w.flatten.map Symbol.terminal ++ β.map Symbol.terminal).drop u.length ++ [R]) ++ ((γ.map wrapSym ++ [H]) ++
          ((x.map (List.map wrapSym)).map (· ++ [H])).flatten)
      · convert right_half using 1
        simp
      rw [List.append_eq_append_iff] at right_half'
      cases right_half' with
      | inl has =>
        have r₀Nin : Symbol.nonterminal ◩r₀.inputN ∈ (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal).drop u.length ++ [R]
        · obtain ⟨_, _, -⟩ := has
          aesop
        rw [List.mem_append] at r₀Nin
        cases r₀Nin with
        | inl among_terminals =>
          rw [←List.map_append, ←List.map_drop, List.mem_map] at among_terminals
          obtain ⟨t, -, ht⟩ := among_terminals
          exact Symbol.noConfusion ht
        | inr hR =>
          rw [List.mem_singleton] at hR
          exact Sum.noConfusion (Symbol.nonterminal.inj hR)
      | inr hbs =>
        have Rin : R ∈ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym
        · obtain ⟨_, _, -⟩ := hbs
          simp_all
        rw [very_middle, ←List.map_append_append] at Rin
        exact map_wrap_never_contains_R Rin
    have v'_is_suffix : v' = (γ.map wrapSym ++ [H]).drop
        (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)
    · rw [←v'_from_left, List.drop_append']
      convert List.nil_append _
      exact List.drop_of_length_le le_u_len
    -- have hnγ : u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length ≤ (γ.map wrapSym).length
    -- · sorry -- maybe extract explicit `n` above
    obtain ⟨o, hor₀⟩ :
      ∃ o : ℕ,
        r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym =
        ((γ.map wrapSym).drop (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)).take o
    · have middle_part_r := congr_arg (List.take (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym).length) right_half
      rw [List.take_left] at middle_part_r
      use (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◩r₀.inputN] ++ r₀.inputR.map wrapSym).length
      have middle_part_l := congr_arg (List.drop u.length) left_half
      simp_rw [List.drop_left'] at middle_part_l
      have u_len : u.length = (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length + (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)
      · omega
      rw [u_len, List.drop_append] at middle_part_l
      rw [middle_part_r, ←middle_part_l]
      sorry
    right
    use  γ.take (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)
    use (γ.drop (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)).drop o
    sorry
/-
  repeat rw [List.append_assoc u] at hyp
  rw [List.append_eq_append_iff] at hyp
  cases hyp
  · rcases hyp with ⟨u', u_eq, xj_eq⟩
    left
    repeat rw [← List.append_assoc] at xj_eq
    by_cases is_x_nil : x = []
    · exfalso
      rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at xj_eq
      have imposs := congr_arg List.length xj_eq
      rw [List.length] at imposs
      rw [List.length_append_append] at imposs
      rw [List.length_append_append] at imposs
      rw [List.length_singleton] at imposs
      clear * - imposs
      linarith
    rcases cases_1_and_2_and_3a_match_aux is_x_nil xj_eq with ⟨m, u₁, v₁, u'_eq, xm_eq, v_eq⟩
    use m, u₁, v₁
    constructor
    · rw [u_eq]
      rw [u'_eq]
      rw [← List.append_assoc]
    constructor
    · exact xm_eq
    · exact v_eq
  · rcases hyp with ⟨v', left_half, right_half⟩
    have very_middle :
      [Symbol.nonterminal ◩r₀.inputN)] =
        List.map wrapSym [Symbol.nonterminal r₀.inputN]
        · rw [List.map_singleton]
      rfl
    cases' x with x₀ xₗ
    · rw [List.map_nil, List.map_nil, List.flatten, List.append_nil] at right_half
      rw [← right_half] at left_half
      have backwards := congr_arg List.reverse left_half
      clear right_half left_half
      right
      repeat rw [List.reverse_append] at backwards
      rw [List.reverse_singleton, List.singleton_append] at backwards
      rw [← List.reverse_reverse v]
      cases' v.reverse with e z
      · exfalso
        rw [List.nil_append] at backwards
        rw [← List.map_reverse _ r₀.inputR] at backwards
        cases' r₀.inputR.reverse with d l
        · rw [List.map_nil, List.nil_append] at backwards
          rw [List.reverse_singleton (Symbol.nonterminal ◩r₀.inputN))] at backwards
          rw [List.singleton_append] at backwards
          have imposs := List.head_eq_of_cons_eq backwards
          exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
        · rw [List.map_cons, List.cons_append, List.cons_append] at backwards
          have imposs := List.head_eq_of_cons_eq backwards
          exact wrap_never_outputs_H imposs.symm
      rw [List.cons_append, List.cons_append, List.cons.inj_eq] at backwards
      cases' backwards with He backward
      rw [← He] at *
      clear He e
      have forward := congr_arg List.reverse backward
      clear backward
      repeat rw [List.reverse_append] at forward
      repeat rw [List.reverse_reverse] at forward
      rw [← List.append_assoc] at forward
      rw [List.append_eq_append_iff] at forward
      cases forward
      swap;
      · exfalso
        rcases forward with ⟨a, imposs, -⟩
        rw [List.append_assoc u] at imposs
        rw [List.append_assoc _ (List.map wrapSym r₀.inputR)] at imposs
        rw [← List.append_assoc u] at imposs
        rw [← List.append_assoc u] at imposs
        exact case_3_false_of_wbr_eq_urz imposs
      rcases forward with ⟨a', left_side, gamma_is⟩
      repeat rw [← List.append_assoc] at left_side
      rw [List.append_eq_append_iff] at left_side
      cases left_side
      · exfalso
        rcases left_side with ⟨a, imposs, -⟩
        exact case_3_false_of_wbr_eq_urz imposs
      rcases left_side with ⟨c', the_left, the_a'⟩
      rw [the_a'] at gamma_is
      clear the_a' a'
      rw [List.append_assoc] at the_left
      rw [List.append_assoc] at the_left
      rw [List.append_eq_append_iff] at the_left
      cases the_left
      · exfalso
        rcases the_left with ⟨a, -, imposs⟩
        apply false_of_true_eq_false
        convert congr_arg ((· ∈ ·) R) imposs.symm
        · rw [eq_iff_iff, true_iff_iff]
          apply List.mem_append_right
          apply List.mem_append_left
          apply List.mem_singleton_self
        · rw [eq_iff_iff, false_iff_iff]
          rw [List.mem_append]
          push_neg
          constructor
          · rw [List.mem_map]
            push_neg
            intros
            apply wrap_never_outputs_R
          · rw [List.mem_singleton]
            intro impos
            exact Sum.noConfusion (Symbol.nonterminal.inj impos)
      rcases the_left with ⟨u₀, u_eq, rule_side⟩
      rw [u_eq] at *
      clear u_eq u
      have zr_eq :
        z.reverse = (γ.map wrapSym).drop (c' ++ List.map wrapSym r₀.inputR).length :=
        by
        have gamma_suffix :=
          congr_arg (List.drop (c' ++ List.map wrapSym r₀.inputR).length) gamma_is
        rw [List.drop_left] at gamma_suffix
        exact gamma_suffix.symm
      cases' u₀ with d l
      · exfalso
        rw [List.nil_append] at rule_side
        cases' r₀.inputL with d l
        · rw [List.map_nil, List.nil_append] at rule_side
          have imposs := List.head_eq_of_cons_eq rule_side
          exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
        · rw [List.map_cons, List.cons_append] at rule_side
          have imposs := List.head_eq_of_cons_eq rule_side
          exact wrap_never_outputs_R imposs.symm
      rw [List.singleton_append, List.cons_append, List.cons.inj_eq] at rule_side
      cases' rule_side with Rd c'_eq
      rw [← Rd] at *
      clear Rd d
      rw [c'_eq] at gamma_is
      use γ.take l.length, γ.drop (c' ++ List.map wrapSym r₀.inputR).length
      constructor
      · rw [← List.singleton_append]
        have l_from_gamma := congr_arg (List.take l.length) gamma_is
        repeat rw [List.append_assoc] at l_from_gamma
        rw [List.take_left] at l_from_gamma
        rw [List.map_take]
        rw [l_from_gamma]
        rw [← List.append_assoc]
      constructor
      · rw [c'_eq]
        convert_to γ.take l.length ++ γ.drop l.length = _
        · symm
          apply List.take_append_drop
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
        rw [zr_eq] at gamma_is
        rw [c'_eq] at gamma_is
        repeat rw [List.append_assoc] at gamma_is
        have gamma_minus_initial_l := congr_arg (List.drop l.length) gamma_is
        rw [List.drop_left, very_middle, ← List.map_drop, ← List.map_drop] at gamma_minus_initial_l
        repeat rw [← List.map_append] at gamma_minus_initial_l
        rw [map_wrapSym_inj gamma_minus_initial_l]
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
        repeat rw [List.length_append]
        repeat rw [List.length_map]
        repeat rw [List.length_append]
        repeat rw [List.length_singleton]
        repeat rw [add_assoc]
      · rw [List.map_nil, List.map_nil, List.flatten, List.append_nil]
        rw [List.reverse_cons, zr_eq]
        rw [List.map_drop]
    by_cases is_v'_nil : v' = []
    · rw [is_v'_nil, List.nil_append] at right_half
      rw [is_v'_nil, List.append_nil] at left_half
      left
      use 0, [], x₀.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length
      rw [List.map_cons, List.map_cons, List.flatten] at right_half
      constructor
      · rw [List.map_nil, List.append_nil]
        rw [List.take_zero, List.map_nil, List.flatten, List.append_nil]
        exact left_half.symm
      have lengths_trivi :
        List.length
            (List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
              List.map wrapSym r₀.inputR) =
          List.length (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR)
      · rw [very_middle, ← List.map_append_append]
        apply List.length_map
      have len_rᵢ_le_len_x₀ :
        (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length ≤
          (List.map wrapSym x₀).length
      · classical
        have first_H := congr_arg (List.indexOf H) right_half
        rw [List.append_assoc _ [H], List.indexOf_append_of_not_mem map_wrap_never_contains_H] at
          first_H
        rw [List.singleton_append, List.indexOf_cons_self, add_zero] at first_H
        rw [very_middle, ← List.map_append_append,
          List.indexOf_append_of_not_mem map_wrap_never_contains_H] at first_H
        rw [List.length_map] at first_H
        exact Nat.le.intro first_H
      constructor
      · rw [List.get?]
        apply congr_arg
        rw [List.nil_append]
        convert_to
          x₀ =
            x₀.take (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length  ++
              x₀.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length
        · trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
          apply map_wrapSym_inj
          rw [List.map_append_append]
          have right_left :=
            congr_arg
              (List.take (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length)
              right_half
          rw [List.take_left' lengths_trivi] at right_left
          rw [← very_middle, right_left]
          rw [List.append_assoc _ [H]]
          rw [List.take_append_of_le_length len_rᵢ_le_len_x₀]
          rw [List.map_take]
        rw [List.take_append_drop]
      · rw [List.map_cons, List.drop_one, List.tail_cons]
        have right_right :=
          congr_arg (List.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length)
            right_half
        rw [List.drop_left' lengths_trivi] at right_right
        rw [right_right]
        rw [List.append_assoc _ [H]]
        rw [List.drop_append_of_le_length len_rᵢ_le_len_x₀]
        rw [List.map_drop]
        rw [List.append_assoc _ [H]]
        rfl
    right
    obtain ⟨z, v'_eq⟩ :
      ∃ z,
        v' =
          List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
              List.map wrapSym r₀.inputR ++
            z
            · obtain ⟨v'', without_final_H⟩ : ∃ v'', v' = v'' ++ [H] :=
        by
        rw [List.append_eq_append_iff] at left_half
        cases left_half
        · rcases left_half with ⟨a', -, matters⟩
          use []
          cases' a' with d l
          · rw [List.nil_append] at matters ⊢
            exact matters.symm
          · exfalso
            have imposs := congr_arg List.length matters
            rw [List.length_singleton, List.length_append, List.length_cons] at imposs
            have right_pos := length_ge_one_of_not_nil is_v'_nil
            clear * - imposs right_pos
            linarith
        · rcases left_half with ⟨c', -, v_c'⟩
          exact ⟨c', v_c'⟩
      rw [without_final_H] at right_half
      rw [List.append_assoc v''] at right_half
      have key_prop :
        List.length
            (List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
              List.map wrapSym r₀.inputR) ≤
          v''.length
      · classical
        have first_H := congr_arg (List.indexOf H) right_half
        rw [very_middle, ← List.map_append_append,
          List.indexOf_append_of_not_mem map_wrap_never_contains_H] at first_H
        have H_not_in_v'' : H ∉ v''
        · rw [without_final_H, ← List.append_assoc] at left_half
          intro contra
          apply false_of_true_eq_false
          convert congr_arg ((· ∈ ·) H) (List.append_right_cancel left_half).symm
          · rw [eq_iff_iff, true_iff_iff]
            exact List.mem_append_right _ contra
          · clear * -
            rw [eq_iff_iff, false_iff_iff]
            intro contr
            iterate 3
              rw [List.mem_append] at contr
              cases contr
            iterate 2
              rw [List.mem_map] at contr
              rcases contr with ⟨t, -, impos⟩
              exact Symbol.noConfusion impos
            · rw [List.mem_singleton] at contr
              exact H_neq_R contr
            · rw [List.mem_map] at contr
              rcases contr with ⟨s, -, imposs⟩
              exact wrap_never_outputs_H imposs
        rw [List.indexOf_append_of_not_mem H_not_in_v''] at first_H
        rw [List.singleton_append, List.indexOf_cons_self, add_zero] at first_H
        rw [very_middle, ← List.map_append_append]
        exact Nat.le.intro first_H
      obtain ⟨n, key_prop'⟩ := Nat.le.dest key_prop
      have right_take := congr_arg (List.take v''.length) right_half
      rw [List.take_left] at right_take
      rw [← key_prop'] at right_take
      rw [List.take_append] at right_take
      use v.take n ++ [H]
      rw [without_final_H]
      rw [← right_take]
      repeat rw [← List.append_assoc]
    rw [v'_eq] at right_half
    rw [List.append_assoc _ z] at right_half
    rw [List.append_right_inj] at right_half
    rw [v'_eq] at left_half
    obtain ⟨u₁, v₁, gamma_parts, z_eq⟩ :
      ∃ u₁,
        ∃ v₁,
          List.map wrapSym γ =
              List.map wrapSym u₁ ++
                  (List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
                    List.map wrapSym r₀.inputR) ++
                List.map wrapSym v₁ ∧
            z = List.map wrapSym v₁ ++ [H]
            · repeat rw [← List.append_assoc] at left_half
      rw [List.append_assoc _ (List.map wrapSym γ)] at left_half
      rw [List.append_assoc _ _ z] at left_half
      rw [List.append_eq_append_iff] at left_half
      cases left_half
      swap;
      · exfalso
        rcases left_half with ⟨c', imposs, -⟩
        exact case_3_false_of_wbr_eq_urz imposs
      rcases left_half with ⟨a', lhl, lhr⟩
      have lhl' := congr_arg List.reverse lhl
      repeat rw [List.reverse_append] at lhl'
      rw [List.reverse_singleton] at lhl'
      rw [← List.reverse_reverse a'] at lhr
      cases' a'.reverse with d' l'
      · exfalso
        rw [List.nil_append] at lhl'
        rw [List.singleton_append, List.reverse_singleton, List.singleton_append] at lhl'
        have imposs := List.head_eq_of_cons_eq lhl'
        exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
      rw [List.singleton_append] at lhl'
      rw [List.cons_append] at lhl'
      rw [List.cons.inj_eq] at lhl'
      cases' lhl' with eq_d' lhl''
      rw [← eq_d'] at lhr
      clear eq_d' d'
      rw [← List.append_assoc l'] at lhl''
      rw [List.append_eq_append_iff] at lhl''
      cases lhl''
      swap;
      · exfalso
        rcases lhl'' with ⟨c'', imposs, -⟩
        rw [List.reverse_singleton] at imposs
        apply false_of_true_eq_false
        convert congr_arg ((· ∈ ·) R) imposs.symm
        · rw [eq_iff_iff, true_iff_iff]
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_singleton_self
        · rw [eq_iff_iff, false_iff_iff]
          rw [List.mem_reverse']
          apply map_wrap_never_contains_R
      rcases lhl'' with ⟨b', lhlr', lhll'⟩
      rw [List.reverse_singleton] at lhlr'
      have lhlr := congr_arg List.reverse lhlr'
      rw [List.reverse_append, List.reverse_append, List.reverse_reverse] at lhlr
      rw [List.reverse_singleton, List.singleton_append] at lhlr
      rw [← List.reverse_reverse b'] at lhll'
      cases' b'.reverse with d'' l''
      · exfalso
        rw [List.nil_append] at lhlr
        cases' r₀.inputL with d l
        · rw [List.map_nil] at lhlr
          exact List.noConfusion lhlr
        rw [List.map_cons] at lhlr
        have imposs := List.head_eq_of_cons_eq lhlr
        exact wrap_never_outputs_R imposs.symm
      rw [List.cons_append] at lhlr
      rw [List.cons.inj_eq] at lhlr
      cases' lhlr with eq_d'' lve
      rw [← eq_d''] at lhll'
      clear eq_d'' d''
      have lhll := congr_arg List.reverse lhll'
      rw [List.reverse_reverse, List.reverse_append, List.reverse_reverse, List.reverse_append,
        List.reverse_reverse, List.reverse_reverse] at lhll
      rw [lhll] at *
      clear lhll u
      rw [List.reverse_cons] at lhr
      rw [lve] at lhr
      use γ.take l''.length
      use
        List.drop
          (l'' ++ List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
              List.map wrapSym r₀.inputR).length
          γ
      have z_expr :
        z =
          List.map wrapSym
              (List.drop
                (l'' ++ List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
                    List.map wrapSym r₀.inputR).length
                γ) ++
            [H] :=
        by
        have lhdr :=
          congr_arg
            (List.drop
              (l'' ++ List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
                  List.map wrapSym r₀.inputR).length)
            lhr
        rw [List.drop_append_of_le_length] at lhdr
        · rw [List.map_drop, lhdr, ← List.append_assoc, List.drop_left]
        have lhr' := congr_arg List.reverse lhr
        repeat rw [List.reverse_append] at lhr'
        rw [List.reverse_singleton] at lhr'
        cases' z.reverse with d l
        · exfalso
          rw [List.nil_append, List.singleton_append] at lhr'
          rw [← List.map_reverse _ r₀.inputR] at lhr'
          cases' r₀.inputR.reverse with dᵣ lᵣ
          · rw [List.map_nil, List.nil_append, List.reverse_singleton, List.singleton_append] at
              lhr'
            have imposs := List.head_eq_of_cons_eq lhr'
            exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
          · rw [List.map_cons, List.cons_append] at lhr'
            have imposs := List.head_eq_of_cons_eq lhr'
            exact wrap_never_outputs_H imposs.symm
        repeat rw [List.length_append]
        have contra_len := congr_arg List.length lhr'
        repeat rw [List.length_append] at contra_len
        repeat rw [List.length_reverse] at contra_len
        repeat rw [List.length_singleton] at contra_len
        rw [List.length_cons] at contra_len
        rw [List.length_singleton]
        clear * - contra_len
        linarith
      constructor
      swap; · exact z_expr
      rw [z_expr] at lhr
      have gamma_expr :
        List.map wrapSym γ =
          l'' ++ List.map wrapSym r₀.inputL ++ [Symbol.nonterminal ◩r₀.inputN)] ++
            (List.map wrapSym r₀.inputR ++
              List.map wrapSym
                (List.drop
                  (l'' ++ List.map wrapSym r₀.inputL ++
                        [Symbol.nonterminal ◩r₀.inputN)] ++
                      List.map wrapSym r₀.inputR).length
                  γ)) :=
        by
        repeat rw [← List.append_assoc] at lhr
        repeat rw [← List.append_assoc]
        exact List.append_right_cancel lhr
      rw [gamma_expr]
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
      have almost := congr_arg (List.take l''.length) gamma_expr.symm
      repeat rw [List.append_assoc] at almost
      rw [List.take_left] at almost
      rw [List.map_take]
      exact almost
    use u₁, v₁
    constructor; swap; constructor
    · apply map_wrapSym_inj
      rwa [very_middle, ← List.map_append_append, ← List.map_append_append, ← List.append_assoc, ←
        List.append_assoc] at gamma_parts
    · rwa [z_eq] at right_half
    rw [gamma_parts] at left_half
    rw [List.append_assoc (List.map wrapSym u₁)] at left_half
    rw [← List.append_assoc _ (List.map wrapSym u₁)] at left_half
    rw [List.append_assoc _ _ [H]] at left_half
    have left_left := congr_arg (List.take u.length) left_half
    rw [List.take_left] at left_left
    rw [List.take_left'] at left_left
    · exact left_left.symm
    have lh_len := congr_arg List.length left_half
    repeat rw [List.length_append] at lh_len
    repeat rw [List.length_singleton] at lh_len
    have cut_off_end : z.length = (List.map wrapSym v₁).length + 1
    · simpa using congr_arg List.length z_eq
    rw [cut_off_end] at lh_len
    repeat rw [List.length_append]
    rw [List.length_singleton]
    repeat rw [add_assoc] at lh_len
    iterate 3 rw [← add_assoc] at lh_len
    rwa [add_left_inj] at lh_len
-/
private lemma star_case_3 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp :
      ∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
        (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
        g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
        α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
            ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
         ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α' = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hyp with ⟨w, β, γ, x, valid_w, valid_middle, valid_x, cat⟩
  have no_Z_in_alpha : Z ∉ α
  · intro contr
    rw [cat] at contr
    clear * - contr
    simp only [List.mem_append] at contr
    rcases contr with ((((hZw | hZβ) | hZR) | hZγ) | hZH) | hZx
    · rw [List.mem_map] at hZw
      obtain ⟨s, -, imposs⟩ := hZw
      exact Symbol.noConfusion imposs
    · rw [List.mem_map] at hZβ
      obtain ⟨s, -, imposs⟩ := hZβ
      exact Symbol.noConfusion imposs
    · rw [List.mem_singleton] at hZR
      exact Z_neq_R hZR
    · rw [List.mem_map] at hZγ
      obtain ⟨s, -, imposs⟩ := hZγ
      exact wrap_never_outputs_Z imposs
    · rw [List.mem_singleton] at hZH
      exact Z_neq_H hZH
    · exact Z_not_in_join_mpHmmw hZx
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    exfalso
    apply no_Z_in_alpha
    rw [bef]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    rewrite [List.mem_singleton]
    rfl
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      apply no_Z_in_alpha
      rw [bef]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      rewrite [List.mem_singleton]
      rfl
    | tail _ rin =>
      cases rin with
      | head =>
        dsimp only at bef aft
        rw [List.append_nil, cat] at bef
        have gamma_nil_here := case_3_gamma_nil bef
        cases x with
        | nil =>
          right; right; left
          rw [gamma_nil_here, List.map_nil, List.append_nil] at bef
          rw [List.map_nil, List.map_nil, List.flatten, List.append_nil] at bef
          have v_nil := case_3_v_nil bef
          rw [v_nil, List.append_nil] at bef aft
          use w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
          rw [List.append_cancel_right_eq, R, List.append_cancel_right_eq] at bef
          rewrite [aft, ←bef, List.map_append, List.map_map, List.map_map]
          rfl
        | cons x₀ L =>
          left
          use w ++ [β], [], x₀, L
          constructor
          · intro wᵢ wiin
            rw [List.mem_append] at wiin
            exact wiin.casesOn (valid_w wᵢ) (by aesop)
          constructor
          · rw [gamma_nil_here] at valid_middle
            apply valid_x
            rw [List.map_nil, List.nil_append]
            exact List.mem_cons_self x₀ L
          constructor
          · intro xᵢ xiin
            exact valid_x xᵢ (List.mem_cons_of_mem x₀ xiin)
          rw [aft]
          have u_eq : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map (@Symbol.terminal T (nn g.nt))
          · exact case_3_u_eq_left_side bef
          have v_eq : v = (((x₀::L).map (List.map wrapSym)).map (· ++ [H])).flatten
          · rw [u_eq, gamma_nil_here, List.map_nil, List.append_nil] at bef
            exact List.append_cancel_left bef.symm
          rw [u_eq, v_eq]
          simp
      | tail _ rin' =>
        cases rin' with
        | head =>
          dsimp only at bef aft
          rw [List.append_nil] at bef aft
          rw [cat] at bef
          have gamma_nil_here := case_3_gamma_nil bef
          rw [← List.reverse_reverse x] at *
          cases' hx : x.reverse with xₘ L
          · right; left
            rw [gamma_nil_here, List.map_nil, List.append_nil] at bef
            rw [hx, List.reverse_nil, List.map_nil, List.map_nil, List.flatten, List.append_nil] at bef
            have v_nil := case_3_v_nil bef
            rw [v_nil, List.append_nil] at bef aft
            use List.flatten w ++ β
            constructor
            · use w ++ [β]
              constructor
              · rw [List.flatten_append]
                rw [List.flatten_singleton]
              · intro y y_in
                rw [List.mem_append] at y_in
                aesop
            · rw [List.append_cancel_right_eq, R, List.append_cancel_right_eq] at bef
              rw [aft, ←bef, List.map_append]
          · right; right; right
            rw [hx, List.reverse_cons] at bef
            rw [aft]
            have Z_ni_wb : Z ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal
            · apply case_3_ni_wb
            have R_ni_wb : R ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal
            · apply case_3_ni_wb
            have u_eq : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal :=
              case_3_u_eq_left_side bef
            have v_eq : v = (((L.reverse ++ [xₘ]).map (List.map wrapSym)).map (· ++ [H])).flatten
            · rw [u_eq, gamma_nil_here, List.map_nil, List.append_nil] at bef
              exact List.append_cancel_left bef.symm
            rw [u_eq, v_eq]
            constructor
            · use w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++
                    ((L.reverse.map (List.map wrapSym)).map (· ++ [H])).flatten ++
                    xₘ.map wrapSym
              rw [List.map_append, List.map_append, List.flatten_append, List.map_singleton,
                  List.map_singleton, List.flatten_singleton, ←List.append_assoc, ←List.append_assoc]
            constructor
            · rw [List.mem_append]
              exact (·.casesOn Z_ni_wb Z_not_in_join_mpHmmw)
            · rw [List.mem_append]
              exact (·.casesOn R_ni_wb R_not_in_join_mpHmmw)
        | tail _ rin =>
          have rin' : r ∈ rulesThatScanTerminals g ∨ r ∈ g.rules.map wrapGr
          · rwa [or_comm, ←List.mem_append]
          clear rin
          cases rin' with
          | inl hrg =>
            left
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, r_is⟩
            rw [← r_is] at bef aft
            dsimp only at bef aft
            rw [List.append_nil, cat] at bef
            have u_matches : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal :=
              case_3_u_eq_left_side bef
            have tv_matches : [Symbol.terminal t] ++ v = γ.map wrapSym ++ [H] ++ (List.map (· ++ [H]) (x.map (List.map wrapSym))).flatten
            · rw [u_matches] at bef
              repeat rw [List.append_assoc] at bef
              rw [List.append_cancel_left_eq, List.append_cancel_left_eq, R, List.append_cancel_left_eq, ←List.append_assoc] at bef
              exact bef.symm
            cases' γ with a δ
            · exfalso
              rw [List.map_nil, List.nil_append, List.singleton_append, List.singleton_append] at tv_matches
              have t_matches := List.head_eq_of_cons_eq tv_matches
              exact Symbol.noConfusion t_matches
            rw [List.singleton_append, List.map_cons, List.cons_append, List.cons_append] at tv_matches
            use w, β ++ [t], δ, x, valid_w
            constructor
            · have t_matches' := List.head_eq_of_cons_eq tv_matches
              cases a <;> unfold wrapSym at t_matches'
              · have t_eq_a := Symbol.terminal.inj t_matches'
                rw [t_eq_a, List.map_append, List.map_singleton, List.append_assoc, List.singleton_append]
                exact valid_middle
              · exfalso
                exact Symbol.noConfusion t_matches'
            constructor
            · exact valid_x
            rw [aft, u_matches, List.map_append, List.map_singleton]
            have v_matches := List.tail_eq_of_cons_eq tv_matches
            simp [v_matches, List.append_assoc]
          | inr hrg =>
            left
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, orig_in, wrap_orig⟩
            unfold wrapGr at wrap_orig
            rw [cat, ←wrap_orig] at bef
            cases case_3_match_rule bef with
            | inl huv =>
              rcases huv with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
              clear bef
              rw [u_eq, v_eq] at aft
              use w, β, γ, x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ x.drop m.succ
              constructor
              · exact valid_w
              constructor
              · exact valid_middle
              constructor
              · intro xᵢ xiin
                rw [List.mem_append_append] at xiin
                cases xiin with
                | inl =>
                  apply valid_x
                  apply List.mem_of_mem_take
                  assumption
                | inr hxᵢ =>
                  cases hxᵢ with
                  | inl xiin =>
                    rw [List.mem_singleton] at xiin
                    rw [xiin]
                    have last_step :
                      g.Transforms
                        (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                        (u₁ ++ r₀.output ++ v₁)
                    · use r₀, orig_in, u₁, v₁
                    apply gr_deri_of_deri_tran _ last_step
                    apply valid_x (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                    exact List.mem_of_getElem? xm_eq
                  | inr =>
                    apply valid_x
                    apply List.mem_of_mem_drop
                    assumption
              · rw [aft]
                simp [←wrap_orig]
            | inr huv =>
              rcases huv with ⟨u₁, v₁, u_eq, γ_eq, v_eq⟩
              clear bef
              rw [u_eq, v_eq] at aft
              use w, β, u₁ ++ r₀.output ++ v₁, x, valid_w
              constructor
              · apply gr_deri_of_deri_tran valid_middle
                rw [γ_eq]
                use r₀, orig_in, β.map Symbol.terminal ++ u₁, v₁
                constructor
                repeat rw [←List.append_assoc]
              constructor
              · exact valid_x
              · rw [aft]
                simp [←wrap_orig]

private lemma star_case_4 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : ∃ u : List T, u ∈ KStar.kstar g.language ∧ α = u.map Symbol.terminal) :
  False :=
by
  rcases hyp with ⟨w, -, alpha_of_w⟩
  rw [alpha_of_w] at orig
  rcases orig with ⟨r, -, _, _, bef, -⟩
  simpa using congr_arg (Symbol.nonterminal r.inputN ∈ ·) bef

private lemma star_case_5 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : ∃ σ : List (Symbol T g.nt), α = σ.map wrapSym ++ [R]) :
  ∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R] :=
by
  rcases hyp with ⟨w, ends_with_R⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  rw [ends_with_R] at bef
  clear ends_with_R
  cases rin with
  | head =>
    exfalso
    simp only [List.append_nil] at bef
    have imposs := congr_arg (fun l => Z ∈ l) bef
    simp only [List.mem_append] at imposs
    rw [List.mem_singleton] at imposs
    rw [List.mem_singleton] at imposs
    apply false_of_true_eq_false
    convert imposs.symm
    · simp [Z]
    · rw [false_iff]
      push_neg
      constructor
      · apply map_wrap_never_contains_Z
      · exact Z_neq_R
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      simp only [List.append_nil] at bef
      have imposs := congr_arg (Z ∈ ·) bef
      simp only [List.mem_append] at imposs
      rw [List.mem_singleton] at imposs
      rw [List.mem_singleton] at imposs
      apply false_of_true_eq_false
      convert imposs.symm
      · simp [Z]
      · rw [false_iff]
        push_neg
        constructor
        · apply map_wrap_never_contains_Z
        · exact Z_neq_R
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        dsimp only at bef
        rw [List.append_nil] at bef
        have rev := congr_arg List.reverse bef
        repeat rw [List.reverse_append] at rev
        repeat rw [List.reverse_singleton] at rev
        rw [List.singleton_append] at rev
        cases hv : v.reverse with
        | nil =>
          rw [hv, List.nil_append, List.singleton_append] at rev
          have tails := List.tail_eq_of_cons_eq rev
          rw [← List.map_reverse] at tails
          cases hw : w.reverse with
          | nil =>
            rw [hw, List.map_nil] at tails
            have imposs := congr_arg List.length tails
            rw [List.length, List.length_append, List.length_singleton] at imposs
            clear * - imposs
            linarith
          | cons d' l' =>
            rw [hw, List.map_cons, List.singleton_append] at tails
            have heads := List.head_eq_of_cons_eq tails
            exact wrap_never_outputs_R heads
        | cons d l =>
          rw [hv] at rev
          have tails := List.tail_eq_of_cons_eq rev
          have H_in_tails := congr_arg (fun l => H ∈ l) tails
          dsimp only at H_in_tails
          rw [List.mem_reverse] at H_in_tails
          apply false_of_true_eq_false
          convert H_in_tails.symm
          · rw [true_iff]
            apply List.mem_append_right
            apply List.mem_append_left
            apply List.mem_singleton_self
          · rw [false_iff]
            intro hyp_H_in
            exact map_wrap_never_contains_H hyp_H_in
      | tail _ rin' =>
        cases rin' with
        | head =>
          exfalso
          dsimp only at bef
          rw [List.append_nil] at bef
          have rev := congr_arg List.reverse bef
          repeat rw [List.reverse_append] at rev
          repeat rw [List.reverse_singleton] at rev
          rw [List.singleton_append] at rev
          cases hv : v.reverse with
          | nil =>
            rw [hv, List.nil_append, List.singleton_append] at rev
            have tails := List.tail_eq_of_cons_eq rev
            rw [← List.map_reverse] at tails
            cases hw : w.reverse with
            | nil =>
              rw [hw, List.map_nil] at tails
              have imposs := congr_arg List.length tails
              rw [List.length, List.length_append, List.length_singleton] at imposs
              clear * - imposs
              linarith
            | cons d' l' =>
              rw [hw, List.map_cons, List.singleton_append] at tails
              have heads := List.head_eq_of_cons_eq tails
              exact wrap_never_outputs_R heads
          | cons d l =>
            rw [hv] at rev
            have tails := List.tail_eq_of_cons_eq rev
            have H_in_tails := congr_arg (fun l => H ∈ l) tails
            dsimp only at H_in_tails
            rw [List.mem_reverse] at H_in_tails
            apply false_of_true_eq_false
            convert H_in_tails.symm
            · rw [true_iff]
              apply List.mem_append_right
              apply List.mem_append_left
              apply List.mem_singleton_self
            · rw [false_iff]
              intro hyp_H_in
              exact map_wrap_never_contains_H hyp_H_in
        | tail _ rin =>
          change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
          rw [List.mem_append] at rin
          cases rin with
          | inl hrg =>
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, -, r_of_r₀⟩
            rw [List.append_eq_append_iff] at bef
            cases bef with
            | inl has =>
              rcases has with ⟨x, ur_eq, singleR⟩
              by_cases is_x_nil : x = []
              · have v_is_R : v = [R]
                · rw [is_x_nil, List.nil_append] at singleR
                  exact singleR.symm
                rw [v_is_R] at aft
                rw [is_x_nil, List.append_nil] at ur_eq
                have u_from_w : u = (w.map wrapSym).take u.length
                · repeat rw [List.append_assoc] at ur_eq
                  have tak := congr_arg (List.take u.length) ur_eq
                  rw [List.take_left] at tak
                  exact tak
                rw [← List.map_take] at u_from_w
                rw [u_from_w] at aft
                rw [← r_of_r₀] at aft
                dsimp only [wrapGr] at aft
                use w.take u.length ++ r₀.output
                rw [List.map_append]
                exact aft
              · exfalso
                have x_is_R : x = [R]
                · by_cases is_v_nil : v = []
                  · rw [is_v_nil, List.append_nil] at singleR
                    exact singleR.symm
                  · exfalso
                    have imposs := congr_arg List.length singleR
                    rw [List.length_singleton] at imposs
                    rw [List.length_append] at imposs
                    have xl_ge_one := length_ge_one_of_not_nil is_x_nil
                    have vl_ge_one := length_ge_one_of_not_nil is_v_nil
                    clear * - imposs xl_ge_one vl_ge_one
                    linarith
                rw [x_is_R] at ur_eq
                have ru_eq := congr_arg List.reverse ur_eq
                repeat rw [List.reverse_append] at ru_eq
                repeat
                  rw [List.reverse_singleton] at ru_eq
                  rw [List.singleton_append] at ru_eq
                rw [← r_of_r₀] at ru_eq
                dsimp only [wrapGr, R] at ru_eq
                rw [← List.map_reverse] at ru_eq
                cases hr₀ : r₀.inputR.reverse with
                | nil =>
                  rw [hr₀, List.map_nil, List.nil_append] at ru_eq
                  have imposs := List.head_eq_of_cons_eq ru_eq
                  exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
                | cons d l =>
                  rw [hr₀] at ru_eq
                  have imposs := List.head_eq_of_cons_eq ru_eq
                  cases d <;> unfold wrapSym at imposs
                  · exact Symbol.noConfusion imposs
                  · exact Sum.noConfusion (Symbol.nonterminal.inj imposs)
            | inr hbs =>
              rcases hbs with ⟨y, w_eq, v_eq⟩
              have u_from_w : u = (w.map wrapSym).take u.length
              · repeat rw [List.append_assoc] at w_eq
                have tak := congr_arg (List.take u.length) w_eq
                rw [List.take_left] at tak
                exact tak.symm
              have y_from_w : y = (w.map wrapSym).drop (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length
              · have drp := congr_arg (List.drop (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length) w_eq
                rw [List.drop_left] at drp
                exact drp.symm
              rw [u_from_w] at aft
              rw [y_from_w] at v_eq
              rw [v_eq] at aft
              use w.take u.length ++ r₀.output ++ w.drop (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length
              rw [aft, ←r_of_r₀]
              simp [wrapGr]
          | inr hrg =>
            exfalso
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, eq_r⟩
            rw [← eq_r] at bef
            clear eq_r
            dsimp only at bef
            rw [List.append_nil] at bef
            have rev := congr_arg List.reverse bef
            repeat rw [List.reverse_append] at rev
            repeat rw [List.reverse_singleton] at rev
            rw [List.singleton_append] at rev
            cases hv : v.reverse with
            | nil =>
              rw [hv, List.nil_append, List.singleton_append] at rev
              have tails := List.tail_eq_of_cons_eq rev
              rw [← List.map_reverse] at tails
              cases hw : w.reverse with
              | nil =>
                rw [hw, List.map_nil] at tails
                have imposs := congr_arg List.length tails
                rw [List.length, List.length_append, List.length_singleton] at imposs
                clear * - imposs
                linarith
              | cons d' l' =>
                rw [hw, List.map_cons, List.singleton_append] at tails
                have heads := List.head_eq_of_cons_eq tails
                exact wrap_never_outputs_R heads
            | cons d l =>
              rw [hv] at rev
              have tails := List.tail_eq_of_cons_eq rev
              have R_in_tails := congr_arg (R ∈ ·) tails
              dsimp only at R_in_tails
              rw [List.mem_reverse] at R_in_tails
              apply false_of_true_eq_false
              convert R_in_tails.symm
              · rw [true_iff]
                apply List.mem_append_right
                apply List.mem_append_right
                apply List.mem_append_left
                apply List.mem_singleton_self
              · rw [false_iff]
                intro hyp_R_in
                exact map_wrap_never_contains_R hyp_R_in

private lemma star_case_6 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hyp with ⟨⟨w, ends_with_H⟩, no_Z, no_R⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    exfalso
    simp only [List.append_nil] at bef
    rw [bef] at no_Z
    apply no_Z
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_singleton_self
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      simp only [List.append_nil] at bef
      rw [bef] at no_Z
      apply no_Z
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_singleton_self
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        dsimp only at bef
        rw [List.append_nil] at bef
        rw [bef] at no_R
        apply no_R
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_singleton_self
      | tail _ rin' =>
        cases rin' with
        | head =>
          exfalso
          dsimp only at bef
          rw [List.append_nil] at bef
          rw [bef] at no_R
          apply no_R
          apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_singleton_self
        | tail _ rin =>
          change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
          rw [List.mem_append] at rin
          cases rin with
          | inl hrg =>
            rw [ends_with_H] at bef
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, -, r_of_r₀⟩
            constructor
            · use u ++ r.output ++ v.take (v.length - 1)
              rw [aft]
              have vlnn : v.length ≥ 1
              · by_contra contra
                have v_nil := zero_of_not_ge_one contra
                rw [List.length_eq_zero_iff] at v_nil
                rw [v_nil] at bef
                rw [← r_of_r₀] at bef
                rw [List.append_nil] at bef
                unfold wrapGr at bef
                have rev := congr_arg List.reverse bef
                clear * - rev
                repeat rw [List.reverse_append] at rev
                rw [← List.map_reverse _ r₀.inputR] at rev
                rw [List.reverse_singleton] at rev
                cases hr₀ : r₀.inputR.reverse with
                | nil =>
                  have H_eq_N : H = Symbol.nonterminal ◩r₀.inputN
                  · rw [hr₀] at rev
                    simp at rev
                    exact rev.left
                  unfold H at H_eq_N
                  have inr_eq_inl := Symbol.nonterminal.inj H_eq_N
                  exact Sum.noConfusion inr_eq_inl
                | cons d l =>
                  rw [hr₀, List.map_cons] at rev
                  have H_is : H = wrapSym d
                  · simp at rev
                    exact rev.left
                  unfold H at H_is
                  cases d <;> unfold wrapSym at H_is
                  · exact Symbol.noConfusion H_is
                  · simp at H_is
              have bef_rev := congr_arg List.reverse bef
              repeat rw [List.reverse_append] at bef_rev
              have bef_rev_tak := congr_arg (List.take 1) bef_rev
              rw [List.take_left' (by rfl)] at bef_rev_tak
              rw [List.take_append_of_le_length (by rwa [List.length_reverse])] at bef_rev_tak
              convert_to u ++ r.output ++ v = u ++ r.output ++ (v.take (v.length - 1) ++ [H])
              · simp
              conv_lhs => rw [←v.take_append_drop (v.length - 1)]
              congr
              have h1 : 1 = v.length - (v.length - 1)
              · omega
              rw [h1, ←List.reverse_drop] at bef_rev_tak
              apply List.reverse_injective
              exact bef_rev_tak.symm
            · constructor
              · rw [aft]
                intro contra
                rw [List.mem_append, List.mem_append] at contra
                cases contra with
                | inl hZ =>
                  cases hZ with
                  | inl hZu =>
                    apply no_Z
                    rw [ends_with_H]
                    rw [bef]
                    repeat rw [List.append_assoc]
                    rw [List.mem_append]
                    left
                    exact hZu
                  | inr hZr =>
                    rw [←r_of_r₀] at hZr
                    unfold wrapGr at hZr
                    rw [List.mem_map] at hZr
                    rcases hZr with ⟨s, -, imposs⟩
                    cases s
                    · unfold wrapSym at imposs
                      exact Symbol.noConfusion imposs
                    · unfold wrapSym at imposs
                      unfold Z at imposs
                      simp at imposs
                | inr hZv =>
                  apply no_Z
                  rw [ends_with_H, bef, List.mem_append]
                  right
                  exact hZv
              · rw [aft]
                intro contra
                rw [List.mem_append] at contra
                rw [List.mem_append] at contra
                cases contra with
                | inl hR =>
                  cases hR with
                  | inl hRu =>
                    apply no_R
                    rw [ends_with_H]
                    rw [bef]
                    repeat rw [List.append_assoc]
                    rw [List.mem_append]
                    left
                    exact hRu
                  | inr hRr =>
                    rw [←r_of_r₀] at hRr
                    unfold wrapGr at hRr
                    rw [List.mem_map] at hRr
                    rcases hRr with ⟨s, -, imposs⟩
                    cases s
                    · unfold wrapSym at imposs
                      exact Symbol.noConfusion imposs
                    · unfold wrapSym R at imposs
                      simp at imposs
                | inr hRv =>
                  apply no_R
                  rw [ends_with_H]
                  rw [bef]
                  rw [List.mem_append]
                  right
                  exact hRv
          | inr hrg =>
            exfalso
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, eq_r⟩
            rw [←eq_r] at bef
            dsimp only at bef
            rw [List.append_nil] at bef
            rw [bef] at no_R
            apply no_R
            apply List.mem_append_left
            apply List.mem_append_left
            apply List.mem_append_right
            apply List.mem_singleton_self

private lemma star_induction {g : Grammar T} {α : List (ns T g.nt)}
    (ass : g.star.Derives [Z] α) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧ α = [Z] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α :=
by
  induction' ass with a b trash orig ih
  · left
    use []
    constructor
    · intro y imposs
      exfalso
      exact List.not_mem_nil y imposs
    · rfl
  cases' ih with ih ih
  · rw [← or_assoc]
    left
    exact star_case_1 orig ih
  cases' ih with ih ih
  · right
    exact star_case_2 orig ih
  cases' ih with ih ih
  · right; right
    exact star_case_3 orig ih
  cases' ih with ih ih
  · exfalso
    exact star_case_4 orig ih
  cases' ih with ih ih
  · right; right; right; right; left
    exact star_case_5 orig ih
  · right; right; right; right; right
    exact star_case_6 orig ih

end hard_direction


/-- The class of grammar-generated languages is closed under the Kleene star. -/
theorem GG_of_star_GG (L : Language T) : L.IsGG → (KStar.kstar L).IsGG := by
  intro ⟨g, hg⟩
  use g.star
  apply Set.eq_of_subset_of_subset
  · -- prove `L.star ⊇` here
    intro w hyp
    have result := star_induction hyp
    clear hyp
    cases' result with result result
    · exfalso
      rcases result with ⟨x, -, contr⟩
      cases' w with d l
      · tauto
      rw [List.map_cons] at contr
      have terminal_eq_Z : Symbol.terminal d = Z := List.head_eq_of_cons_eq contr
      exact Symbol.noConfusion terminal_eq_Z
    cases' result with result result
    · exfalso
      rcases result with ⟨x, -, contr⟩
      cases' w with d l
      · tauto
      rw [List.map_cons] at contr
      have terminal_eq_R : Symbol.terminal d = R := List.head_eq_of_cons_eq contr
      exact Symbol.noConfusion terminal_eq_R
    cases' result with result result
    · exfalso
      rcases result with ⟨α, β, γ, x, -, -, -, contr⟩
      have output_contains_R : R ∈ w.map (@Symbol.terminal T g.star.nt)
      · rw [contr]
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_cons_self
      rw [List.mem_map] at output_contains_R
      rcases output_contains_R with ⟨t, -, terminal_eq_R⟩
      exact Symbol.noConfusion terminal_eq_R
    cases' result with result result
    · rcases result with ⟨u, win, map_eq_map⟩
      have w_eq_u : w = u :=
        by
        have st_inj : Function.Injective (@Symbol.terminal T g.star.nt)
        · apply Symbol.terminal.inj
        rw [← List.map_injective_iff] at st_inj
        exact st_inj map_eq_map
      rw [w_eq_u, ← hg]
      exact win
    cases' result with result result
    · exfalso
      cases' result with σ contr
      have last_symbols := congr_arg (·[0]?) (congr_arg List.reverse contr)
      rw [← List.map_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append] at last_symbols
      cases hw0 : w.reverse[0]?
      · simp_all
      · clear * - last_symbols
        unfold R at last_symbols
        cases hw : w.reverse <;> aesop
    · exfalso
      rcases result with ⟨⟨ω, contr⟩, -⟩
      have last_symbols := congr_arg (·[0]?) (congr_arg List.reverse contr)
      rw [← List.map_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append] at last_symbols
      cases hw0 : w.reverse[0]?
      · simp_all
      · clear * - last_symbols
        unfold H at last_symbols
        cases hw : w.reverse <;> aesop
  · -- prove `L.star ⊆` here
    intro p ass
    unfold KStar.kstar at ass
    rcases ass with ⟨w, w_join, parts_in_L⟩
    let v := w.reverse
    have v_reverse : v.reverse = w
    · apply List.reverse_reverse
    rw [← v_reverse] at w_join parts_in_L
    rw [w_join]
    clear w_join p
    rw [← hg] at parts_in_L
    cases' short_induction parts_in_L with derived terminated
    apply gr_deri_of_deri_deri derived
    apply gr_deri_of_tran_deri
    · use g.star.rules.get ⟨1, Nat.one_lt_succ_succ _⟩
      constructor
      · apply List.get_mem
      use [], ((v.reverse.map (List.map Symbol.terminal)).map (· ++ [H])).flatten
      constructor
      · rw [List.reverse_reverse]
        rfl
      · rfl
    rw [List.nil_append, v_reverse]
    have final_step :
      g.star.Transforms
        (w.flatten.map Symbol.terminal ++ [R, H])
        (w.flatten.map Symbol.terminal)
    · use g.star.rules.get ⟨3, List.isSome_getElem?.→ rfl⟩
      constructor
      · apply List.get_mem
      use w.flatten.map Symbol.terminal, []
      constructor
      · aesop
      · have out_nil : (g.star.rules.get ⟨3, List.isSome_getElem?.→ rfl⟩).output = []
        · rfl
        rw [List.append_nil, out_nil, List.append_nil]
    apply gr_deri_of_deri_tran _ final_step
    convert_to
      g.star.Derives
        ([R] ++ ([H] ++ ((w.map (List.map Symbol.terminal)).map (· ++ [H])).flatten))
        (w.flatten.map Symbol.terminal ++ [R, H])
    have rebracket :
      [H] ++ ((w.map (List.map Symbol.terminal)).map (· ++ [H])).flatten =
             ((w.map (List.map Symbol.terminal)).map ([H] ++ ·)).flatten ++ [H]
    · apply List.append_flatten_map_append
    rw [rebracket]
    apply terminal_scan_aux
    aesop

#print axioms GG_of_star_GG
