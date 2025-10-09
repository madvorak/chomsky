import Chomsky.Classes.ContextFree.Basics.Lifting

variable {T : Type}

/-- Grammar for a union of two context-free languages. -/
def CFG.union (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (Option (g₁.nt ⊕ g₂.nt)) none (
    ⟨none, [Symbol.nonterminal (some ◩g₁.initial)]⟩ :: (
    ⟨none, [Symbol.nonterminal (some ◪g₂.initial)]⟩ :: (
    List.map (liftRule (Option.some ∘ Sum.inl)) g₁.rules ++
    List.map (liftRule (Option.some ∘ Sum.inr)) g₂.rules)))

private lemma both_empty {u v : List T} {a b : T} (ha : [a] = u ++ [b] ++ v) :
    u = [] ∧ v = [] := by
  cases u <;> cases v <;> simp at ha; trivial

variable {g₁ g₂ : CFG T}

private def oN₁_of_N : (CFG.union g₁ g₂).nt → Option g₁.nt
  | none => none
  | some ◩n => some n
  | some ◪_ => none

private def oN₂_of_N : (CFG.union g₁ g₂).nt → Option g₂.nt
  | none => none
  | some ◩_ => none
  | some ◪n => some n

private def g₁g : LiftedCFG T :=
  ⟨g₁, CFG.union g₁ g₂, some ∘ Sum.inl, oN₁_of_N,
    (fun x y hxy => Sum.inl_injective (Option.some_injective _ hxy)),
    (by
      intro x y hxy
      cases x with
      | none => right; rfl;
      | some x₀ =>
        cases y with
        | none => right; exact hxy
        | some y₀ =>
          cases x₀ with
          | inl =>
            cases y₀ with
            | inl =>
              simp only [oN₁_of_N, Option.some.injEq] at hxy
              left
              rw [hxy]
            | inr =>
              exfalso
              simp [oN₁_of_N] at hxy
          | inr =>
            cases y₀ with
            | inl =>
              exfalso
              simp [oN₁_of_N] at hxy
            | inr =>
              right
              rfl),
    (fun _ => rfl),
    (by
      intro r hr
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      rw [List.mem_map]
      exact ⟨r, hr, rfl⟩),
    (by
      intro r ⟨hr, ⟨n₀, imposs⟩⟩
      cases hr with
      | head =>
        exfalso
        exact Option.noConfusion imposs
      | tail _ hr =>
        cases hr with
        | head =>
          exfalso
          exact Option.noConfusion imposs
        | tail _ hr =>
          change r ∈ List.map _ g₁.rules ++ List.map _ g₂.rules at hr
          rw [List.mem_append] at hr
          cases hr with
          | inl hr =>
            rw [List.mem_map] at hr
            exact hr
          | inr hr =>
            exfalso
            rw [List.mem_map] at hr
            rcases hr with ⟨_, -, rfl⟩
            simp only [liftRule, Function.comp_apply] at imposs
            rw [Option.some_inj] at imposs
            exact Sum.noConfusion imposs)⟩

private def g₂g : LiftedCFG T :=
  ⟨g₂, CFG.union g₁ g₂, some ∘ Sum.inr, oN₂_of_N,
    (fun x y hxy => Sum.inr_injective (Option.some_injective _ hxy)),
    (by
      intro x y hxy
      cases x with
      | none => right; rfl;
      | some x₀ =>
        cases y with
        | none => right; exact hxy
        | some y₀ =>
          cases x₀ with
          | inl =>
            cases y₀ with
            | inl =>
              right
              rfl
            | inr =>
              exfalso
              simp [oN₂_of_N] at hxy
          | inr =>
            cases y₀ with
            | inl =>
              exfalso
              simp [oN₂_of_N] at hxy
            | inr =>
              simp only [oN₂_of_N, Option.some.injEq] at hxy
              left
              rw [hxy]),
    (fun _ => rfl),
    (by
      intro r hr
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨r, hr, rfl⟩),
    (by
      intro r ⟨hr, ⟨n₀, imposs⟩⟩
      cases hr with
      | head =>
        exfalso
        exact Option.noConfusion imposs
      | tail _ hr =>
        cases hr with
        | head =>
          exfalso
          exact Option.noConfusion imposs
        | tail _ hr =>
          change r ∈ List.map _ g₁.rules ++ List.map _ g₂.rules at hr
          rw [List.mem_append] at hr
          cases hr with
          | inl hr =>
            exfalso
            rw [List.mem_map] at hr
            rcases hr with ⟨_, -, rfl⟩
            simp only [liftRule, Function.comp_apply] at imposs
            rw [Option.some_inj] at imposs
            exact Sum.noConfusion imposs
          | inr hr =>
            rw [List.mem_map] at hr
            exact hr)⟩

variable {w : List T}

private lemma in_union_of_in_left (hw : w ∈ g₁.language) :
    w ∈ (CFG.union g₁ g₂).language := by
  have deri_start :
    (CFG.union g₁ g₂).Derives [Symbol.nonterminal none]
      [Symbol.nonterminal (some ◩g₁.initial)] := by
    refine CFG.deri_of_tran
      ⟨⟨none, [Symbol.nonterminal (some ◩g₁.initial)]⟩, List.mem_cons_self .., ?_⟩
    use [], []
    simp
  exact deri_start.trans (liftString_all_terminals g₁g.liftNT w ▸ g₁g.lift_derives hw)

private lemma in_union_of_in_right (hw : w ∈ g₂.language) :
    w ∈ (CFG.union g₁ g₂).language := by
  have deri_start :
    (CFG.union g₁ g₂).Derives [Symbol.nonterminal none]
      [Symbol.nonterminal (some ◪g₂.initial)] := by
    refine CFG.deri_of_tran
      ⟨⟨none, [Symbol.nonterminal (some ◪g₂.initial)]⟩,
        List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    use [], []
    simp
  exact deri_start.trans (liftString_all_terminals g₂g.liftNT w ▸ g₂g.lift_derives hw)

private lemma in_left_of_in_union (hw :
    (CFG.union g₁ g₂).Derives
      [Symbol.nonterminal (some ◩g₁.initial)]
      (List.map Symbol.terminal w)) :
    w ∈ g₁.language := by
  apply sinkString_all_terminals g₁g.sinkNT w ▸ g₁g.sink_derives hw
  apply singletonGoodString
  constructor
  rfl

private lemma in_right_of_in_union (hw :
    (CFG.union g₁ g₂).Derives
      [Symbol.nonterminal (some ◪g₂.initial)]
      (List.map Symbol.terminal w)) :
    w ∈ g₂.language := by
  apply sinkString_all_terminals g₂g.sinkNT w ▸ g₂g.sink_derives hw
  apply singletonGoodString
  constructor
  rfl

private lemma impossible_rule {r : Option (g₁.nt ⊕ g₂.nt) × List (Symbol T (Option (g₁.nt ⊕ g₂.nt)))}
    (hg : [Symbol.nonterminal (CFG.union g₁ g₂).initial] =
      ([] : List (Symbol T (CFG.union g₁ g₂).nt)) ++ [Symbol.nonterminal r.fst] ++
      ([] : List (Symbol T (CFG.union g₁ g₂).nt)))
    (hr : r ∈
      List.map (liftRule (Option.some ∘ Sum.inl)) g₁.rules ++
      List.map (liftRule (Option.some ∘ Sum.inr)) g₂.rules) :
    False := by
  have rule_root : none = r.fst := Symbol.nonterminal.inj (List.head_eq_of_cons_eq hg)
  rw [List.mem_append] at hr
  cases hr with
  | inl hr' =>
    rw [List.mem_map] at hr'
    rcases hr' with ⟨_, -, rfl⟩
    exact Option.noConfusion rule_root
  | inr hr' =>
    rw [List.mem_map] at hr'
    rcases hr' with ⟨_, -, rfl⟩
    exact Option.noConfusion rule_root

private lemma in_language_of_in_union (hw : w ∈ (CFG.union g₁ g₂).language) :
    w ∈ g₁.language ∨ w ∈ g₂.language := by
  cases CFG.eq_or_tran_deri_of_deri hw with
  | inl impossible =>
    exfalso
    sorry/-have h0 := congr_arg (List.get? · 0) impossible
    simp only [List.get?_map] at h0
    cases hw0 : w.get? 0 with
    | none => exact Option.noConfusion (hw0 ▸ h0)
    | some => exact Symbol.noConfusion (Option.some.inj (hw0 ▸ h0))-/
  | inr hv =>
    rcases hv with ⟨_, ⟨r, hr, u, v, huv, rfl⟩, hg⟩
    rcases both_empty huv with ⟨rfl, rfl⟩
    cases hr with
    | head =>
      left
      exact in_left_of_in_union hg
    | tail _ hr' =>
      cases hr' with
      | head =>
        right
        exact in_right_of_in_union hg
      | tail _ hr'' =>
        exfalso
        exact impossible_rule huv hr''

lemma CFG.mem_union_language_iff_mem_or_mem :
    w ∈ (CFG.union g₁ g₂).language ↔ w ∈ g₁.language ∨ w ∈ g₂.language :=
  ⟨in_language_of_in_union, fun hw => hw.elim in_union_of_in_left in_union_of_in_right⟩

/-- The class of context-free languages is closed under union. -/
theorem Language.IsContextFree.union (L₁ L₂ : Language T) :
    L₁.IsCF ∧ L₂.IsCF → (L₁ + L₂).IsCF := by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  exact ⟨CFG.union g₁ g₂, Set.ext (fun _ =>
    CFG.mem_union_language_iff_mem_or_mem)⟩
