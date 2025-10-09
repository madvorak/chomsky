import Chomsky.Classes.Unrestricted.Basics.Toolbox
import Chomsky.Utilities.ListUtils
import Mathlib.Tactic.Linarith


section list_technicalities

variable {α β : Type}

-- TODO inline
lemma list_take_one_drop {l : List α} {i : ℕ} (hil : i < l.length) :
  List.take 1 (List.drop i l) = [l.get ⟨i, hil⟩] :=
by
  apply List.take_one_drop_eq_of_lt_length

lemma list_drop_take_succ {l : List α} {i : ℕ} (hil : i < l.length) :
  List.drop i (List.take (i + 1) l) = [l.get ⟨i, hil⟩] :=
by
  rw [List.drop_take, ←list_take_one_drop]
  congr
  omega

lemma list_forall₂_get {R : α → β → Prop} :
  ∀ x : List α, ∀ y : List β, List.Forall₂ R x y →
    ∀ i : ℕ, ∀ hix : i < x.length, ∀ hiy : i < y.length,
      R (x.get ⟨i, hix⟩) (y.get ⟨i, hiy⟩)
| [], [] => by intro _ i hx; exfalso; apply Nat.not_lt_zero; exact hx
| [], _::_ => by intro hyp; exfalso; cases hyp
| _::_, [] => by intro hyp; exfalso; cases hyp
| _::_, _::_ => by
    intro hR i _ _
    rw [List.forall₂_cons] at hR
    cases i
    · unfold List.get
      exact hR.left
    unfold List.get
    apply list_forall₂_get
    exact hR.right

lemma list_filterMap_eq_of_map_eq_map_some {f : α → Option β} :
  ∀ x : List α, ∀ y : List β,
    List.map f x = List.map Option.some y →
      List.filterMap f x = y
| [], [] => fun _ => rfl
| _::_, [] => by intro hyp; exfalso; apply List.cons_ne_nil; exact hyp
| [], _::_ => by intro hyp; exfalso; apply List.cons_ne_nil; exact hyp.symm
| a::_, _::_ => by
    intro hf
    rw [List.map_cons, List.map_cons] at hf
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none =>
      rw [hfa] at hf
      simp at hf
    | some _ =>
      rw [hfa] at hf
      simp at hf ⊢
      obtain ⟨hbb, hll⟩ := hf
      constructor
      · exact hbb
      · apply list_filterMap_eq_of_map_eq_map_some
        exact hll

end list_technicalities


-- new nonterminal type
def nnn (T N₁ N₂ : Type) : Type :=
  Sum (Option (Sum N₁ N₂)) (Sum T T)

-- new symbol type
abbrev nst (T N₁ N₂ : Type) : Type :=
  Symbol T (nnn T N₁ N₂)

variable {T : Type}

section the_construction

def wrapSymbol₁ {N₁ : Type} (N₂ : Type) : Symbol T N₁ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal ◪◩t
  | Symbol.nonterminal n => Symbol.nonterminal ◩(some ◩n)

def wrapSymbol₂ {N₂ : Type} (N₁ : Type) : Symbol T N₂ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal ◪◪t
  | Symbol.nonterminal n => Symbol.nonterminal ◩(some ◪n)

private def wrapGrule₁ {N₁ : Type} (N₂ : Type) (r : Grule T N₁) : Grule T (nnn T N₁ N₂) :=
  Grule.mk (List.map (wrapSymbol₁ N₂) r.inputL) ◩(some ◩r.inputN)
    (List.map (wrapSymbol₁ N₂) r.inputR) (List.map (wrapSymbol₁ N₂) r.output)

private def wrapGrule₂ {N₂ : Type} (N₁ : Type) (r : Grule T N₂) : Grule T (nnn T N₁ N₂) :=
  Grule.mk (List.map (wrapSymbol₂ N₁) r.inputL) ◩(some ◪r.inputN)
    (List.map (wrapSymbol₂ N₁) r.inputR) (List.map (wrapSymbol₂ N₁) r.output)

def rulesForTerminals₁ (N₂ : Type) (g : Grammar T) : List (Grule T (nnn T g.nt N₂)) :=
  List.map (fun t => Grule.mk [] ◪◩t [] [Symbol.terminal t]) (allUsedTerminals g)

def rulesForTerminals₂ (N₁ : Type) (g : Grammar T) : List (Grule T (nnn T N₁ g.nt)) :=
  List.map (fun t => Grule.mk [] ◪◪t [] [Symbol.terminal t]) (allUsedTerminals g)


-- grammar for concatenation of `g₁.language` with `g₂.language`
def bigGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (nnn T g₁.nt g₂.nt) ◩none (
    @Grule.mk T (nnn T g₁.nt g₂.nt) [] ◩none [] [
      Symbol.nonterminal ◩(some ◩g₁.initial),
      Symbol.nonterminal ◩(some ◪g₂.initial)
    ] :: ((
      List.map (wrapGrule₁ g₂.nt) g₁.rules ++
      List.map (wrapGrule₂ g₁.nt) g₂.rules
    ) ++ (
      rulesForTerminals₁ g₂.nt g₁ ++
      rulesForTerminals₂ g₁.nt g₂)))

end the_construction


section easy_direction

lemma grammar_generates_only_legit_terminals {g : Grammar T} {w : List (Symbol T g.nt)}
    (hgw : g.Derives [Symbol.nonterminal g.initial] w)
    (s : Symbol T g.nt) (symbol_derived : s ∈ w) :
  (∃ r : Grule T g.nt, r ∈ g.rules ∧ s ∈ r.output) ∨ (s = Symbol.nonterminal g.initial) :=
by
  induction' hgw with x y _ orig ih
  · rw [List.mem_singleton] at symbol_derived
    right
    exact symbol_derived
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  rw [aft] at symbol_derived
  rw [List.mem_append, List.mem_append] at symbol_derived
  cases' symbol_derived with symbol_derived' s_in_v
  cases' symbol_derived' with s_in_u s_in_out
  · apply ih
    rw [bef]
    repeat'
      rw [List.mem_append]
      left
    exact s_in_u
  · left
    use r
  · apply ih
    rw [bef]
    rw [List.mem_append]
    right
    exact s_in_v

private lemma first_transformation {g₁ g₂ : Grammar T} :
  (bigGrammar g₁ g₂).Transforms
    [Symbol.nonterminal (bigGrammar g₁ g₂).initial]
    [Symbol.nonterminal ◩(some ◩g₁.initial),
     Symbol.nonterminal ◩(some ◪g₂.initial)] :=
by
  use (bigGrammar g₁ g₂).rules.get ⟨0, by simp [bigGrammar]⟩
  constructor
  · simp [bigGrammar]
  use [], []
  constructor
  · rfl
  · rfl

private lemma substitute_terminals {g₁ g₂ : Grammar T} {s : T → Sum T T} {w : List T}
  (rule_for_each_terminal : ∀ t ∈ w,
      Grule.mk [] ◪(s t) [] [Symbol.terminal t] ∈
        rulesForTerminals₁ g₂.nt g₁ ++ rulesForTerminals₂ g₁.nt g₂) :
  (bigGrammar g₁ g₂).Derives
    (List.map (Symbol.nonterminal ∘ Sum.inr ∘ s) w)
    (List.map Symbol.terminal w) :=
by
  induction' w with d l ih
  · apply Grammar.deri_self
  rw [List.map_cons, List.map_cons, ← List.singleton_append, ← List.singleton_append]
  have step_head :
    (bigGrammar g₁ g₂).Transforms
      ([(Symbol.nonterminal ∘ Sum.inr ∘ s) d] ++
        List.map (Symbol.nonterminal ∘ Sum.inr ∘ s) l)
      ([Symbol.terminal d] ++ List.map (Symbol.nonterminal ∘ Sum.inr ∘ s) l)
  · use Grule.mk [] ◪(s d) [] [Symbol.terminal d]
    constructor
    · change _ ∈ List.cons _ _
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      apply rule_for_each_terminal
      apply List.mem_cons_self
    use [], List.map (Symbol.nonterminal ∘ Sum.inr ∘ s) l
    constructor <;> rfl
  apply Grammar.deri_of_tran_deri step_head
  apply Grammar.append_deri
  apply ih
  · intro t tin
    apply rule_for_each_terminal t
    exact List.mem_cons_of_mem d tin

lemma in_big_of_in_concatenated {g₁ g₂ : Grammar T} {w : List T}
    (hwgg : w ∈ g₁.language * g₂.language) :
  w ∈ (bigGrammar g₁ g₂).language :=
by
  rw [Language.mem_mul] at hwgg
  rcases hwgg with ⟨u, hu, v, hv, hw⟩
  unfold Grammar.language at *
  rw [Set.mem_setOf_eq] at *
  apply Grammar.deri_of_tran_deri first_transformation
  rw [← hw]
  rw [List.map_append]
  apply
    (bigGrammar g₁ g₂).deri_of_deri_deri
      (v := List.map Symbol.terminal u ++ [Symbol.nonterminal ◩(some ◪g₂.initial)])
  · clear * - hu
    rw [← List.singleton_append]
    apply Grammar.deri_append
    apply
      (bigGrammar g₁ g₂).deri_of_deri_deri
        (v := List.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inl) u)
    · have upgrade_deri₁ :
        ∀ w : List (Symbol T g₁.nt),
          g₁.Derives [Symbol.nonterminal g₁.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal ◩(some ◩g₁.initial)]
              (List.map (wrapSymbol₁ g₂.nt) w)
      · clear * -
        intro w deri₁
        induction' deri₁ with x y _ orig ih
        · apply Grammar.deri_self
        apply Grammar.deri_of_deri_tran ih
        clear * - orig
        rcases orig with ⟨r, rin, u, v, bef, aft⟩
        use wrapGrule₁ g₂.nt r
        constructor
        · dsimp [bigGrammar]
          apply List.mem_cons_of_mem
          apply List.mem_append_left
          apply List.mem_append_left
          rw [List.mem_map]
          use r
        use List.map (wrapSymbol₁ g₂.nt) u
        use List.map (wrapSymbol₁ g₂.nt) v
        constructor
        · convert congr_arg (List.map (wrapSymbol₁ g₂.nt)) bef
          rw [List.map_append_append]
          rw [List.map_append_append]
          rfl
        · convert congr_arg (List.map (wrapSymbol₁ g₂.nt)) aft
          rw [List.map_append_append]
          rfl
      have upgraded := upgrade_deri₁ _ hu
      rw [List.map_map] at upgraded
      exact upgraded
    · have legit_terminals₁ :
        ∀ t ∈ u, ∃ r : Grule T g₁.nt,
          r ∈ g₁.rules ∧ Symbol.terminal t ∈ r.output
      · intro t tin
        have legit := grammar_generates_only_legit_terminals hu (Symbol.terminal t) (by
          rw [List.mem_map]
          use t
        )
        cases' legit with possibl imposs
        · exact possibl
        · exfalso
          exact Symbol.noConfusion imposs
      apply substitute_terminals
      · intro t tin
        apply List.mem_append_left
        unfold rulesForTerminals₁
        rw [List.mem_map]
        use t
        constructor
        · unfold allUsedTerminals
          rw [List.mem_filterMap]
          use Symbol.terminal t
          constructor
          · rw [List.mem_flatten]
            obtain ⟨r, rin, sttin⟩ := legit_terminals₁ t tin
            use r.output
            constructor
            · apply List.mem_map_of_mem
              exact rin
            · exact sttin
          · rfl
        · rfl
  · clear * - hv
    apply Grammar.append_deri
    apply
      @Grammar.deri_of_deri_deri _ _ _
        (List.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inr) v) _
    · have upgrade_deri₂ :
        ∀ w : List (Symbol T g₂.nt),
          g₂.Derives [Symbol.nonterminal g₂.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal ◩(some ◪g₂.initial)]
              (List.map (wrapSymbol₂ g₁.nt) w)
      · clear * -
        intro w deri₁
        induction' deri₁ with x y _ orig ih
        · apply Grammar.deri_self
        apply Grammar.deri_of_deri_tran ih
        clear * - orig
        rcases orig with ⟨r, rin, u, v, bef, aft⟩
        use wrapGrule₂ g₁.nt r
        constructor
        · change
            wrapGrule₂ g₁.nt r ∈
              _ :: List.map (wrapGrule₁ g₂.nt) g₁.rules ++ List.map (wrapGrule₂ g₁.nt) g₂.rules ++ _
          apply List.mem_cons_of_mem
          apply List.mem_append_left
          apply List.mem_append_right
          rw [List.mem_map]
          use r
        use List.map (wrapSymbol₂ g₁.nt) u
        use List.map (wrapSymbol₂ g₁.nt) v
        constructor
        · convert congr_arg (List.map (wrapSymbol₂ g₁.nt)) bef
          rw [List.map_append_append]
          rw [List.map_append_append]
          rfl
        · convert congr_arg (List.map (wrapSymbol₂ g₁.nt)) aft
          rw [List.map_append_append]
          rfl
      have upgraded := upgrade_deri₂ _ hv
      rw [List.map_map] at upgraded
      exact upgraded
    · have legit_terminals₂ :
        ∀ t ∈ v, ∃ r : Grule T g₂.nt,
          r ∈ g₂.rules ∧ Symbol.terminal t ∈ r.output
      · intro t tin
        have legit := grammar_generates_only_legit_terminals hv (Symbol.terminal t) (by
          rw [List.mem_map]
          use t
        )
        cases' legit with possibl imposs
        · exact possibl
        · exfalso
          exact Symbol.noConfusion imposs
      apply substitute_terminals
      · intro t tin
        apply List.mem_append_right
        unfold rulesForTerminals₂
        rw [List.mem_map]
        use t
        constructor
        · unfold allUsedTerminals
          rw [List.mem_filterMap]
          use Symbol.terminal t
          constructor
          · rw [List.mem_flatten]
            obtain ⟨r, rin, sttin⟩ := legit_terminals₂ t tin
            use r.output
            constructor
            · apply List.mem_map_of_mem
              exact rin
            · exact sttin
          · rfl
        · rfl

end easy_direction


section hard_direction

section correspondence_for_terminals

private def correspondingSymbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
  | Symbol.terminal t, Symbol.terminal t' => t = t'
  | Symbol.nonterminal ◪◩a, Symbol.nonterminal ◪◩a' => a = a'
  | Symbol.nonterminal ◪◪a, Symbol.nonterminal ◪◪a' => a = a'
  | Symbol.nonterminal ◪◩a, Symbol.terminal t => t = a
  | Symbol.nonterminal ◪◪a, Symbol.terminal t => t = a
  | Symbol.nonterminal ◩(some ◩n), Symbol.nonterminal ◩(some ◩n') => n = n'
  | Symbol.nonterminal ◩(some ◪n), Symbol.nonterminal ◩(some ◪n') => n = n'
  | Symbol.nonterminal ◩none, Symbol.nonterminal ◩none => True
  | _, _ => False

private lemma correspondingSymbols_self {N₁ N₂ : Type} (s : nst T N₁ N₂) :
  correspondingSymbols s s :=
by
  cases' s with t n
  · simp [correspondingSymbols]
  · cases' n with a b
    · cases' a with v
      · simp [correspondingSymbols]
      · cases' v with n₁ n₂
        · simp [correspondingSymbols]
        · simp [correspondingSymbols]
    · cases' b with t₁ t₂
      · simp [correspondingSymbols]
      · simp [correspondingSymbols]

private lemma correspondingSymbols_never₁ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s₂ : Symbol T N₂} :
  ¬ correspondingSymbols (wrapSymbol₁ N₂ s₁) (wrapSymbol₂ N₁ s₂) :=
by
  cases s₁ <;> cases s₂ <;> exact not_false

private lemma correspondingSymbols_never₂ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s₂ : Symbol T N₂} :
  ¬ correspondingSymbols (wrapSymbol₂ N₁ s₂) (wrapSymbol₁ N₂ s₁) :=
by
  cases s₁ <;> cases s₂ <;> exact not_false

private def correspondingStrings {N₁ N₂ : Type} : List (nst T N₁ N₂) → List (nst T N₁ N₂) → Prop :=
  List.Forall₂ correspondingSymbols

private lemma correspondingStrings_self {N₁ N₂ : Type} {x : List (nst T N₁ N₂)} :
  correspondingStrings x x :=
by
  unfold correspondingStrings
  rw [List.forall₂_same]
  intros s _
  exact correspondingSymbols_self s

private lemma correspondingStrings_nil {N₁ N₂ : Type} :
  @correspondingStrings T N₁ N₂ [] [] :=
by
  apply List.Forall₂.nil

private lemma correspondingStrings_cons {N₁ N₂ : Type} {d₁ d₂ : nst T N₁ N₂} {l₁ l₂ : List (nst T N₁ N₂)} :
  correspondingStrings (d₁::l₁) (d₂::l₂) ↔ correspondingSymbols d₁ d₂ ∧ correspondingStrings l₁ l₂ :=
by
  apply List.forall₂_cons

private lemma correspondingStrings_singleton {N₁ N₂ : Type} {s₁ s₂ : nst T N₁ N₂}
    (hss : correspondingSymbols s₁ s₂) :
  correspondingStrings [s₁] [s₂] :=
by
  rw [correspondingStrings_cons]
  constructor
  · exact hss
  · exact correspondingStrings_nil

private lemma correspondingStrings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : List (nst T N₁ N₂)}
    (ass₁ : correspondingStrings x₁ y₁) (ass₂ : correspondingStrings x₂ y₂) :
  correspondingStrings (x₁ ++ x₂) (y₁ ++ y₂) :=
by
  unfold correspondingStrings at *
  exact List.rel_append ass₁ ass₂

private lemma correspondingStrings_length {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x y) :
  x.length = y.length :=
by
  unfold correspondingStrings at hxy
  exact List.Forall₂.length_eq hxy

private lemma correspondingStrings_get {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} {i : ℕ}
    (hix : i < x.length) (hiy : i < y.length) (hxy : correspondingStrings x y) :
  correspondingSymbols (x.get ⟨i, hix⟩) (y.get ⟨i, hiy⟩) :=
by
  apply list_forall₂_get
  exact hxy

private lemma correspondingStrings_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x y) :
  correspondingStrings x.reverse y.reverse :=
by
  unfold correspondingStrings at *
  rw [List.forall₂_reverse_iff]
  exact hxy

private lemma correspondingStrings_of_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x.reverse y.reverse) :
  correspondingStrings x y :=
by
  unfold correspondingStrings at *
  rw [List.forall₂_reverse_iff] at hxy
  exact hxy

private lemma correspondingStrings_take {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (List.take n x) (List.take n y) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_take n hxy

private lemma correspondingStrings_drop {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (List.drop n x) (List.drop n y) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_drop n hxy

private lemma correspondingStrings_split {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (List.take n x) (List.take n y) ∧
  correspondingStrings (List.drop n x) (List.drop n y) :=
by
  constructor
  · exact correspondingStrings_take n hxy
  · exact correspondingStrings_drop n hxy

end correspondence_for_terminals

section unwrapping_nst

private def unwrapSymbol₁ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₁)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal ◪◩a => some (Symbol.terminal a)
  | Symbol.nonterminal ◪◪_ => none
  | Symbol.nonterminal ◩(some ◩n) => some (Symbol.nonterminal n)
  | Symbol.nonterminal ◩(some ◪_) => none
  | Symbol.nonterminal ◩none => none

private def unwrapSymbol₂ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₂)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal ◪◩_ => none
  | Symbol.nonterminal ◪◪a => some (Symbol.terminal a)
  | Symbol.nonterminal ◩(some ◩_) => none
  | Symbol.nonterminal ◩(some ◪n) => some (Symbol.nonterminal n)
  | Symbol.nonterminal ◩none => none

private lemma unwrap_wrap₁_symbol {N₁ N₂ : Type} :
  @unwrapSymbol₁ T N₁ N₂ ∘ wrapSymbol₁ N₂ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₂_symbol {N₁ N₂ : Type} :
  @unwrapSymbol₂ T N₁ N₂ ∘ wrapSymbol₂ N₁ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₁_string {N₁ N₂ : Type} {w : List (Symbol T N₁)} :
  (w.map (wrapSymbol₁ N₂)).filterMap unwrapSymbol₁ = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₁_symbol]
  apply List.filterMap_some

private lemma unwrap_wrap₂_string {N₁ N₂ : Type} {w : List (Symbol T N₂)} :
  (w.map (wrapSymbol₂ N₁)).filterMap unwrapSymbol₂ = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₂_symbol]
  apply List.filterMap_some

private lemma unwrap_eq_some_of_correspondingSymbols₁ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s : nst T N₁ N₂}
    (hNss : correspondingSymbols (wrapSymbol₁ N₂ s₁) s) :
  unwrapSymbol₁ s = some s₁ :=
by
  cases' s₁ with t₁ n₁
  · cases' s with t n
    · rw [show t = t₁ by convert hNss]
      rfl
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
      · cases' t with t' t''
        · rw [show t₁ = t' by convert hNss]
          rfl
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
  · cases' s with t n
    · simp [wrapSymbol₁, correspondingSymbols] at hNss
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · cases' n' with n'₁ n'₂
          · rw [show n₁ = n'₁ by convert hNss]
            rfl
          · simp [wrapSymbol₁, correspondingSymbols] at hNss
      · cases' t with t' t''
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · simp [wrapSymbol₁, correspondingSymbols] at hNss

private lemma unwrap_eq_some_of_correspondingSymbols₂ {N₁ N₂ : Type} {s₂ : Symbol T N₂} {s : nst T N₁ N₂}
    (hNss : correspondingSymbols (wrapSymbol₂ N₁ s₂) s) :
  unwrapSymbol₂ s = some s₂ :=
by
  cases' s₂ with t₂ n₂
  · cases' s with t n
    · rw [show t = t₂ by convert hNss]
      rfl
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
      · cases' t with t' t''
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · rw [show t₂ = t'' by convert hNss]
          rfl
  · cases' s with t n
    · simp [wrapSymbol₂, correspondingSymbols] at hNss
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · cases' n' with n'₁ n'₂
          · simp [wrapSymbol₂, correspondingSymbols] at hNss
          · rw [show n₂ = n'₂ by convert hNss]
            rfl
      · cases' t with t' t''
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · simp [wrapSymbol₂, correspondingSymbols] at hNss

private lemma map_unwrap_eq_map_some_of_correspondingStrings₁ {N₁ N₂ : Type} :
  ∀ v : List (Symbol T N₁), ∀ w : List (nst T N₁ N₂),
    correspondingStrings (List.map (wrapSymbol₁ N₂) v) w →
      List.map unwrapSymbol₁ w = List.map Option.some v
  | [], [] => by
      intro _
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      simp [correspondingStrings]
  | a::x, [] => by
      simp [correspondingStrings]
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass
      rw [List.map_cons, List.forall₂_cons] at ass
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₁ ass.left
      · apply map_unwrap_eq_map_some_of_correspondingStrings₁
        exact ass.right

private lemma map_unwrap_eq_map_some_of_correspondingStrings₂ {N₁ N₂ : Type} :
  ∀ v : List (Symbol T N₂), ∀ w : List (nst T N₁ N₂),
    correspondingStrings (List.map (wrapSymbol₂ N₁) v) w →
      List.map unwrapSymbol₂ w = List.map Option.some v
  | [], [] => by
      intro _
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      simp [correspondingStrings]
  | a::x, [] => by
      simp [correspondingStrings]
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass
      rw [List.map_cons, List.forall₂_cons] at ass
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₂ ass.left
      · apply map_unwrap_eq_map_some_of_correspondingStrings₂
        exact ass.right

private lemma filterMap_unwrap_of_correspondingStrings₁ {N₁ N₂ : Type} {v : List (Symbol T N₁)} {w : List (nst T N₁ N₂)}
    (hNvw : correspondingStrings (List.map (wrapSymbol₁ N₂) v) w) :
  List.filterMap unwrapSymbol₁ w = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  apply map_unwrap_eq_map_some_of_correspondingStrings₁
  exact hNvw

private lemma filterMap_unwrap_of_correspondingStrings₂ {N₁ N₂ : Type} {v : List (Symbol T N₂)} {w : List (nst T N₁ N₂)}
    (hNvw : correspondingStrings (List.map (wrapSymbol₂ N₁) v) w) :
  List.filterMap unwrapSymbol₂ w = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  apply map_unwrap_eq_map_some_of_correspondingStrings₂
  exact hNvw

private lemma correspondingStrings_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (hNw : ∃ z : List (Symbol T N₁), correspondingStrings (z.map (wrapSymbol₁ N₂)) w) :
  correspondingStrings (List.map (wrapSymbol₁ N₂) (List.filterMap unwrapSymbol₁ w)) w :=
by
  induction' w with d l ih
  · exact correspondingStrings_nil
  specialize ih (by
    cases' hNw with z hyp
    cases' z with z₀ z'
    · exfalso
      simp [correspondingStrings, wrapSymbol₁] at hyp
    · use z'
      rw [List.map_cons, correspondingStrings_cons] at hyp
      exact hyp.right
  )
  cases' d with t n
  · have unwrap_first_t :
      List.filterMap unwrapSymbol₁ (Symbol.terminal t :: l) =
      Symbol.terminal t :: List.filterMap unwrapSymbol₁ l
    · rfl
    rw [unwrap_first_t]
    unfold List.map
    rw [correspondingStrings_cons]
    constructor
    · simp [wrapSymbol₁, correspondingSymbols]
    · exact ih
  -- probably throw away from here down
  cases' n with o t'
  · cases' o with n'
    · sorry
    · sorry
  rw [List.map_filterMap]
  convert_to
    correspondingStrings
      (List.filterMap Option.some (Symbol.nonterminal ◪t' :: l))
      (Symbol.nonterminal ◪t' :: l)
  · congr
    ext1 a
    cases' a with t n
    · sorry
    · sorry
  rw [List.filterMap_some]
  apply correspondingStrings_self

private lemma correspondingStrings_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (hNw : ∃ z : List (Symbol T N₂), correspondingStrings (z.map (wrapSymbol₂ N₁)) w) :
  correspondingStrings ((w.filterMap unwrapSymbol₂).map (wrapSymbol₂ N₁)) w := -- TODO update the above
by
  induction w with
  | nil =>
    exact correspondingStrings_nil
  | cons d l ih =>
    specialize ih (by
        obtain ⟨z, hz⟩ := hNw
        unfold correspondingStrings at *
        cases z <;> aesop)
    cases d with
    | terminal t =>
      exact List.Forall₂.cons rfl ih
    | nonterminal n =>
      cases n with
      | inl n₀ =>
        cases n₀ with
        | none =>
          sorry
        | some n =>
          cases n with
          | inl n₁ =>
            sorry
          | inr n₂ =>
            sorry
      | inr t =>
        cases t with
        | inl t₁ =>
          sorry
        | inr t₂ =>
          sorry
/-induction' w with d l ih
  · unfold corresponding_strings
    unfold List.filterMap
    unfold List.map
    exact correspondingStrings_nil
  specialize
    ih
      (by
        cases' hNw with z hyp
        unfold corresponding_strings at *
        cases' z with z₀ z'
        · exfalso
          finish
        · use z'
          finish)
  unfold corresponding_strings
  cases d
  · have unwrap_first_t :
      List.filterMap unwrap_symbol₂ (Symbol.terminal d::l) =
        Symbol.terminal d::List.filterMap unwrap_symbol₂ l :=
      by rfl
    rw [unwrap_first_t]
    unfold List.map
    unfold wrapSymbol₂
    rw [List.forall₂_cons] -- correspondingStrings_cons
    constructor
    · unfold corresponding_symbols
    · exact ih
  cases d
  cases d; swap
  cases d; swap
  · have unwrap_first_nlsr :
      List.filterMap unwrap_symbol₂ (Symbol.nonterminal ◩(some ◪d) :: l) =
        Symbol.nonterminal d :: List.filterMap unwrap_symbol₂ l :=
      by rfl
    rw [unwrap_first_nlsr]
    unfold List.map
    unfold wrapSymbol₂
    rw [List.forall₂_cons] -- correspondingStrings_cons
    constructor
    · unfold corresponding_symbols
    · exact ih
  pick_goal 3
  cases d; swap
  · have unwrap_first_nrr :
      List.filterMap unwrap_symbol₂ (Symbol.nonterminal ◪◪d :: l) =
        Symbol.terminal d :: List.filterMap unwrap_symbol₂ l :=
      by rfl
    rw [unwrap_first_nrr]
    unfold List.map
    unfold wrapSymbol₂
    rw [List.forall₂_cons] -- correspondingStrings_cons
    constructor
    · unfold corresponding_symbols
    · exact ih
  any_goals
    exfalso
    cases' hNw with z hyp
    cases' z with z₀ z'
    · have imposs := corresponding_strings_length hyp
      clear * - imposs
      rw [List.length] at imposs
      rw [List.length_map] at imposs
      rw [List.length] at imposs
      linarith
    · rw [List.map_cons] at hyp
      unfold corresponding_strings at hyp
      rw [List.forall₂_cons] at hyp  -- correspondingStrings_cons
      have impos := hyp.left
      clear * - impos
      cases z₀ <;>
        · unfold wrapSymbol₂ at impos
          unfold corresponding_symbols at impos
          exact impos-/

end unwrapping_nst

section very_complicated

private lemma induction_step_for_lifted_rule_from_g₁ {g₁ g₂ : Grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {r : Grule T (nnn T g₁.nt g₂.nt)} (rin : r ∈ List.map (wrapGrule₁ g₂.nt) g₁.rules)
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.output ++ v)
    (ih_x : g₁.Derives [Symbol.nonterminal g₁.initial] x)
    (ih_y : g₂.Derives [Symbol.nonterminal g₂.initial] y)
    (ih_concat : correspondingStrings
        (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)
        a)   :
  ∃ x' : List (Symbol T g₁.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x'  ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y   ∧
    correspondingStrings
      (List.map (wrapSymbol₁ g₂.nt) x' ++ List.map (wrapSymbol₂ g₁.nt) y)
      b   :=
by
  rw [List.mem_map] at rin
  rcases rin with ⟨r₁, rin₁, wrap_r₁_eq_r⟩
  rw [← wrap_r₁_eq_r] at *
  clear wrap_r₁_eq_r
  simp [wrapGrule₁] at *
  rw [← List.singleton_append] at bef
  let m :=
    (List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1 +
      (List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length
  let b' :=
    u ++ List.map (wrapSymbol₁ g₂.nt) r₁.output ++ List.take (x.length - u.length - m) v
  use List.filterMap unwrapSymbol₁ b'
  have critical :
    (List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1 +
        (List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length ≤
      x.length - u.length :=
    by
    clear * - ih_concat bef
    have as_positive :
      u.length +
          ((List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1 +
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length) ≤
        x.length :=
      by
      by_contra contra
      push_neg at contra
      rw [bef] at ih_concat
      clear bef
      repeat' rw [← List.append_assoc] at ih_concat
      have len_pos :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
              List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length >
          0 :=
        by
        repeat' rw [List.length_append]
        rw [List.length_singleton]
        clear * -
        linarith
      have equal_total_len := correspondingStrings_length ih_concat
      have inequality_m1 :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length -
            1 <
          (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
              List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length :=
        sorry
      have inequality_cat :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length -
            1 <
          (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR ++
              v).length :=
        by
        rw [List.length_append _ v]
        apply lt_of_lt_of_le sorry
        exact le_self_add
      have inequality_map :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length -
            1 <
          (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
        by
        rw [equal_total_len]
        sorry
      have inequality_map_opp :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length -
            1 ≥
          (List.map (wrapSymbol₁ g₂.nt) x).length :=
        by
        clear * - contra
        apply Nat.le_pred_of_lt
        repeat' rw [List.length_append]
        repeat' rw [List.length_map]
        rw [List.length_map] at contra
        rw [List.length_map] at contra
        rw [List.length_singleton]
        rw [add_assoc]
        rw [add_assoc]
        rw [add_assoc] at contra
        exact contra
      sorry /-have clash := correspondingStrings_nthLe inequality_map inequality_cat ih_concat
      rw [List.nthLe_append inequality_cat inequality_m1] at clash
      rw [List.nthLe_append_right inequality_map_opp inequality_map] at clash
      rw [List.nthLe_map] at clash ; swap
      · have inequality_map := inequality_map
        rw [List.length_append _ (List.map (wrapSymbol₂ g₁.nt) y)] at inequality_map
        rw [List.length_map _ y] at inequality_map
        rw [tsub_lt_iff_left inequality_map_opp]
        exact inequality_map
      by_cases (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length ≥ 1
      · rw [List.nthLe_append_right] at clash ; swap
        · rw [List.length_append _ (List.map (wrapSymbol₁ g₂.nt) r₁.input_R)]
          have trivi_ineq : ∀ m k : ℕ, k ≥ 1 → m ≤ m + k - 1 :=
            by
            clear * -
            omega
          convert trivi_ineq (u ++ _ ++ [_]).length _ h
        rw [List.nthLe_map] at clash ; swap
        · rw [List.length_map] at h
          repeat' rw [List.length_append]
          repeat' rw [List.length_map]
          rw [List.length_singleton]
          have easy_ineq : ∀ m k : ℕ, k ≥ 1 → m + k - 1 - m < k :=
            by
            clear * -
            omega
          convert easy_ineq (u.length + r₁.input_L.length + 1) _ h
        exact corresponding_symbols_never₂ clash
      · push_neg at h
        have ris_third_is_nil : List.map (wrapSymbol₁ g₂.nt) r₁.input_R = [] :=
          by
          rw [← List.length_eq_zero]
          rw [← Nat.lt_one_iff]
          exact h
        have inequality_m0 :
          (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal ◩(some ◩r₁.input_N)]).length -
              1 <
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                [Symbol.nonterminal ◩(some ◩r₁.input_N)]).length :=
          by
          rw [ris_third_is_nil] at inequality_m1
          rw [List.append_nil] at inequality_m1
          exact inequality_m1
        simp_rw [ris_third_is_nil] at clash
        simp only [List.append_nil] at clash
        rw [List.nthLe_append_right] at clash
        swap;
        · apply le_of_eq
          rw [List.length_append _ [_]]
          rw [List.length_singleton]
          apply Nat.succ_sub_one
        rw [List.nthLe_singleton] at clash
        change corresponding_symbols _ (wrapSymbol₁ g₂.nt (Symbol.nonterminal r₁.input_N)) at clash
        exact corresponding_symbols_never₂ clash-/
    omega
  constructor
  · constructor
    · apply Grammar.deri_of_deri_tran ih_x
      use r₁
      constructor
      · exact rin₁
      use List.filterMap unwrapSymbol₁ u
      use List.filterMap unwrapSymbol₁ (List.take (x.length - u.length - m) v)
      constructor
      · have x_equiv :
          correspondingStrings (List.map (wrapSymbol₁ g₂.nt) x)
            (List.take x.length
              (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                    [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                  List.map (wrapSymbol₁ g₂.nt) r₁.inputR ++
                v)) :=
          by
          rw [bef] at ih_concat
          clear * - ih_concat
          rw [← List.append_assoc _ _ v] at ih_concat
          rw [← List.append_assoc _ _ v] at ih_concat
          rw [List.append_assoc u]
          rw [List.append_assoc u]
          rw [List.append_assoc u]
          rw [List.append_assoc (List.map (wrapSymbol₁ g₂.nt) r₁.inputL)]
          sorry /-convert correspondingStrings_take x.length ih_concat
          · have x_len_eq : x.length = (List.map (wrapSymbol₁ g₂.nt) x).length := by
              rw [List.length_map]
            rw [x_len_eq]
            rw [List.take_left]-/
        clear * - x_equiv critical
        have ul_le_xl : u.length ≤ x.length :=
          by
          clear * - critical
          have weaker_le : 1 ≤ x.length - u.length := by omega
          have stupid_le : u.length + 1 ≤ x.length := by omega
          exact Nat.le_of_succ_le stupid_le
        repeat' rw [List.take_append_eq_append_take] at x_equiv
        rw [List.take_of_length_le ul_le_xl] at x_equiv
        repeat' rw [List.append_assoc]
        have chunk2 :
          List.take (x.length - u.length) (List.map (wrapSymbol₁ g₂.nt) r₁.inputL) =
            List.map (wrapSymbol₁ g₂.nt) r₁.inputL :=
          by
          apply List.take_of_length_le
          clear * - critical
          omega
        have chunk3 :
          List.take (x.length - (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length)
              [@Symbol.nonterminal T (nnn T g₁.nt g₂.nt) ◩(some ◩r₁.inputN)] =
            [Symbol.nonterminal ◩(some ◩r₁.inputN)] :=
          by
          apply List.take_of_length_le
          clear * - critical
          change 1 ≤ x.length - (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length
          rw [List.length_append]
          have weakened :
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1 ≤ x.length - u.length := by omega
          have goal_as_le_sub_sub :
            1 ≤ x.length - u.length - (List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length := by omega
          rw [tsub_add_eq_tsub_tsub]
          exact goal_as_le_sub_sub
        have chunk4 :
          List.take
              (x.length -
                (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                    [Symbol.nonterminal ◩(some ◩r₁.inputN)]).length)
              (List.map (wrapSymbol₁ g₂.nt) r₁.inputR) =
            List.map (wrapSymbol₁ g₂.nt) r₁.inputR :=
          by
          apply List.take_of_length_le
          clear * - critical
          rw [List.length_append_append]
          change
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length ≤
              x.length - (u.length + (List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1)
          omega
        have chunk5 :
          List.take
              (x.length -
                (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                      [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                    List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length)
              v =
            List.take (x.length - u.length - m) v :=
          by
          repeat' rw [List.length_append]
          apply congr_arg₂; swap
          · rfl
          have rearrange_sum_of_four : ∀ a b c d : ℕ, a + b + c + d = a + (b + c + d) := by omega
          rw [rearrange_sum_of_four]
          show x.length - (u.length + m) = x.length - u.length - m
          clear * -
          omega
        rw [chunk2, chunk3, chunk4, chunk5] at x_equiv
        clear chunk2 chunk3 chunk4 chunk5
        obtain ⟨temp_5, equiv_segment_5⟩ :=
          correspondingStrings_split
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                  [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length
            x_equiv
        clear x_equiv
        rw [List.drop_left] at equiv_segment_5
        rw [List.take_left] at temp_5
        obtain ⟨temp_4, equiv_segment_4⟩ :=
          correspondingStrings_split
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
                [Symbol.nonterminal ◩(some ◩r₁.inputN)]).length
            temp_5
        clear temp_5
        rw [List.drop_left] at equiv_segment_4
        rw [List.take_left] at temp_4
        rw [List.take_take] at temp_4
        obtain ⟨temp_3, equiv_segment_3⟩ :=
          correspondingStrings_split (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length temp_4
        clear temp_4
        rw [List.drop_left] at equiv_segment_3
        rw [List.take_left] at temp_3
        rw [List.take_take] at temp_3
        obtain ⟨equiv_segment_1, equiv_segment_2⟩ := correspondingStrings_split u.length temp_3
        clear temp_3
        rw [List.drop_left] at equiv_segment_2
        rw [List.take_left] at equiv_segment_1
        rw [List.take_take] at equiv_segment_1
        have equiv_sgmnt_1 :
          correspondingStrings (List.take u.length (List.map (wrapSymbol₁ g₂.nt) x)) u := by
          simpa using equiv_segment_1
        have equiv_sgmnt_2 :
          correspondingStrings
            (List.drop u.length
              (List.take (u.length + r₁.inputL.length) (List.map (wrapSymbol₁ g₂.nt) x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputL) :=
          by simpa using equiv_segment_2
        have equiv_sgmnt_3 :
          correspondingStrings
            (List.drop (u.length + r₁.inputL.length)
              (List.take (u.length + (r₁.inputL.length + 1)) (List.map (wrapSymbol₁ g₂.nt) x)))
            [Symbol.nonterminal ◩(some ◩r₁.inputN)] :=
          by simpa using equiv_segment_3
        have equiv_sgmnt_4 :
          correspondingStrings
            (List.drop (u.length + (r₁.inputL.length + 1))
              (List.take (u.length + (r₁.inputL.length + (r₁.inputR.length + 1)))
                (List.map (wrapSymbol₁ g₂.nt) x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputR) :=
          by simpa using equiv_segment_4
        have equiv_sgmnt_5 :
          correspondingStrings
            (List.drop (u.length + (r₁.inputL.length + (r₁.inputR.length + 1)))
              (List.map (wrapSymbol₁ g₂.nt) x))
            (List.take (x.length - u.length - m) v) :=
          by simpa using equiv_segment_5
        clear equiv_segment_1 equiv_segment_2 equiv_segment_3 equiv_segment_4 equiv_segment_5
        have segment_1_eqi :
          correspondingStrings (List.map (wrapSymbol₁ g₂.nt) (List.take u.length x)) u :=
          by
          convert equiv_sgmnt_1
          rw [List.map_take]
        have segment_1_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_1_eqi).symm
        rw [← List.take_append_drop u.length x]
        apply congr_arg₂
        · exact segment_1_equ
        clear segment_1_equ segment_1_eqi equiv_sgmnt_1
        have segment_2_eqi :
          correspondingStrings
            (List.map (wrapSymbol₁ g₂.nt) (List.take r₁.inputL.length (List.drop u.length x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.inputL) :=
          by
          convert equiv_sgmnt_2
          rw [List.map_take]
          rw [List.map_drop]
          rw [List.drop_take]
          simp
        have segment_2_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_2_eqi).symm
        rw [unwrap_wrap₁_string] at segment_2_equ
        rw [← List.take_append_drop r₁.inputL.length (List.drop u.length x)]
        apply congr_arg₂
        · exact segment_2_equ
        clear segment_2_equ segment_2_eqi equiv_sgmnt_2
        rw [List.drop_drop]
        have segment_3_eqi :
          correspondingStrings
            (List.map (wrapSymbol₁ g₂.nt)
              (List.take 1 (List.drop (r₁.inputL.length + u.length) x)))
            (List.map (wrapSymbol₁ g₂.nt) [Symbol.nonterminal r₁.inputN]) :=
          by
          convert equiv_sgmnt_3
          rw [List.map_take]
          rw [List.map_drop]
          rw [← add_assoc]
          rw [List.drop_take]
          rw [add_comm]
          simp
        have segment_3_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_3_eqi).symm
        rw [unwrap_wrap₁_string] at segment_3_equ
        sorry /-rw [← List.take_append_drop 1 (List.drop (r₁.inputL.length + u.length) x)]
        apply congr_arg₂
        · exact segment_3_equ
        clear segment_3_equ segment_3_eqi equiv_sgmnt_3
        rw [List.drop_drop]
        have segment_4_eqi :
          corresponding_strings
            (List.map (wrapSymbol₁ g₂.nt)
              (List.take r₁.input_R.length (List.drop (1 + (r₁.input_L.length + u.length)) x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_R) :=
          by
          convert equiv_sgmnt_4
          rw [List.map_take]
          rw [List.map_drop]
          have sum_rearrange :
            u.length + (r₁.input_L.length + (r₁.input_R.length + 1)) =
              u.length + (r₁.input_L.length + 1) + r₁.input_R.length :=
            by linarith
          rw [sum_rearrange]
          rw [List.drop_take]
          have small_sum_rearr :
            1 + (r₁.input_L.length + u.length) = u.length + (r₁.input_L.length + 1) := by linarith
          rw [small_sum_rearr]
        have segment_4_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_4_eqi).symm
        rw [unwrap_wrap₁_string] at segment_4_equ
        rw [←
          List.take_append_drop r₁.input_R.length
            (List.drop (1 + (r₁.input_L.length + u.length)) x)]
        apply congr_arg₂
        · exact segment_4_equ
        clear segment_4_equ segment_4_eqi equiv_sgmnt_4
        rw [List.drop_drop]
        repeat' rw [List.length_append]
        repeat' rw [List.length_take]
        repeat' rw [List.length_drop]
        have sum_of_min_lengths :
          min u.length x.length +
              (min r₁.input_L.length (x.length - u.length) +
                (min 1 (x.length - (r₁.input_L.length + u.length)) +
                  (min r₁.input_R.length (x.length - (1 + (r₁.input_L.length + u.length))) +
                    (x.length - (r₁.input_R.length + (1 + (r₁.input_L.length + u.length))))))) =
            x.length :=
          by
          have add_mirror :
            r₁.input_R.length + 1 + r₁.input_L.length = r₁.input_L.length + 1 + r₁.input_R.length :=
            by ring
          rw [List.length_map, List.length_map, ← add_mirror] at critical
          have min1 : min u.length x.length = u.length :=
            by
            apply min_eq_left
            exact ul_le_xl
          have min2 : min r₁.input_L.length (x.length - u.length) = r₁.input_L.length :=
            by
            clear * - critical
            apply min_eq_left
            apply le_trans _ critical
            apply le_add_self
          have min3 : min 1 (x.length - (r₁.input_L.length + u.length)) = 1 :=
            by
            clear * - critical
            apply min_eq_left
            omega
          have min4 :
            min r₁.input_R.length (x.length - (1 + (r₁.input_L.length + u.length))) =
              r₁.input_R.length :=
            by
            clear * - critical
            apply min_eq_left
            omega
          rw [min1, min2, min3, min4]
          rw [le_tsub_iff_right ul_le_xl] at critical
          clear * - critical add_mirror
          repeat' rw [← add_assoc]
          have sum_eq_sum :
            u.length + r₁.input_L.length + 1 + r₁.input_R.length =
              r₁.input_R.length + 1 + r₁.input_L.length + u.length :=
            by
            rw [add_mirror]
            rw [add_assoc]
            rw [add_assoc]
            rw [add_comm]
            rw [← add_assoc _ 1 _]
          rw [sum_eq_sum]
          exact Nat.add_sub_of_le critical
        rw [sum_of_min_lengths]
        clear * - equiv_sgmnt_5
        have another_rearranging :
          r₁.input_R.length + (1 + (r₁.input_L.length + u.length)) =
            u.length + (r₁.input_L.length + (r₁.input_R.length + 1)) :=
          by ring
        rw [another_rearranging]
        rw [← List.map_drop] at equiv_sgmnt_5
        symm
        exact filter_map_unwrap_of_corresponding_strings₁ equiv_sgmnt_5-/
      · sorry/-rw [List.filterMap_append_append]
        congr
        rw [unwrap_wrap₁_string]-/
      · sorry
    · sorry
  rw [aft]
  rw [bef] at ih_concat
  rw [List.filterMap_append_append, List.map_append_append, List.append_assoc, List.append_assoc]
  refine ⟨ih_y, ?_⟩
  apply correspondingStrings_append
  · have part_for_u := correspondingStrings_take u.length ih_concat
    rw [List.take_left] at part_for_u
    have trivi : u.length ≤ (List.map (wrapSymbol₁ g₂.nt) x).length :=
      by
      clear * - critical
      rw [List.length_map]
      omega
    rw [List.take_append_of_le_length trivi] at part_for_u
    clear * - part_for_u
    rw [← List.map_take] at part_for_u
    apply correspondingStrings_after_wrap_unwrap_self₁
    use List.take u.length x
  apply correspondingStrings_append
  · rw [unwrap_wrap₁_string]
    sorry --apply correspondingStrings_self
  convert_to
    correspondingStrings _
      (List.take (x.length - u.length - m) v ++ List.drop (x.length - u.length - m) v)
  · rw [List.take_append_drop]
  apply correspondingStrings_append
  · have eqi := correspondingStrings_take (List.map (wrapSymbol₁ g₂.nt) x).length ih_concat
    rw [List.take_left] at eqi
    have part_for_v_beginning := correspondingStrings_drop (u.length + m) eqi
    clear * - part_for_v_beginning critical
    rw [← List.map_drop] at part_for_v_beginning
    apply correspondingStrings_after_wrap_unwrap_self₁
    use List.drop (u.length + m) x
    sorry /-convert part_for_v_beginning
    clear part_for_v_beginning
    rw [List.length_map]
    rw [List.take_append_eq_append_take]
    rw [List.drop_append_eq_append_drop]
    have tul_lt : (List.take x.length u).length ≤ u.length + m :=
      by
      rw [List.length_take]
      calc
        min x.length u.length ≤ u.length := min_le_right _ _
        _ ≤ u.length + m := le_self_add
    rw [List.drop_eq_nil_of_le tul_lt]
    rw [List.nil_append]
    rw [← List.append_assoc _ _ v]
    rw [← List.append_assoc _ _ v]
    rw [← List.append_assoc]
    rw [List.take_append_eq_append_take]
    rw [List.drop_append_eq_append_drop]
    have rul_inp_len :
      (List.map (wrapSymbol₁ g₂.nt) r₁.inputL ++
              [Symbol.nonterminal ◩(some ◩r₁.inputN)] ++
            List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length =
        m :=
      by
      rw [List.length_append_append]
      rw [List.length_singleton]
    have u_is_shorter : min x.length u.length = u.length :=
      by
      apply min_eq_right
      clear * - critical
      omega
    rw [List.drop_eq_nil_of_le]; swap
    · rw [List.length_take]
      rw [rul_inp_len]
      rw [List.length_take]
      rw [u_is_shorter]
      calc
        min (x.length - u.length) m ≤ m := min_le_right _ _
        _ ≤ u.length + m - u.length := le_add_tsub_swap
    rw [List.nil_append]
    rw [List.length_take]
    rw [List.length_take]
    rw [rul_inp_len]
    have zero_dropping : u.length + m - min x.length u.length - min (x.length - u.length) m = 0 :=
      by
      have middle_cannot_exceed : min (x.length - u.length) m = m := min_eq_right critical
      rw [u_is_shorter, middle_cannot_exceed]
      clear * -
      omega
    rw [zero_dropping]
    unfold List.drop-/
  -- now we have what `g₂` generated
  have reverse_concat := correspondingStrings_reverse ih_concat
  repeat' rw [List.reverse_append] at reverse_concat
  have the_part := correspondingStrings_take y.length reverse_concat
  apply correspondingStrings_of_reverse
  have len_sum : y.length + (x.length - u.length - m) = v.length :=
    by
    change
      y.length +
          (x.length - u.length -
            ((List.map (wrapSymbol₁ g₂.nt) r₁.inputL).length + 1 +
              (List.map (wrapSymbol₁ g₂.nt) r₁.inputR).length)) =
        v.length
    have len_concat := correspondingStrings_length ih_concat
    clear * - len_concat critical
    repeat' rw [List.length_append] at len_concat
    rw [List.length_map] at len_concat
    rw [List.length_map] at len_concat
    rw [List.length_singleton] at len_concat
    rw [← Nat.add_sub_assoc]; swap
    · exact critical
    rw [← Nat.add_sub_assoc]; swap
    · clear * - critical
      omega
    rw [add_comm] at len_concat
    rw [len_concat]
    clear len_concat
    rw [add_tsub_cancel_left]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc]
    sorry
  have yl_lt_vl : y.length ≤ v.length := Nat.le.intro len_sum
  convert_to correspondingStrings _ (List.take y.length v.reverse)
  · convert_to (List.drop (v.length - y.length) v).reverse = List.take y.length v.reverse
    · apply congr_arg
      apply congr_arg₂
      · clear * - len_sum
        omega
      · rfl
    exact List.take_reverse.symm
  clear * - the_part yl_lt_vl
  rw [List.take_append_of_le_length] at the_part ; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  repeat' rw [List.append_assoc] at the_part
  rw [List.take_append_of_le_length] at the_part ; swap
  · rw [List.length_reverse]
    exact yl_lt_vl
  rw [List.take_of_length_le] at the_part ; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  exact the_part

private lemma induction_step_for_lifted_rule_from_g₂ {g₁ g₂ : Grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {r : Grule T (nnn T g₁.nt g₂.nt)} (rin : r ∈ List.map (wrapGrule₂ g₁.nt) g₂.rules)
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.output ++ v)
    (ih_x : g₁.Derives [Symbol.nonterminal g₁.initial] x)
    (ih_y : g₂.Derives [Symbol.nonterminal g₂.initial] y)
    (ih_concat : correspondingStrings
        (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)
        a)   :
  ∃ y' : List (Symbol T g₂.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x   ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y'  ∧
    correspondingStrings
      (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y')
      b   :=
by sorry
  /-rw [List.mem_map] at rin
  rcases rin with ⟨r₂, rin₂, wrap_r₂_eq_r⟩
  rw [← wrap_r₂_eq_r] at *
  clear wrap_r₂_eq_r
  simp [wrap_grule₂] at *
  rw [← List.singleton_append] at bef
  rw [bef] at ih_concat
  let b' := List.drop x.length u ++ List.map (wrapSymbol₂ g₁.nt) r₂.output_string ++ v
  use List.filterMap unwrap_symbol₂ b'
  have total_len := corresponding_strings_length ih_concat
  repeat' rw [List.length_append] at total_len
  repeat' rw [List.length_map] at total_len
  have matched_right : u.length ≥ x.length :=
    by
    clear * - ih_concat total_len
    by_contra
    push_neg at h
    rename' h => ul_lt_xl
    have ul_lt_ihls :
      u.length < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
      by
      rw [List.length_append]
      rw [List.length_map]
      rw [List.length_map]
      exact Nat.lt_add_right _ _ _ ul_lt_xl
    have ul_lt_ihrs :
      u.length <
        (u ++
            (List.map (wrapSymbol₂ g₁.nt) r₂.input_L ++
              ([Symbol.nonterminal ◩(some ◪r₂.input_N)))] ++
                (List.map (wrapSymbol₂ g₁.nt) r₂.input_R ++ v)))).length :=
      by
      repeat' rw [List.length_append]
      rw [List.length_singleton]
      clear * -
      linarith
    have ulth := correspondingStrings_nthLe ul_lt_ihls ul_lt_ihrs ih_concat
    rw [List.nthLe_append ul_lt_ihls] at ulth ; swap
    · rw [List.length_map]
      exact ul_lt_xl
    rw [List.nthLe_append_right] at ulth ; swap
    · rfl
    rw [List.nthLe_map] at ulth ; swap
    · exact ul_lt_xl
    by_cases (List.map (wrapSymbol₂ g₁.nt) r₂.input_L).length > u.length - u.length
    · rw [List.nthLe_append _ h] at ulth
      rw [List.nthLe_map] at ulth ; swap
      · rw [List.length_map] at h
        exact h
      exact corresponding_symbols_never₁ ulth
    push_neg at h
    rw [List.nthLe_append_right h] at ulth
    have matched_central_nt :
      corresponding_symbols (wrapSymbol₁ g₂.nt (x.nth_le u.length ul_lt_xl))
        (wrapSymbol₂ g₁.nt (Symbol.nonterminal r₂.input_N)) :=
      by
      clear * - ulth
      finish
    exact corresponding_symbols_never₁ matched_central_nt
  constructor
  · constructor
    · exact ih_x
    · apply Grammar.deri_of_deri_tran ih_y
      use r₂
      constructor
      · exact rin₂
      use List.filterMap unwrap_symbol₂ (List.drop x.length u)
      use List.filterMap unwrap_symbol₂ v
      constructor
      · have corres_y :=
          corresponding_strings_drop (List.map (wrapSymbol₁ g₂.nt) x).length ih_concat
        rw [List.drop_left] at corres_y
        rw [List.drop_append_of_le_length] at corres_y ; swap
        · rw [List.length_map]
          exact matched_right
        clear * - corres_y total_len
        repeat' rw [List.append_assoc]
        obtain ⟨seg1, rest1⟩ :=
          corresponding_strings_split (List.drop (List.map (wrapSymbol₁ g₂.nt) x).length u).length
            corres_y
        clear corres_y
        rw [List.take_left] at seg1
        rw [List.drop_left] at rest1
        rw [← List.take_append_drop (List.filterMap unwrap_symbol₂ (List.drop x.length u)).length y]
        rw [← List.map_take] at seg1
        have min_uxy : min (u.length - x.length) y.length = u.length - x.length :=
          by
          rw [min_eq_left]
          clear * - total_len
          omega
        have tuxy :
          List.take (List.take (u.length - x.length) y).length y =
            List.take (u.length - x.length) y :=
          by
          rw [List.length_take]
          rw [min_uxy]
        have fmu1 := filter_map_unwrap_of_corresponding_strings₂ seg1
        rw [List.length_map] at fmu1
        have fml :
          (List.filterMap unwrap_symbol₂ (List.drop x.length u)).length =
            (List.drop x.length u).length :=
          by
          rw [congr_arg List.length fmu1]
          rw [List.length_take] at tuxy
          rw [List.length_drop]
          rw [min_uxy] at tuxy
          rw [congr_arg List.length tuxy]
          rw [List.length_take]
          exact min_uxy
        apply congr_arg₂
        · rw [fmu1]
          rw [List.length_drop]
          exact tuxy
        clear seg1 fmu1 tuxy min_uxy
        rw [List.length_map] at rest1
        obtain ⟨seg2, rest2⟩ :=
          corresponding_strings_split (List.map (wrapSymbol₂ g₁.nt) r₂.input_L).length rest1
        clear rest1
        rw [List.take_left] at seg2
        rw [List.drop_left] at rest2
        rw [←
          List.take_append_drop (List.map (wrapSymbol₂ g₁.nt) r₂.input_L).length
            (List.drop (List.filterMap unwrap_symbol₂ (List.drop x.length u)).length y)]
        apply congr_arg₂
        · clear * - seg2 fml
          rw [← List.map_drop] at seg2
          rw [← List.map_take] at seg2
          have fmu2 := filter_map_unwrap_of_corresponding_strings₂ seg2
          rw [List.length_map] at fmu2
          rw [List.length_map]
          rw [unwrap_wrap₂_string] at fmu2
          rw [fml]
          exact fmu2.symm
        clear seg2
        rw [List.length_map] at rest2
        rw [List.drop_drop] at rest2 ⊢
        obtain ⟨seg3, rest3⟩ := corresponding_strings_split 1 rest2
        clear rest2
        rw [List.take_left' (List.length_singleton _)] at seg3
        rw [List.drop_left' (List.length_singleton _)] at rest3
        rw [List.length_map]
        rw [fml]
        rw [←
          List.take_append_drop 1 (List.drop (r₂.input_L.length + (List.drop x.length u).length) y)]
        apply congr_arg₂
        · rw [← List.map_drop] at seg3
          rw [← List.map_take] at seg3
          have fmu3 := filter_map_unwrap_of_corresponding_strings₂ seg3
          exact fmu3.symm
        clear seg3
        rw [List.drop_drop] at rest3 ⊢
        rw [← List.map_drop] at rest3
        rw [← filter_map_unwrap_of_corresponding_strings₂ rest3]
        rw [List.filterMap_append]
        rw [unwrap_wrap₂_string]
      · rw [List.filterMap_append_append]
        congr
        apply unwrap_wrap₂_string
  rw [aft]
  rw [List.filterMap_append_append]
  rw [List.map_append_append]
  rw [List.append_assoc]
  rw [← List.append_assoc (List.map (wrapSymbol₁ g₂.nt) x)]
  apply corresponding_strings_append; swap
  · rw [unwrap_wrap₂_string]
    apply corresponding_strings_append
    · apply corresponding_strings_self
    apply corresponding_string_after_wrap_unwrap_self₂
    repeat' rw [← List.append_assoc] at ih_concat
    have rev := corresponding_strings_reverse ih_concat
    rw [List.reverse_append _ v] at rev
    have tak := corresponding_strings_take v.reverse.length rev
    rw [List.take_left] at tak
    have rtr := corresponding_strings_reverse tak
    have nec : v.reverse.length ≤ (List.map (wrapSymbol₂ g₁.nt) y).reverse.length :=
      by
      clear * - matched_right total_len
      rw [List.length_reverse]
      rw [List.length_reverse]
      rw [List.length_map]
      linarith
    clear * - rtr nec
    rw [List.reverse_reverse] at rtr
    rw [List.reverse_append] at rtr
    rw [List.take_append_of_le_length nec] at rtr
    rw [List.reverse_take] at rtr ; swap
    · rw [List.length_reverse (List.map (wrapSymbol₂ g₁.nt) y)] at nec
      exact nec
    rw [← List.map_drop] at rtr
    rw [List.reverse_reverse] at rtr
    exact ⟨_, rtr⟩
  rw [← List.take_append_drop x.length u]
  apply corresponding_strings_append
  · have almost := corresponding_strings_take x.length ih_concat
    rw [List.take_append_of_le_length matched_right] at almost
    convert almost
    have xl_eq : x.length = (List.map (wrapSymbol₁ g₂.nt) x).length := by rw [List.length_map]
    rw [xl_eq]
    rw [List.take_left]
  · rw [List.take_append_drop]
    apply corresponding_string_after_wrap_unwrap_self₂
    have tdc := corresponding_strings_drop x.length (corresponding_strings_take u.length ih_concat)
    rw [List.take_left] at tdc
    have ul_eq : u.length = x.length + (u.length - x.length) :=
      by
      rw [← Nat.add_sub_assoc matched_right]
      rw [add_comm]
      rw [Nat.add_sub_assoc]; swap
      · rfl
      rw [Nat.sub_self]
      rw [add_zero]
    rw [ul_eq] at tdc
    clear * - tdc
    rw [List.drop_take] at tdc
    rw [List.drop_left'] at tdc ; swap
    · apply List.length_map
    rw [← List.map_take] at tdc
    exact ⟨_, tdc⟩-/

private lemma big_induction {g₁ g₂ : Grammar T} {w : List (nst T g₁.nt g₂.nt)}
    (hggw : (bigGrammar g₁ g₂).Derives
        [Symbol.nonterminal ◩(some ◩g₁.initial),
         Symbol.nonterminal ◩(some ◪g₂.initial)]
        w) :
  ∃ x : List (Symbol T g₁.nt), ∃ y : List (Symbol T g₂.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x  ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y  ∧
    correspondingStrings
      (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)
      w   :=
by
  induction' hggw with a b _ orig ih
  · use [Symbol.nonterminal g₁.initial], [Symbol.nonterminal g₂.initial]
    constructor
    · apply Grammar.deri_self
    constructor
    · apply Grammar.deri_self
    simp only [wrapSymbol₁, wrapSymbol₂, List.map_singleton, List.singleton_append]
    rw [correspondingStrings_cons]
    constructor
    · rfl
    rw [correspondingStrings_cons]
    constructor
    · rfl
    exact correspondingStrings_nil
  rcases ih with ⟨x, y, ih_x, ih_y, ih_concat⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  simp only [bigGrammar, List.mem_cons, List.mem_append, or_assoc] at rin
  rcases rin with rinit | rin₁ | rin₂ | rte₁ | rte₂
  · exfalso
    rw [rinit] at bef
    clear * - ih_concat bef
    simp only [List.append_nil] at bef
    rw [bef] at ih_concat
    have same_lengths := correspondingStrings_length ih_concat
    clear bef
    have ulen₁ : u.length < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length
    · rw [List.length_append _ v] at same_lengths
      rw [List.length_append u _] at same_lengths
      rw [List.length_singleton] at same_lengths
      clear * - same_lengths
      linarith
    rw [List.append_assoc] at ih_concat
    have eqi_symb := correspondingStrings_get ulen₁ ?_ ih_concat ; swap
    · rw [List.length_append, List.length_append, List.length_singleton]
      clear * -
      linarith
    sorry /-
    rw [List.get_append_right] at eqi_symb
    simp only [Nat.sub_self, List.singleton_append, List.get] at eqi_symb
    have eq_none :
      (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length ulen₁ =
        Symbol.nonterminal ◩none) :=
      by
      clear * - eqi_symb
      cases'
        (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length ulen₁ with
        t s
      · exfalso
        unfold correspondingSymbols at eqi_symb
        exact eqi_symb
      cases s
      · cases s
        · rfl
        exfalso
        clear * - eqi_symb
        cases s <;> tauto
      · exfalso
        clear * - eqi_symb
        cases s <;> tauto
    have impossible_in :
      Symbol.nonterminal ◩none) ∈
        List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y :=
      by
      rw [List.mem_iff_nthLe]
      use u.length
      use ulen₁
      exact eq_none
    rw [List.mem_append] at impossible_in
    cases impossible_in <;>
      · rw [List.mem_map] at impossible_in
        rcases impossible_in with ⟨s, -, contradic⟩
        clear * - contradic
        cases s
        · have imposs := Symbol.nonterminal.inj contradic
          exact Sum.noConfusion imposs
        · have impos := Sum.inl.inj (Symbol.nonterminal.inj contradic)
          exact Option.noConfusion impos-/
  · cases' induction_step_for_lifted_rule_from_g₁ rin₁ bef aft ih_x ih_y ih_concat with x' pros
    exact ⟨x', y, pros⟩
  · use x
    exact induction_step_for_lifted_rule_from_g₂ rin₂ bef aft ih_x ih_y ih_concat
  · use x, y
    sorry
  · use x, y
    sorry
  /-constructor
    · constructor
      · exact ih_x
      · exact ih_y
    rw [aft]
    rw [bef] at ih_concat
    rw [List.mem_append] at rin
    cases rin
    · unfold rulesForTerminals₁ at rin
      rw [List.mem_map] at rin
      rcases rin with ⟨t, -, eq_r⟩
      rw [← eq_r] at *
      clear eq_r
      rw [List.append_nil] at ih_concat
      rw [List.append_nil] at ih_concat
      have xy_split_u :
        List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y =
          List.take u.length (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) ++
            List.drop u.length (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) :=
        by rw [List.take_append_drop]
      rw [xy_split_u]
      have part_for_u := corresponding_strings_take u.length ih_concat
      rw [List.append_assoc]
      apply corresponding_strings_append
      · convert part_for_u
        rw [List.append_assoc]
        rw [List.take_left]
      have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal ◪◩t))]).length :=
        by
        rw [List.length_append]
        rw [List.length_singleton]
        apply lt_add_one
      have ul_lt_len_umv :
        u.length < (u ++ [Symbol.nonterminal ◪◩t))] ++ v).length :=
        by
        rw [List.length_append]
        apply lt_of_lt_of_le ul_lt_len_um
        apply le_self_add
      have ul_lt_len_xy :
        u.length < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
        by
        have same_len := corresponding_strings_length ih_concat
        rw [same_len]
        exact ul_lt_len_umv
      have middle_nt := correspondingStrings_nthLe ul_lt_len_xy ul_lt_len_umv ih_concat
      rw [List.nthLe_append ul_lt_len_umv ul_lt_len_um] at middle_nt
      rw [List.nthLe_append_right (by rfl) ul_lt_len_um] at middle_nt
      have middle_nt_elem :
        corresponding_symbols
          ((List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length
            ul_lt_len_xy)
          (Symbol.nonterminal ◪◩t))) :=
        by
        convert middle_nt
        sorry
      have xy_split_nt :
        List.drop u.length (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) =
          List.take 1
              (List.drop u.length
                (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)) ++
            List.drop 1
              (List.drop u.length
                (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)) :=
        by rw [List.take_append_drop]
      rw [xy_split_nt]
      apply corresponding_strings_append; swap
      · rw [List.drop_drop]
        have part_for_v := corresponding_strings_drop (1 + u.length) ih_concat
        convert part_for_v
        have correct_len :
          1 + u.length = (u ++ [Symbol.nonterminal ◪◩t))]).length :=
          by
          rw [add_comm]
          rw [List.length_append]
          rw [List.length_singleton]
        rw [correct_len]
        rw [List.drop_left]
      · convert_to
          corresponding_strings
            [List.nthLe (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) u.length
                ul_lt_len_xy]
            [Symbol.terminal t]
        · apply list_take_one_drop
        clear * - middle_nt_elem
        apply corresponding_strings_singleton
        cases'
          (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length
            ul_lt_len_xy with
          e s
        · exfalso
          unfold corresponding_symbols at middle_nt_elem
          exact middle_nt_elem
        cases s
        · exfalso
          cases s; swap
          cases s
          all_goals
            unfold corresponding_symbols at middle_nt_elem
            exact middle_nt_elem
        · cases s
          · unfold corresponding_symbols at middle_nt_elem
            rw [middle_nt_elem]
            unfold corresponding_symbols
          · exfalso
            unfold corresponding_symbols at middle_nt_elem
            exact middle_nt_elem
    · unfold rulesForTerminals₂ at rin
      rw [List.mem_map] at rin
      rcases rin with ⟨t, -, eq_r⟩
      rw [← eq_r] at *
      clear eq_r
      rw [List.append_nil] at ih_concat
      rw [List.append_nil] at ih_concat
      have xy_split_v :
        List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y =
          List.take (u.length + 1)
              (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) ++
            List.drop (u.length + 1)
              (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) :=
        by rw [List.take_append_drop]
      rw [xy_split_v]
      have part_for_v := corresponding_strings_drop (u.length + 1) ih_concat
      apply corresponding_strings_append; swap
      · convert part_for_v
        have rewr_len : u.length + 1 = (u ++ [Symbol.nonterminal ◪◪t))]).length :=
          by
          rw [List.length_append]
          rw [List.length_singleton]
        rw [rewr_len]
        rw [List.drop_left]
      have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal ◪◪t))]).length :=
        by
        rw [List.length_append]
        rw [List.length_singleton]
        apply lt_add_one
      have ul_lt_len_umv :
        u.length < (u ++ [Symbol.nonterminal ◪◪t))] ++ v).length :=
        by
        rw [List.length_append]
        apply lt_of_lt_of_le ul_lt_len_um
        apply le_self_add
      have ul_lt_len_xy :
        u.length < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
        by
        have same_len := corresponding_strings_length ih_concat
        rw [same_len]
        exact ul_lt_len_umv
      have middle_nt := correspondingStrings_nthLe ul_lt_len_xy ul_lt_len_umv ih_concat
      rw [List.nthLe_append ul_lt_len_umv ul_lt_len_um] at middle_nt
      rw [List.nthLe_append_right (by rfl) ul_lt_len_um] at middle_nt
      have middle_nt_elem :
        corresponding_symbols
          ((List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length
            ul_lt_len_xy)
          (Symbol.nonterminal ◪◪t))) :=
        by
        convert middle_nt
        sorry
      have xy_split_nt :
        List.take (u.length + 1)
            (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) =
          List.take u.length
              (List.take (u.length + 1)
                (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)) ++
            List.drop u.length
              (List.take (u.length + 1)
                (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)) :=
        by rw [List.take_append_drop u.length]
      rw [xy_split_nt]
      apply corresponding_strings_append
      · rw [List.take_take]
        have part_for_u := corresponding_strings_take u.length ih_concat
        convert part_for_u
        · apply min_eq_left
          apply Nat.le_succ
        rw [List.append_assoc]
        rw [List.take_left]
      · convert_to
          corresponding_strings
            [List.nthLe (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) u.length
                ul_lt_len_xy]
            [Symbol.terminal t]
        · apply list_drop_take_succ
        clear * - middle_nt_elem
        apply corresponding_strings_singleton
        cases'
          (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length
            ul_lt_len_xy with
          e s
        · exfalso
          unfold corresponding_symbols at middle_nt_elem
          exact middle_nt_elem
        cases s
        · exfalso
          cases s; swap
          cases s
          all_goals
            unfold corresponding_symbols at middle_nt_elem
            exact middle_nt_elem
        · cases s
          · exfalso
            unfold corresponding_symbols at middle_nt_elem
            exact middle_nt_elem
          · unfold corresponding_symbols at middle_nt_elem
            rw [middle_nt_elem]
            unfold corresponding_symbols-/

lemma in_concatenated_of_in_big {g₁ g₂ : Grammar T} {w : List T}
    (hwgg : w ∈ (bigGrammar g₁ g₂).language) :
  w ∈ g₁.language * g₂.language :=
by
  rw [Language.mem_mul]
  cases' Grammar.eq_or_tran_deri_of_deri hwgg with case_id case_step
  · exfalso
    have nonmatch := congr_fun (congr_arg List.get? case_id) 0
    clear * - nonmatch
    unfold List.get? at nonmatch
    cases w
    · rw [List.map_nil] at nonmatch
      exact Option.noConfusion nonmatch
    · unfold List.map at nonmatch
      unfold List.get? at nonmatch
      have imposs := Option.some.inj nonmatch
      exact Symbol.noConfusion imposs
  clear hwgg
  rcases case_step with ⟨w₁, hyp_tran, hyp_deri⟩
  have w₁eq : w₁ =
      [Symbol.nonterminal ◩(some ◩g₁.initial),
       Symbol.nonterminal ◩(some ◪g₂.initial)]
  · clear * - hyp_tran
    -- only the first rule is applicable
    rcases hyp_tran with ⟨r, rin, u, v, bef, aft⟩
    have bef_len := congr_arg List.length bef
    rw [List.length_append_append, List.length_append_append,
        List.length_singleton, List.length_singleton] at bef_len
    have u_nil : u = []
    · clear * - bef_len
      rw [← List.length_eq_zero_iff]
      linarith
    have v_nil : v = []
    · clear * - bef_len
      rw [← List.length_eq_zero_iff]
      linarith
    have rif_nil : r.inputL = []
    · clear * - bef_len
      rw [← List.length_eq_zero_iff]
      linarith
    have nt_match : Symbol.nonterminal (bigGrammar g₁ g₂).initial = Symbol.nonterminal r.inputN
    · have bef_fst := congr_fun (congr_arg List.get? bef) 0
      rw [u_nil, rif_nil] at bef_fst
      rw [← Option.some_inj]
      exact bef_fst
    simp only [bigGrammar, List.mem_cons, List.mem_append, or_assoc, List.mem_map] at rin
    rcases rin with rinit | rin₁ | rin₂ | rte₁ | rte₂
    · rw [rinit] at bef aft
      dsimp only at bef aft
      rw [u_nil, v_nil] at aft
      rw [List.nil_append, List.append_nil] at aft
      exact aft
    · exfalso
      rcases rin₁ with ⟨r₀, hr₀g₁, wrap_eq_r⟩
      rw [← wrap_eq_r] at nt_match
      unfold wrapGrule₁ at nt_match
      have inl_match := Symbol.nonterminal.inj nt_match
      change Sum.inl none = Sum.inl (some ◩r₀.inputN) at inl_match
      have none_eq_some := Sum.inl.inj inl_match
      exact Option.noConfusion none_eq_some
    · exfalso
      rcases rin₂ with ⟨r₀, hr₀g₂, wrap_eq_r⟩
      rw [← wrap_eq_r] at nt_match
      unfold wrapGrule₂ at nt_match
      have inl_match := Symbol.nonterminal.inj nt_match
      change Sum.inl none = Sum.inl (some ◪r₀.inputN) at inl_match
      have none_eq_some := Sum.inl.inj inl_match
      exact Option.noConfusion none_eq_some
    · unfold rulesForTerminals₁ at rte₁
      rw [List.mem_map] at rte₁
      rcases rte₁ with ⟨t, htg₁, tt_eq_r⟩
      rw [← tt_eq_r] at nt_match
      have inl_eq_inr := Symbol.nonterminal.inj nt_match
      exact Sum.noConfusion inl_eq_inr
    · unfold rulesForTerminals₂ at rte₂
      rw [List.mem_map] at rte₂
      rcases rte₂ with ⟨t, htg₂, tt_eq_r⟩
      rw [← tt_eq_r] at nt_match
      have inl_eq_inr := Symbol.nonterminal.inj nt_match
      exact Sum.noConfusion inl_eq_inr
  clear hyp_tran
  rw [w₁eq] at hyp_deri
  have hope_result := big_induction hyp_deri
  clear * - hope_result
  rcases hope_result with ⟨x, y, deri_x, deri_y, concat_xy⟩
  use List.take x.length w
  sorry /-
  use List.drop x.length w
  constructor
  · clear deri_y
    unfold Grammar.language
    rw [Set.mem_setOf_eq]
    convert deri_x
    clear deri_x
    have xylen := correspondingStrings_length concat_xy
    rw [List.length_append] at xylen
    repeat' rw [List.length_map] at xylen
    apply List.ext_get
    · rw [List.length_map, List.length_take_of_le]
      exact le_of_add_le_left (le_of_eq xylen)
    intros i iltwl iltxl
    rw [List.get_map]
    have i_lt_lenl : i < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length
    · rw [List.length_append]
      sorry
    have i_lt_lenr : i < (List.map Symbol.terminal w).length
    · sorry
    have equivalent_ith := correspondingStrings_get i_lt_lenl i_lt_lenr concat_xy
    have asdf :
      List.get (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) ⟨i, i_lt_lenl⟩ =
      wrapSymbol₁ g₂.nt (x.get ⟨i, iltxl⟩)
    · sorry
    rw [asdf, List.get_map] at equivalent_ith
    set I : Fin x.length := ⟨i, iltxl⟩
    cases' x.get I with t n₁
    · simp [wrapSymbol₁, correspondingSymbols] at equivalent_ith
      sorry
    ext1 i
    by_cases i ≥ x.length
    · convert_to none = none
      · have xlen :
          x.length = (List.map (@Symbol.terminal T g₁.nt) (List.take x.length w)).length :=
          by
          clear * - xylen
          rw [List.length_map]
          rw [List.length_take]
          symm
          apply min_eq_left
          exact Nat.le.intro xylen
        rw [xlen] at h
        clear * - h
        rw [List.get?_eq_none]
        exact h
      · clear * - h
        rw [List.get?_eq_none]
        exact h
      rfl
    push_neg at h
    rename' h => hix
    have i_lt_len_lwx : i < (List.map (wrapSymbol₁ g₂.nt) x).length :=
      by
      rw [List.length_map]
      exact hix
    have i_lt_len_w : i < w.length :=
      by
      apply lt_of_lt_of_le hix
      exact Nat.le.intro xylen
    have i_lt_len₁ :
      i < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
      by
      rw [List.length_append]
      apply lt_of_lt_of_le i_lt_len_lwx
      apply le_self_add
    have i_lt_len₂ : i < (List.map Symbol.terminal w).length :=
      by
      rw [List.length_map]
      exact i_lt_len_w
    rw [List.get?_map]
    rw [List.get?_take hix]
    have equivalent_ith :
      corresponding_symbols
        (List.nthLe (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) i i_lt_len₁)
        (List.nthLe (List.map Symbol.terminal w) i i_lt_len₂) :=
      by
      apply correspondingStrings_nthLe
      exact concat_xy
    rw [List.nthLe_map] at equivalent_ith ; swap
    · exact i_lt_len_w
    rw [List.nthLe_append] at equivalent_ith ; swap
    · exact i_lt_len_lwx
    rw [List.nthLe_map] at equivalent_ith ; swap
    · exact hix
    clear * - equivalent_ith
    rw [List.nthLe_get? hix]
    cases' x.nth_le i hix with t n <;> unfold wrapSymbol₁ at equivalent_ith  <;>
      unfold corresponding_symbols at equivalent_ith
    · have symbol_ith := congr_arg (@Symbol.terminal T g₁.nt) equivalent_ith
      rw [List.nthLe_get? i_lt_len_w]
      rw [Option.map_some']
      exact congr_arg Option.some symbol_ith
    · exfalso
      exact equivalent_ith
  constructor
  · clear deri_x
    unfold Grammar.language
    rw [Set.mem_setOf_eq]
    convert deri_y
    clear deri_y
    have xylen := correspondingStrings_length concat_xy
    rw [List.length_append] at xylen
    repeat' rw [List.length_map] at xylen
    sorry /-ext1 i
    by_cases i ≥ y.length
    · convert_to none = none
      · have ylen :
          y.length = (List.map (@Symbol.terminal T g₁.nt) (List.drop x.length w)).length :=
          by
          clear * - xylen
          rw [List.length_map]
          rw [List.length_drop]
          sorry
        rw [ylen] at h
        clear * - h
        rw [List.get?_eq_none]
        rw [List.length_map] at *
        exact h
      · clear * - h
        rw [List.get?_eq_none]
        exact h
      rfl
    push_neg at h
    rename' h => hiy
    rw [←
      List.take_append_drop (List.map (wrapSymbol₁ g₂.nt) x).length (List.map Symbol.terminal w)] at
      concat_xy
    rw [List.get?_map]
    have equivalent_second_parts :
      corresponding_strings (List.map (wrapSymbol₂ g₁.nt) y)
        (List.drop (List.map (wrapSymbol₁ g₂.nt) x).length (List.map Symbol.terminal w)) :=
      by
      have llen_eq_llen :
        (List.map (wrapSymbol₁ g₂.nt) x).length =
          (List.take (List.map (wrapSymbol₁ g₂.nt) x).length (List.map Symbol.terminal w)).length :=
        by
        rw [List.length_take]
        symm
        apply min_eq_left
        rw [List.length_map]
        rw [List.length_map]
        exact Nat.le.intro xylen
      convert corresponding_strings_drop (List.map (wrapSymbol₁ g₂.nt) x).length concat_xy
      · rw [List.drop_left]
      · rw [List.take_append_drop]
      exact T
    clear concat_xy
    symm
    have i_lt_len_lwy : i < (List.map (wrapSymbol₂ g₁.nt) y).length :=
      by
      rw [List.length_map]
      exact hiy
    have i_lt_len_dxw : i < (List.drop x.length (List.map Symbol.terminal w)).length :=
      by
      rw [List.length_drop]
      rw [List.length_map]
      rw [← xylen]
      convert i_lt_len_lwy
      rw [List.length_map]
      rw [add_comm]
      rw [Nat.add_sub_assoc]
      rw [Nat.sub_self]
      rw [Nat.add_zero]
      rfl
    have i_lt_len_mtw : i < (List.map Symbol.terminal (List.drop x.length w)).length :=
      by
      convert i_lt_len_dxw
      apply List.map_drop
    have i_lt_len_dlmxw :
      i < (List.drop (List.map (wrapSymbol₁ g₂.nt) x).length (List.map Symbol.terminal w)).length :=
      by
      rw [List.length_map]
      -- DO NOT call `i_lt_len_dxw` even though it looks like a good idea!
      rw [List.length_drop]
      rw [List.length_map]
      rw [← xylen]
      convert i_lt_len_lwy
      rw [List.length_map]
      rw [add_comm]
      rw [Nat.add_sub_assoc]
      rw [Nat.sub_self]
      rw [Nat.add_zero]
      rfl
    have eqiv_symb :=
      correspondingStrings_nthLe i_lt_len_lwy i_lt_len_dlmxw equivalent_second_parts
    have goal_as_ith_drop :
      y.nth_le i hiy =
        (List.drop x.length (List.map Symbol.terminal w)).nthLe i i_lt_len_dxw :=
      by
      have xli_lt_len_w : x.length + i < w.length :=
        by
        clear * - hiy xylen
        linarith
      rw [List.nthLe_map _ _ hiy] at eqiv_symb
      rw [List.nthLe_drop'] at *
      rw [List.nthLe_map]; swap
      · exact xli_lt_len_w
      rw [List.nthLe_map] at eqiv_symb ; swap
      · rw [List.length_map]
        exact xli_lt_len_w
      clear * - eqiv_symb
      cases' y.nth_le i hiy with t n
      · unfold wrapSymbol₂ at eqiv_symb
        unfold corresponding_symbols at eqiv_symb
        have eq_symb := congr_arg Symbol.terminal eqiv_symb
        rw [← eq_symb]
        apply congr_arg Symbol.terminal
        simp only [List.length_map]
      · exfalso
        unfold wrapSymbol₂ at eqiv_symb
        unfold corresponding_symbols at eqiv_symb
        exact eqiv_symb
    have goal_as_some_ith :
      some (y.nth_le i hiy) =
        some ((List.map Symbol.terminal (List.drop x.length w)).nthLe i i_lt_len_mtw) :=
      by
      rw [goal_as_ith_drop]
      clear * -
      congr
      rw [List.map_drop]
    clear * - goal_as_some_ith
    rw [← List.nthLe_get? hiy] at goal_as_some_ith
    rw [← List.nthLe_get? i_lt_len_mtw] at goal_as_some_ith
    convert goal_as_some_ith
    rw [List.get?_map]-/
  apply List.take_append_drop-/

end very_complicated

end hard_direction


/-- The class of grammar-generated languages is closed under concatenation. -/
theorem GG_of_GG_c_GG (L₁ : Language T) (L₂ : Language T) :
  L₁.IsGG ∧ L₂.IsGG → (L₁ * L₂).IsGG :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  use bigGrammar g₁ g₂
  apply Set.eq_of_subset_of_subset
  · -- prove `L₁ * L₂ ⊇` here
    intro w hyp
    rw [← eq_L₁]
    rw [← eq_L₂]
    exact in_concatenated_of_in_big hyp
  · -- prove `L₁ * L₂ ⊆` here
    intro w hyp
    rw [← eq_L₁] at hyp
    rw [← eq_L₂] at hyp
    exact in_big_of_in_concatenated hyp

#print axioms GG_of_GG_c_GG
