import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.ListUtils
import Mathlib.Tactic.Linarith


section ListTechnicalities

variable {α β : Type}

lemma list_take_one_drop {l : List α} {i : ℕ} (hil : i < l.length) :
  List.take 1 (List.drop i l) = [l.get ⟨i, hil⟩] :=
by
  have l_split : l = List.take i l ++ List.drop i l := by rw [List.take_append_drop]
  rw [List.get_of_eq l_split]
  rw [List.get_append_right]
  sorry
  · dsimp only
    push_neg
    apply List.length_take_le
  · sorry

lemma list_drop_take_succ {l : List α} {i : ℕ} (hil : i < l.length) :
  List.drop i (List.take (i + 1) l) = [l.get ⟨i, hil⟩] :=
by
  rw [List.drop_take]
  apply list_take_one_drop

lemma list_forall₂_get {R : α → β → Prop} :
  ∀ {x : List α}, ∀ {y : List β},
      List.Forall₂ R x y → ∀ {i : ℕ}, ∀ i_lt_len_x : i < x.length, ∀ i_lt_len_y : i < y.length,
        R (x.get ⟨i, i_lt_len_x⟩) (y.get ⟨i, i_lt_len_y⟩)
| [], [] => by intro _ i hx; exfalso; apply Nat.not_lt_zero; exact hx
| [], a₂::l₂ => by intro hyp; exfalso; cases hyp
| a₁::l₁, [] => by intro hyp; exfalso; cases hyp
| a₁::l₁, a₂::l₂ => by
    intro ass i i_lt_len_x i_lt_len_y
    rw [List.forall₂_cons] at ass 
    cases i
    · unfold List.get
      exact ass.1
    unfold List.get
    apply list_forall₂_get
    exact ass.2

lemma list_filterMap_eq_of_map_eq_map_some {f : α → Option β} :
  ∀ {x : List α}, ∀ {y : List β},
    List.map f x = List.map Option.some y →
      List.filterMap f x = y
| [], [] => fun _ => rfl
| a₁::l₁, [] => by intro hyp; exfalso; apply List.cons_ne_nil; exact hyp
| [], a₂::l₂ => by intro hyp; exfalso; apply List.cons_ne_nil; exact hyp.symm
| a₁::l₁, a₂::l₂ => by
    intro ass
    rw [List.map] at ass 
    rw [List.map] at ass 
    sorry

end ListTechnicalities


-- new nonterminal type
def nnn (T N₁ N₂ : Type) : Type :=
  Sum (Option (Sum N₁ N₂)) (Sum T T)

-- new symbol type
def nst (T N₁ N₂ : Type) : Type :=
  Symbol T (nnn T N₁ N₂)

variable {T : Type}

section TheConstruction

def wrapSymbol₁ {N₁ : Type} (N₂ : Type) : Symbol T N₁ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr (Sum.inl t))
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl (some (Sum.inl n)))

def wrapSymbol₂ {N₂ : Type} (N₁ : Type) : Symbol T N₂ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal (Sum.inr (Sum.inr t))
  | Symbol.nonterminal n => Symbol.nonterminal (Sum.inl (some (Sum.inr n)))

private def wrapGrule₁ {N₁ : Type} (N₂ : Type) (r : Grule T N₁) : Grule T (nnn T N₁ N₂) :=
  Grule.mk (List.map (wrapSymbol₁ N₂) r.inputL) (Sum.inl (some (Sum.inl r.inputN)))
    (List.map (wrapSymbol₁ N₂) r.inputR) (List.map (wrapSymbol₁ N₂) r.outputString)

private def wrapGrule₂ {N₂ : Type} (N₁ : Type) (r : Grule T N₂) : Grule T (nnn T N₁ N₂) :=
  Grule.mk (List.map (wrapSymbol₂ N₁) r.inputL) (Sum.inl (some (Sum.inr r.inputN)))
    (List.map (wrapSymbol₂ N₁) r.inputR) (List.map (wrapSymbol₂ N₁) r.outputString)

def rulesForTerminals₁ (N₂ : Type) (g : Grammar T) : List (Grule T (nnn T g.nt N₂)) :=
  List.map (fun t => Grule.mk [] (Sum.inr (Sum.inl t)) [] [Symbol.terminal t]) (allUsedTerminals g)

def rulesForTerminals₂ (N₁ : Type) (g : Grammar T) : List (Grule T (nnn T N₁ g.nt)) :=
  List.map (fun t => Grule.mk [] (Sum.inr (Sum.inr t)) [] [Symbol.terminal t]) (allUsedTerminals g)


-- the grammar for concatenation of `g₁` and `g₂` languages
def bigGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (nnn T g₁.nt g₂.nt) (Sum.inl none) (
    @Grule.mk T (nnn T g₁.nt g₂.nt) [] (Sum.inl none) [] [
      Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
      Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] ::
    List.map (wrapGrule₁ g₂.nt) g₁.rules ++
    List.map (wrapGrule₂ g₁.nt) g₂.rules ++
    (rulesForTerminals₁ g₂.nt g₁ ++ rulesForTerminals₂ g₁.nt g₂))

end TheConstruction


section EasyDirection

lemma grammar_generates_only_legit_terminals {g : Grammar T} {w : List (Symbol T g.nt)}
    (ass : g.Derives [Symbol.nonterminal g.initial] w)
    (s : Symbol T g.nt) (symbol_derived : s ∈ w) :
  (∃ r : Grule T g.nt, r ∈ g.rules ∧ s ∈ r.outputString) ∨ (s = Symbol.nonterminal g.initial) :=
by
  induction' ass with x y _ orig ih
  · rw [List.mem_singleton] at symbol_derived 
    right
    exact symbol_derived
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  rw [aft] at symbol_derived 
  rw [List.mem_append] at symbol_derived 
  rw [List.mem_append] at symbol_derived 
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
    constructor
    · exact rin
    · exact s_in_out
  · apply ih
    rw [bef]
    rw [List.mem_append]
    right
    exact s_in_v

private lemma first_transformation {g₁ g₂ : Grammar T} :
  (bigGrammar g₁ g₂).Transforms
    [Symbol.nonterminal (bigGrammar g₁ g₂).initial]
    [Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
     Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] :=
by
  use (bigGrammar g₁ g₂).rules.get ⟨0, by simp [bigGrammar]⟩
  constructor
  · simp [bigGrammar]
  use [], []
  constructor
  · rfl
  · rfl

private lemma substitute_terminals {g₁ g₂ : Grammar T} {side : T → Sum T T} {w : List T}
  (rule_for_each_terminal : ∀ t ∈ w,
      Grule.mk [] (Sum.inr (side t)) [] [Symbol.terminal t] ∈
        rulesForTerminals₁ g₂.nt g₁ ++ rulesForTerminals₂ g₁.nt g₂) :
  (bigGrammar g₁ g₂).Derives
    (List.map (Symbol.nonterminal ∘ Sum.inr ∘ side) w)
    (List.map Symbol.terminal w) :=
by
  induction' w with d l ih
  · apply Grammar.deri_self
  rw [List.map_cons, List.map_cons, ← List.singleton_append, ← List.singleton_append]
  have step_head :
    (bigGrammar g₁ g₂).Transforms
      ([(Symbol.nonterminal ∘ Sum.inr ∘ side) d] ++
        List.map (Symbol.nonterminal ∘ Sum.inr ∘ side) l)
      ([Symbol.terminal d] ++ List.map (Symbol.nonterminal ∘ Sum.inr ∘ side) l)
  · use Grule.mk [] (Sum.inr (side d)) [] [Symbol.terminal d]
    constructor
    · change _ ∈ List.cons _ _
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      apply rule_for_each_terminal
      apply List.mem_cons_self
    use [], List.map (Symbol.nonterminal ∘ Sum.inr ∘ side) l
    constructor <;> rfl
  apply Grammar.deri_of_tran_deri step_head
  apply Grammar.deri_with_prefix
  apply ih
  · intro t tin
    apply rule_for_each_terminal t
    exact List.mem_cons_of_mem d tin

lemma in_big_of_in_concatenated {g₁ g₂ : Grammar T} {w : List T}
    (ass : w ∈ g₁.Language * g₂.Language) :
  w ∈ (bigGrammar g₁ g₂).Language :=
by
  rw [Language.mem_mul] at ass 
  rcases ass with ⟨u, v, hu, hv, hw⟩
  unfold Grammar.Language at *
  rw [Set.mem_setOf_eq] at *
  unfold Grammar.Generates at *
  apply Grammar.deri_of_tran_deri first_transformation
  rw [← hw]
  rw [List.map_append]
  apply
    (bigGrammar g₁ g₂).deri_of_deri_deri
      (v := List.map Symbol.terminal u ++ [Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))])
  · clear * - hu
    rw [← List.singleton_append]
    apply Grammar.deri_with_postfix
    apply
      (bigGrammar g₁ g₂).deri_of_deri_deri
        (v := List.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inl) u)
    · have upgrade_deri₁ :
        ∀ w : List (Symbol T g₁.nt),
          g₁.Derives [Symbol.nonterminal g₁.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial)))]
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
          constructor
          · exact rin
          · rfl
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
          r ∈ g₁.rules ∧ Symbol.terminal t ∈ r.outputString
      · intro t tin
        have legit := grammar_generates_only_legit_terminals hu (Symbol.terminal t) (by
          rw [List.mem_map]
          use t
          constructor
          · exact tin
          · rfl
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
          · rw [List.mem_join]
            obtain ⟨r, rin, sttin⟩ := legit_terminals₁ t tin
            use r.outputString
            constructor
            · apply List.mem_map_of_mem
              exact rin
            · exact sttin
          · rfl
        · rfl
  · clear * - hv
    apply Grammar.deri_with_prefix
    apply
      @Grammar.deri_of_deri_deri _ _ _
        (List.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inr) v) _
    · have upgrade_deri₂ :
        ∀ w : List (Symbol T g₂.nt),
          g₂.Derives [Symbol.nonterminal g₂.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
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
              _::List.map (wrapGrule₁ g₂.nt) g₁.rules ++ List.map (wrapGrule₂ g₁.nt) g₂.rules ++ _
          apply List.mem_cons_of_mem
          apply List.mem_append_left
          apply List.mem_append_right
          rw [List.mem_map]
          use r
          constructor
          · exact rin
          · rfl
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
          r ∈ g₂.rules ∧ Symbol.terminal t ∈ r.outputString
      · intro t tin
        have legit := grammar_generates_only_legit_terminals hv (Symbol.terminal t) (by
          rw [List.mem_map]
          use t
          constructor
          · exact tin
          · rfl
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
          · rw [List.mem_join]
            obtain ⟨r, rin, sttin⟩ := legit_terminals₂ t tin
            use r.outputString
            constructor
            · apply List.mem_map_of_mem
              exact rin
            · exact sttin
          · rfl
        · rfl

end EasyDirection


section HardDirection

section CorrespondenceForTerminals

private def correspondingSymbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
  | Symbol.terminal t
  , Symbol.terminal t' =>
      t = t'
  | Symbol.nonterminal (Sum.inr (Sum.inl a))
  , Symbol.nonterminal (Sum.inr (Sum.inl a')) =>
      a = a'
  | Symbol.nonterminal (Sum.inr (Sum.inr a))
  , Symbol.nonterminal (Sum.inr (Sum.inr a')) =>
      a = a'
  | Symbol.nonterminal (Sum.inr (Sum.inl a))
  , Symbol.terminal t =>
      t = a
  | Symbol.nonterminal (Sum.inr (Sum.inr a))
  , Symbol.terminal t =>
      t = a
  | Symbol.nonterminal (Sum.inl (some (Sum.inl n)))
  , Symbol.nonterminal (Sum.inl (some (Sum.inl n'))) =>
      n = n'
  | Symbol.nonterminal (Sum.inl (some (Sum.inr n)))
  , Symbol.nonterminal (Sum.inl (some (Sum.inr n'))) =>
      n = n'
  | Symbol.nonterminal (Sum.inl none)
  , Symbol.nonterminal (Sum.inl none) =>
      True
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
  cases s₁ <;> cases s₂ <;>
    · unfold wrapSymbol₁
      unfold wrapSymbol₂
      unfold correspondingSymbols
      exact not_false

private lemma correspondingSymbols_never₂ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s₂ : Symbol T N₂} :
  ¬ correspondingSymbols (wrapSymbol₂ N₁ s₂) (wrapSymbol₁ N₂ s₁) :=
by
  cases s₁ <;> cases s₂ <;>
    · unfold wrapSymbol₁
      unfold wrapSymbol₂
      unfold correspondingSymbols
      exact not_false


private def correspondingStrings {N₁ N₂ : Type} : List (nst T N₁ N₂) → List (nst T N₁ N₂) → Prop :=
  List.Forall₂ correspondingSymbols

private lemma correspondingStrings_self {N₁ N₂ : Type} {x : List (nst T N₁ N₂)} :
  correspondingStrings x x :=
by
  unfold correspondingStrings
  rw [List.forall₂_same]
  intros s _
  exact correspondingSymbols_self s

private lemma correspondingStrings_cons {N₁ N₂ : Type} {d₁ d₂ : nst T N₁ N₂} {l₁ l₂ : List (nst T N₁ N₂)} :
  correspondingStrings (d₁::l₁) (d₂::l₂)  ↔  correspondingSymbols d₁ d₂  ∧  correspondingStrings l₁ l₂  :=
by
  apply List.forall₂_cons

private lemma correspondingStrings_singleton {N₁ N₂ : Type} {s₁ s₂ : nst T N₁ N₂}
    (ass : correspondingSymbols s₁ s₂) :
  correspondingStrings [s₁] [s₂] :=
by
  rw [correspondingStrings_cons]
  constructor
  · exact ass
  · exact List.Forall₂.nil

private lemma correspondingStrings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : List (nst T N₁ N₂)}
    (ass₁ : correspondingStrings x₁ y₁) (ass₂ : correspondingStrings x₂ y₂) :
  correspondingStrings (x₁ ++ x₂) (y₁ ++ y₂) :=
by
  unfold correspondingStrings at *
  exact List.rel_append ass₁ ass₂

private lemma correspondingStrings_length {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : correspondingStrings x y) :
  x.length = y.length :=
by
  unfold correspondingStrings at ass 
  exact List.Forall₂.length_eq ass

private lemma correspondingStrings_get {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} {i : ℕ}
    (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length) (ass : correspondingStrings x y) :
  correspondingSymbols (x.get ⟨i, i_lt_len_x⟩) (y.get ⟨i, i_lt_len_y⟩) :=
by
  apply list_forall₂_get
  exact ass

private lemma correspondingStrings_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : correspondingStrings x y) :
  correspondingStrings x.reverse y.reverse :=
by
  unfold correspondingStrings at *
  rw [List.forall₂_reverse_iff]
  exact ass

private lemma correspondingStrings_of_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : correspondingStrings x.reverse y.reverse) :
  correspondingStrings x y :=
by
  unfold correspondingStrings at *
  rw [List.forall₂_reverse_iff] at ass 
  exact ass

private lemma correspondingStrings_take {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} (n : ℕ)
    (ass : correspondingStrings x y) :
  correspondingStrings (List.take n x) (List.take n y) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_take n ass

private lemma correspondingStrings_drop {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} (n : ℕ)
    (ass : correspondingStrings x y) :
  correspondingStrings (List.drop n x) (List.drop n y) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_drop n ass

private lemma correspondingStrings_split {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} (n : ℕ)
    (ass : correspondingStrings x y) :
  correspondingStrings (List.take n x) (List.take n y) ∧
  correspondingStrings (List.drop n x) (List.drop n y) :=
by
  constructor
  · exact correspondingStrings_take n ass
  · exact correspondingStrings_drop n ass

end CorrespondenceForTerminals

section UnwrappingNst

private def unwrapSymbol₁ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₁)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal (Sum.inr (Sum.inl a)) => some (Symbol.terminal a)
  | Symbol.nonterminal (Sum.inr (Sum.inr _)) => none
  | Symbol.nonterminal (Sum.inl (some (Sum.inl n))) => some (Symbol.nonterminal n)
  | Symbol.nonterminal (Sum.inl (some (Sum.inr _))) => none
  | Symbol.nonterminal (Sum.inl none) => none

private def unwrapSymbol₂ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₂)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal (Sum.inr (Sum.inl _)) => none
  | Symbol.nonterminal (Sum.inr (Sum.inr a)) => some (Symbol.terminal a)
  | Symbol.nonterminal (Sum.inl (some (Sum.inl _))) => none
  | Symbol.nonterminal (Sum.inl (some (Sum.inr n))) => some (Symbol.nonterminal n)
  | Symbol.nonterminal (Sum.inl none) => none

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
  List.filterMap unwrapSymbol₁ (List.map (wrapSymbol₁ N₂) w) = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₁_symbol]
  apply List.filterMap_some

private lemma unwrap_wrap₂_string {N₁ N₂ : Type} {w : List (Symbol T N₂)} :
  List.filterMap unwrapSymbol₂ (List.map (wrapSymbol₂ N₁) w) = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₂_symbol]
  apply List.filterMap_some

private lemma unwrap_eq_some_of_correspondingSymbols₁ {N₁ N₂ : Type} {s₁ : Symbol T N₁}
    {s : nst T N₁ N₂} (ass : correspondingSymbols (wrapSymbol₁ N₂ s₁) s) :
  unwrapSymbol₁ s = some s₁ :=
by
  cases' s₁ with t₁ n₁
  · cases' s with t n
    · rw [show t = t₁ by convert ass]
      rfl
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₁, correspondingSymbols] at ass
        · simp [wrapSymbol₁, correspondingSymbols] at ass
      · cases' t with t' t''
        · rw [show t₁ = t' by convert ass]
          rfl
        · simp [wrapSymbol₁, correspondingSymbols] at ass
  · cases' s with t n
    · simp [wrapSymbol₁, correspondingSymbols] at ass
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₁, correspondingSymbols] at ass
        · cases' n' with n'₁ n'₂
          · rw [show n₁ = n'₁ by convert ass]
            rfl
          · simp [wrapSymbol₁, correspondingSymbols] at ass
      · cases' t with t' t''
        · simp [wrapSymbol₁, correspondingSymbols] at ass
        · simp [wrapSymbol₁, correspondingSymbols] at ass

private lemma unwrap_eq_some_of_correspondingSymbols₂ {N₁ N₂ : Type} {s₂ : Symbol T N₂}
    {s : nst T N₁ N₂} (ass : correspondingSymbols (wrapSymbol₂ N₁ s₂) s) :
  unwrapSymbol₂ s = some s₂ :=
by
  cases' s₂ with t₂ n₂
  · cases' s with t n
    · rw [show t = t₂ by convert ass]
      rfl
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₂, correspondingSymbols] at ass
        · simp [wrapSymbol₂, correspondingSymbols] at ass
      · cases' t with t' t''
        · simp [wrapSymbol₂, correspondingSymbols] at ass
        · rw [show t₂ = t'' by convert ass]
          rfl
  · cases' s with t n
    · simp [wrapSymbol₂, correspondingSymbols] at ass
    · cases' n with o t
      · cases' o with n'
        · simp [wrapSymbol₂, correspondingSymbols] at ass
        · cases' n' with n'₁ n'₂
          · simp [wrapSymbol₂, correspondingSymbols] at ass
          · rw [show n₂ = n'₂ by convert ass]
            rfl
      · cases' t with t' t''
        · simp [wrapSymbol₂, correspondingSymbols] at ass
        · simp [wrapSymbol₂, correspondingSymbols] at ass

private lemma map_unwrap_eq_map_some_of_correspondingStrings₁ {N₁ N₂ : Type} :
  ∀ {v : List (Symbol T N₁)}, ∀ {w : List (nst T N₁ N₂)},
    correspondingStrings (List.map (wrapSymbol₁ N₂) v) w →
      List.map unwrapSymbol₁ w = List.map Option.some v
  | [], [] => by
      intro _
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      intro hyp
      exfalso
      simp [correspondingStrings] at hyp
  | a::x, [] => by 
      intro hyp
      exfalso
      simp [correspondingStrings] at hyp
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass 
      rw [List.map_cons, List.forall₂_cons] at ass 
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₁ ass.1
      · apply map_unwrap_eq_map_some_of_correspondingStrings₁
        exact ass.2

private lemma map_unwrap_eq_map_some_of_correspondingStrings₂ {N₁ N₂ : Type} :
  ∀ {v : List (Symbol T N₂)}, ∀ {w : List (nst T N₁ N₂)},
    correspondingStrings (List.map (wrapSymbol₂ N₁) v) w →
      List.map unwrapSymbol₂ w = List.map Option.some v
  | [], [] => by
      intro _
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      intro hyp
      exfalso
      simp [correspondingStrings] at hyp
  | a::x, [] => by 
      intro hyp
      exfalso
      simp [correspondingStrings] at hyp
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass 
      rw [List.map_cons, List.forall₂_cons] at ass 
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₂ ass.1
      · apply map_unwrap_eq_map_some_of_correspondingStrings₂
        exact ass.2

private lemma filterMap_unwrap_of_correspondingStrings₁ {N₁ N₂ : Type} {v : List (Symbol T N₁)}
    {w : List (nst T N₁ N₂)} (ass : correspondingStrings (List.map (wrapSymbol₁ N₂) v) w) :
  List.filterMap unwrapSymbol₁ w = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  exact map_unwrap_eq_map_some_of_correspondingStrings₁ ass

private lemma filterMap_unwrap_of_correspondingStrings₂ {N₁ N₂ : Type} {v : List (Symbol T N₂)}
    {w : List (nst T N₁ N₂)} (ass : correspondingStrings (List.map (wrapSymbol₂ N₁) v) w) :
  List.filterMap unwrapSymbol₂ w = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  exact map_unwrap_eq_map_some_of_correspondingStrings₂ ass

private lemma correspondingStrings_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (Symbol T N₁), correspondingStrings (List.map (wrapSymbol₁ N₂) z) w) :
  correspondingStrings (List.map (wrapSymbol₁ N₂) (List.filterMap unwrapSymbol₁ w)) w :=
by
  induction' w with d l ih
  · unfold correspondingStrings
    unfold List.filterMap
    unfold List.map
    exact List.Forall₂.nil
  specialize ih (by
    cases' ass with z hyp
    cases' z with z₀ z'
    · exfalso
      simp [correspondingStrings, wrapSymbol₁] at hyp
    · use z'
      rw [List.map_cons, correspondingStrings_cons] at hyp
      exact hyp.2
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
  cases' n with o t' -- probably throw away from here down
  · cases' o with n'
    · sorry
    · sorry
  rw [List.map_filterMap]
  convert_to
    correspondingStrings
      (List.filterMap Option.some (Symbol.nonterminal (Sum.inr t') :: l))
      (Symbol.nonterminal (Sum.inr t') :: l)
  · congr
    ext1 a
    cases' a with t n
    · sorry
    · sorry
  rw [List.filterMap_some]
  apply correspondingStrings_self
  /-cases' n with ? ??
  cases d; swap
  cases d
  · have unwrap_first_nlsl :
      List.filterMap unwrap_symbol₁ (Symbol.nonterminal (Sum.inl (some (Sum.inl d)))::l) =
        Symbol.nonterminal d::List.filterMap unwrap_symbol₁ l :=
      by rfl
    rw [unwrap_first_nlsl]
    unfold List.map
    unfold wrapSymbol₁
    rw [List.forall₂_cons] -- correspondingStrings_cons
    constructor
    · unfold corresponding_symbols
    · exact ih
  pick_goal 3
  cases d
  · have unwrap_first_nrl :
      List.filterMap unwrap_symbol₁ (Symbol.nonterminal (Sum.inr (Sum.inl d))::l) =
        Symbol.terminal d::List.filterMap unwrap_symbol₁ l :=
      by rfl
    rw [unwrap_first_nrl]
    unfold List.map
    unfold wrapSymbol₁
    rw [List.forall₂_cons] -- correspondingStrings_cons
    constructor
    · unfold corresponding_symbols
    · exact ih
  any_goals
    exfalso
    cases' ass with z hyp
    cases' z with z₀ z'
    · have imposs := correspondingStrings_length hyp
      clear * - imposs
      rw [List.length] at imposs 
      rw [List.length_map] at imposs 
      rw [List.length] at imposs 
      linarith
    · rw [List.map_cons] at hyp 
      unfold corresponding_strings at hyp 
      rw [List.forall₂_cons] at hyp -- correspondingStrings_cons
      have impos := hyp.left
      clear * - impos
      cases z₀ <;>
        · unfold wrapSymbol₁ at impos 
          unfold corresponding_symbols at impos 
          exact impos-/

private lemma correspondingStrings_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (Symbol T N₂), correspondingStrings (List.map (wrapSymbol₂ N₁) z) w) :
  correspondingStrings (List.map (wrapSymbol₂ N₁) (List.filterMap unwrapSymbol₂ w)) w :=
by sorry
/-induction' w with d l ih
  · unfold corresponding_strings
    unfold List.filterMap
    unfold List.map
    exact List.Forall₂.nil
  specialize
    ih
      (by
        cases' ass with z hyp
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
      List.filterMap unwrap_symbol₂ (Symbol.nonterminal (Sum.inl (some (Sum.inr d)))::l) =
        Symbol.nonterminal d::List.filterMap unwrap_symbol₂ l :=
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
      List.filterMap unwrap_symbol₂ (Symbol.nonterminal (Sum.inr (Sum.inr d))::l) =
        Symbol.terminal d::List.filterMap unwrap_symbol₂ l :=
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
    cases' ass with z hyp
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

end UnwrappingNst

section VeryComplicated

/-private lemma induction_step_for_lifted_rule_from_g₁ {g₁ g₂ : Grammar T}
    {a b u v : List (Nst T g₁.Nt g₂.Nt)} {x : List (Symbol T g₁.Nt)} {y : List (Symbol T g₂.Nt)}
    {r : Grule T (Nnn T g₁.Nt g₂.Nt)} (rin : r ∈ List.map (wrapGrule₁ g₂.Nt) g₁.rules)
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.outputString ++ v)
    (ih_x : GrammarDerives g₁ [Symbol.nonterminal g₁.initial] x)
    (ih_y : GrammarDerives g₂ [Symbol.nonterminal g₂.initial] y)
    (ih_concat :
      CorrespondingStrings (List.map (wrapSymbol₁ g₂.Nt) x ++ List.map (wrapSymbol₂ g₁.Nt) y) a) :
    ∃ x' : List (Symbol T g₁.Nt),
      And
        (And (GrammarDerives g₁ [Symbol.nonterminal g₁.initial] x')
          (GrammarDerives g₂ [Symbol.nonterminal g₂.initial] y))
        (CorrespondingStrings (List.map (wrapSymbol₁ g₂.Nt) x' ++ List.map (wrapSymbol₂ g₁.Nt) y)
          b) :=
  by
  rw [List.mem_map] at rin 
  rcases rin with ⟨r₁, rin₁, wrap_r₁_eq_r⟩
  rw [← wrap_r₁_eq_r] at *
  clear wrap_r₁_eq_r
  simp [wrap_grule₁] at *
  rw [← List.singleton_append] at bef 
  let m :=
    (List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1 +
      (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length
  let b' :=
    u ++ List.map (wrapSymbol₁ g₂.nt) r₁.output_string ++ List.take (x.length - u.length - m) v
  use List.filterMap unwrap_symbol₁ b'
  have critical :
    (List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1 +
        (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length ≤
      x.length - u.length :=
    by
    clear * - ih_concat bef
    have as_positive :
      u.length +
          ((List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1 +
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length) ≤
        x.length :=
      by
      by_contra contra
      push_neg at contra 
      rw [bef] at ih_concat 
      clear bef
      repeat' rw [← List.append_assoc] at ih_concat 
      have len_pos :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
              List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length >
          0 :=
        by
        repeat' rw [List.length_append]
        rw [List.length_singleton]
        clear * -
        linarith
      have equal_total_len := corresponding_strings_length ih_concat
      have inequality_m1 :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length -
            1 <
          (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
              List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length :=
        Buffer.lt_aux_2 len_pos
      have inequality_cat :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length -
            1 <
          (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R ++
              v).length :=
        by
        rw [List.length_append _ v]
        apply lt_of_lt_of_le (Buffer.lt_aux_2 len_pos)
        exact le_self_add
      have inequality_map :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length -
            1 <
          (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
        by
        rw [equal_total_len]
        exact inequality_cat
      have inequality_map_opp :
        (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length -
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
      have clash := correspondingStrings_nthLe inequality_map inequality_cat ih_concat
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
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))]).length -
              1 <
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))]).length :=
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
        exact corresponding_symbols_never₂ clash
    omega
  constructor
  · constructor
    · apply Grammar.deri_of_deri_tran ih_x
      use r₁
      constructor
      · exact rin₁
      use List.filterMap unwrap_symbol₁ u
      use List.filterMap unwrap_symbol₁ (List.take (x.length - u.length - m) v)
      constructor
      · have x_equiv :
          corresponding_strings (List.map (wrapSymbol₁ g₂.nt) x)
            (List.take x.length
              (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                    [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                  List.map (wrapSymbol₁ g₂.nt) r₁.input_R ++
                v)) :=
          by
          rw [bef] at ih_concat 
          clear * - ih_concat
          rw [← List.append_assoc _ _ v] at ih_concat 
          rw [← List.append_assoc _ _ v] at ih_concat 
          rw [List.append_assoc u]
          rw [List.append_assoc u]
          rw [List.append_assoc u]
          rw [List.append_assoc (List.map (wrapSymbol₁ g₂.nt) r₁.input_L)]
          convert corresponding_strings_take x.length ih_concat
          · have x_len_eq : x.length = (List.map (wrapSymbol₁ g₂.nt) x).length := by
              rw [List.length_map]
            rw [x_len_eq]
            rw [List.take_left]
        clear * - x_equiv critical
        have ul_le_xl : u.length ≤ x.length :=
          by
          clear * - critical
          have weaker_le : 1 ≤ x.length - u.length := by omega
          have stupid_le : u.length + 1 ≤ x.length := by omega
          exact Nat.le_of_succ_le stupid_le
        repeat' rw [List.take_append_eq_append_take] at x_equiv 
        rw [List.take_all_of_le ul_le_xl] at x_equiv 
        repeat' rw [List.append_assoc]
        have chunk2 :
          List.take (x.length - u.length) (List.map (wrapSymbol₁ g₂.nt) r₁.input_L) =
            List.map (wrapSymbol₁ g₂.nt) r₁.input_L :=
          by
          apply List.take_all_of_le
          clear * - critical
          omega
        have chunk3 :
          List.take (x.length - (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length)
              [@Symbol.nonterminal T (Nnn T g₁.nt g₂.nt) (Sum.inl (some (Sum.inl r₁.input_N)))] =
            [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] :=
          by
          apply List.take_all_of_le
          clear * - critical
          change 1 ≤ x.length - (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length
          rw [List.length_append]
          have weakened :
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1 ≤ x.length - u.length := by omega
          have goal_as_le_sub_sub :
            1 ≤ x.length - u.length - (List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length := by omega
          rw [tsub_add_eq_tsub_tsub]
          exact goal_as_le_sub_sub
        have chunk4 :
          List.take
              (x.length -
                (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                    [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))]).length)
              (List.map (wrapSymbol₁ g₂.nt) r₁.input_R) =
            List.map (wrapSymbol₁ g₂.nt) r₁.input_R :=
          by
          apply List.take_all_of_le
          clear * - critical
          rw [List.length_append_append]
          change
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length ≤
              x.length - (u.length + (List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1)
          omega
        have chunk5 :
          List.take
              (x.length -
                (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                      [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                    List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length)
              v =
            List.take (x.length - u.length - m) v :=
          by
          repeat' rw [List.length_append]
          apply congr_arg₂; swap
          · rfl
          have rearrange_sum_of_four : ∀ a b c d : ℕ, a + b + c + d = a + (b + c + d) := by omega
          rw [rearrange_sum_of_four]
          change x.length - (u.length + m) = x.length - u.length - m
          clear * -
          omega
        rw [chunk2, chunk3, chunk4, chunk5] at x_equiv 
        clear chunk2 chunk3 chunk4 chunk5
        obtain ⟨temp_5, equiv_segment_5⟩ :=
          corresponding_strings_split
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                  [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
                List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length
            x_equiv
        clear x_equiv
        rw [List.drop_left] at equiv_segment_5 
        rw [List.take_left] at temp_5 
        obtain ⟨temp_4, equiv_segment_4⟩ :=
          corresponding_strings_split
            (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
                [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))]).length
            temp_5
        clear temp_5
        rw [List.drop_left] at equiv_segment_4 
        rw [List.take_left] at temp_4 
        rw [List.take_take] at temp_4 
        obtain ⟨temp_3, equiv_segment_3⟩ :=
          corresponding_strings_split (u ++ List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length temp_4
        clear temp_4
        rw [List.drop_left] at equiv_segment_3 
        rw [List.take_left] at temp_3 
        rw [List.take_take] at temp_3 
        obtain ⟨equiv_segment_1, equiv_segment_2⟩ := corresponding_strings_split u.length temp_3
        clear temp_3
        rw [List.drop_left] at equiv_segment_2 
        rw [List.take_left] at equiv_segment_1 
        rw [List.take_take] at equiv_segment_1 
        have equiv_sgmnt_1 :
          corresponding_strings (List.take u.length (List.map (wrapSymbol₁ g₂.nt) x)) u := by
          simpa using equiv_segment_1
        have equiv_sgmnt_2 :
          corresponding_strings
            (List.drop u.length
              (List.take (u.length + r₁.input_L.length) (List.map (wrapSymbol₁ g₂.nt) x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_L) :=
          by simpa using equiv_segment_2
        have equiv_sgmnt_3 :
          corresponding_strings
            (List.drop (u.length + r₁.input_L.length)
              (List.take (u.length + (r₁.input_L.length + 1)) (List.map (wrapSymbol₁ g₂.nt) x)))
            [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] :=
          by simpa using equiv_segment_3
        have equiv_sgmnt_4 :
          corresponding_strings
            (List.drop (u.length + (r₁.input_L.length + 1))
              (List.take (u.length + (r₁.input_L.length + (r₁.input_R.length + 1)))
                (List.map (wrapSymbol₁ g₂.nt) x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_R) :=
          by simpa using equiv_segment_4
        have equiv_sgmnt_5 :
          corresponding_strings
            (List.drop (u.length + (r₁.input_L.length + (r₁.input_R.length + 1)))
              (List.map (wrapSymbol₁ g₂.nt) x))
            (List.take (x.length - u.length - m) v) :=
          by simpa using equiv_segment_5
        clear equiv_segment_1 equiv_segment_2 equiv_segment_3 equiv_segment_4 equiv_segment_5
        have segment_1_eqi :
          corresponding_strings (List.map (wrapSymbol₁ g₂.nt) (List.take u.length x)) u :=
          by
          convert equiv_sgmnt_1
          rw [List.map_take]
        have segment_1_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_1_eqi).symm
        rw [← List.take_append_drop u.length x]
        apply congr_arg₂
        · exact segment_1_equ
        clear segment_1_equ segment_1_eqi equiv_sgmnt_1
        have segment_2_eqi :
          corresponding_strings
            (List.map (wrapSymbol₁ g₂.nt) (List.take r₁.input_L.length (List.drop u.length x)))
            (List.map (wrapSymbol₁ g₂.nt) r₁.input_L) :=
          by
          convert equiv_sgmnt_2
          rw [List.map_take]
          rw [List.map_drop]
          rw [List.drop_take]
        have segment_2_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_2_eqi).symm
        rw [unwrap_wrap₁_string] at segment_2_equ 
        rw [← List.take_append_drop r₁.input_L.length (List.drop u.length x)]
        apply congr_arg₂
        · exact segment_2_equ
        clear segment_2_equ segment_2_eqi equiv_sgmnt_2
        rw [List.drop_drop]
        have segment_3_eqi :
          corresponding_strings
            (List.map (wrapSymbol₁ g₂.nt)
              (List.take 1 (List.drop (r₁.input_L.length + u.length) x)))
            (List.map (wrapSymbol₁ g₂.nt) [Symbol.nonterminal r₁.input_N]) :=
          by
          convert equiv_sgmnt_3
          rw [List.map_take]
          rw [List.map_drop]
          rw [← add_assoc]
          rw [List.drop_take]
          rw [add_comm]
        have segment_3_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_3_eqi).symm
        rw [unwrap_wrap₁_string] at segment_3_equ 
        rw [← List.take_append_drop 1 (List.drop (r₁.input_L.length + u.length) x)]
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
        exact filter_map_unwrap_of_corresponding_strings₁ equiv_sgmnt_5
      · rw [List.filterMap_append_append]
        congr
        rw [unwrap_wrap₁_string]
    · exact ih_y
  rw [aft]
  rw [bef] at ih_concat 
  rw [List.filterMap_append_append]
  rw [List.map_append_append]
  rw [List.append_assoc]
  rw [List.append_assoc]
  apply corresponding_strings_append
  · have part_for_u := corresponding_strings_take u.length ih_concat
    rw [List.take_left] at part_for_u 
    have trivi : u.length ≤ (List.map (wrapSymbol₁ g₂.nt) x).length :=
      by
      clear * - critical
      rw [List.length_map]
      omega
    rw [List.take_append_of_le_length trivi] at part_for_u 
    clear * - part_for_u
    rw [← List.map_take] at part_for_u 
    apply corresponding_string_after_wrap_unwrap_self₁
    use List.take u.length x
    exact part_for_u
  apply corresponding_strings_append
  · rw [unwrap_wrap₁_string]
    apply corresponding_strings_self
  convert_to
    corresponding_strings _
      (List.take (x.length - u.length - m) v ++ List.drop (x.length - u.length - m) v)
  · rw [List.take_append_drop]
  apply corresponding_strings_append
  · have eqi := corresponding_strings_take (List.map (wrapSymbol₁ g₂.nt) x).length ih_concat
    rw [List.take_left] at eqi 
    have part_for_v_beginning := corresponding_strings_drop (u.length + m) eqi
    clear * - part_for_v_beginning critical
    rw [← List.map_drop] at part_for_v_beginning 
    apply corresponding_string_after_wrap_unwrap_self₁
    use List.drop (u.length + m) x
    convert part_for_v_beginning
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
      (List.map (wrapSymbol₁ g₂.nt) r₁.input_L ++
              [Symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
            List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length =
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
    unfold List.drop
  -- now we have what `g₂` generated
  have reverse_concat := corresponding_strings_reverse ih_concat
  repeat' rw [List.reverse_append] at reverse_concat 
  have the_part := corresponding_strings_take y.length reverse_concat
  apply corresponding_strings_of_reverse
  have len_sum : y.length + (x.length - u.length - m) = v.length :=
    by
    change
      y.length +
          (x.length - u.length -
            ((List.map (wrapSymbol₁ g₂.nt) r₁.input_L).length + 1 +
              (List.map (wrapSymbol₁ g₂.nt) r₁.input_R).length)) =
        v.length
    have len_concat := corresponding_strings_length ih_concat
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
    rw [add_tsub_cancel_left]
  have yl_lt_vl : y.length ≤ v.length := Nat.le.intro len_sum
  convert_to corresponding_strings _ (List.take y.length v.reverse)
  · convert_to (List.drop (v.length - y.length) v).reverse = List.take y.length v.reverse
    · apply congr_arg
      apply congr_arg₂
      · clear * - len_sum
        omega
      · rfl
    rw [List.reverse_take]
    exact yl_lt_vl
  clear * - the_part yl_lt_vl
  rw [List.take_append_of_le_length] at the_part ; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  repeat' rw [List.append_assoc] at the_part 
  rw [List.take_append_of_le_length] at the_part ; swap
  · rw [List.length_reverse]
    exact yl_lt_vl
  rw [List.take_all_of_le] at the_part ; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  exact the_part

private lemma induction_step_for_lifted_rule_from_g₂ {g₁ g₂ : Grammar T}
    {a b u v : List (Nst T g₁.Nt g₂.Nt)} {x : List (Symbol T g₁.Nt)} {y : List (Symbol T g₂.Nt)}
    {r : Grule T (Nnn T g₁.Nt g₂.Nt)} (rin : r ∈ List.map (wrapGrule₂ g₁.Nt) g₂.rules)
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.outputString ++ v)
    (ih_x : GrammarDerives g₁ [Symbol.nonterminal g₁.initial] x)
    (ih_y : GrammarDerives g₂ [Symbol.nonterminal g₂.initial] y)
    (ih_concat :
      CorrespondingStrings (List.map (wrapSymbol₁ g₂.Nt) x ++ List.map (wrapSymbol₂ g₁.Nt) y) a) :
    ∃ y' : List (Symbol T g₂.Nt),
      And
        (And (GrammarDerives g₁ [Symbol.nonterminal g₁.initial] x)
          (GrammarDerives g₂ [Symbol.nonterminal g₂.initial] y'))
        (CorrespondingStrings (List.map (wrapSymbol₁ g₂.Nt) x ++ List.map (wrapSymbol₂ g₁.Nt) y')
          b) :=
  by
  rw [List.mem_map] at rin 
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
              ([Symbol.nonterminal (Sum.inl (some (Sum.inr r₂.input_N)))] ++
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
    (ass : (bigGrammar g₁ g₂).Derives
        [Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
         Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
        w) :
  ∃ x : List (Symbol T g₁.nt), ∃ y : List (Symbol T g₂.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x  ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y  ∧
    correspondingStrings
      (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y)
      w :=
  by sorry/-
  induction' ass with a b trash orig ih
  · use [Symbol.nonterminal g₁.initial], [Symbol.nonterminal g₂.initial]
    constructor
    · constructor <;> apply Grammar.deri_self
    · rw [List.map_singleton]
      rw [List.map_singleton]
      unfold wrapSymbol₁
      unfold wrapSymbol₂
      rw [List.singleton_append]
      unfold corresponding_strings
      rw [List.forall₂_cons] -- correspondingStrings_cons
      constructor
      · unfold corresponding_symbols
      rw [List.forall₂_cons] -- correspondingStrings_cons
      constructor
      · unfold corresponding_symbols
      exact List.Forall₂.nil
  rcases ih with ⟨x, y, ⟨ih_x, ih_y⟩, ih_concat⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  change _ ∈ List.cons _ _ at rin 
  rw [List.mem_cons_eq] at rin 
  cases rin
  · exfalso
    rw [rin] at bef 
    clear * - ih_concat bef
    simp only [List.append_nil] at bef 
    rw [bef] at ih_concat 
    have same_lengths := corresponding_strings_length ih_concat
    clear bef
    have ulen₁ :
      u.length < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length :=
      by
      rw [List.length_append _ v] at same_lengths 
      rw [List.length_append u _] at same_lengths 
      rw [List.length_singleton] at same_lengths 
      clear * - same_lengths
      linarith
    have ulen₂ : u.length < (u ++ ([Symbol.nonterminal (Sum.inl none)] ++ v)).length :=
      by
      rw [List.length_append]
      rw [List.length_append]
      rw [List.length_singleton]
      clear * -
      linarith
    have ulen_tauto : u.length ≤ u.length := by rfl
    rw [List.append_assoc] at ih_concat 
    have eqi_symb := correspondingStrings_nthLe ulen₁ ulen₂ ih_concat
    rw [List.nthLe_append_right ulen_tauto] at eqi_symb 
    simp only [Nat.sub_self, List.singleton_append, List.nthLe] at eqi_symb 
    have eq_none :
      (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length ulen₁ =
        Symbol.nonterminal (Sum.inl none) :=
      by
      clear * - eqi_symb
      cases'
        (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).nthLe u.length ulen₁ with
        t s
      · exfalso
        unfold corresponding_symbols at eqi_symb 
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
      Symbol.nonterminal (Sum.inl none) ∈
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
          exact Option.noConfusion impos
  rw [List.mem_append] at rin 
  cases rin
  · rw [List.mem_append] at rin 
    cases rin
    · cases' induction_step_for_lifted_rule_from_g₁ rin bef aft ih_x ih_y ih_concat with x' pros
      exact ⟨x', y, pros⟩
    · use x
      exact induction_step_for_lifted_rule_from_g₂ rin bef aft ih_x ih_y ih_concat
  · use x, y
    constructor
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
      have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal (Sum.inr (Sum.inl t))]).length :=
        by
        rw [List.length_append]
        rw [List.length_singleton]
        apply lt_add_one
      have ul_lt_len_umv :
        u.length < (u ++ [Symbol.nonterminal (Sum.inr (Sum.inl t))] ++ v).length :=
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
          (Symbol.nonterminal (Sum.inr (Sum.inl t))) :=
        by
        convert middle_nt
        finish
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
          1 + u.length = (u ++ [Symbol.nonterminal (Sum.inr (Sum.inl t))]).length :=
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
        have rewr_len : u.length + 1 = (u ++ [Symbol.nonterminal (Sum.inr (Sum.inr t))]).length :=
          by
          rw [List.length_append]
          rw [List.length_singleton]
        rw [rewr_len]
        rw [List.drop_left]
      have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal (Sum.inr (Sum.inr t))]).length :=
        by
        rw [List.length_append]
        rw [List.length_singleton]
        apply lt_add_one
      have ul_lt_len_umv :
        u.length < (u ++ [Symbol.nonterminal (Sum.inr (Sum.inr t))] ++ v).length :=
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
          (Symbol.nonterminal (Sum.inr (Sum.inr t))) :=
        by
        convert middle_nt
        finish
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
    (ass : w ∈ (bigGrammar g₁ g₂).Language) :
  w ∈ g₁.Language * g₂.Language :=
by
  rw [Language.mem_mul]
  cases' Grammar.tran_or_id_of_deri ass with case_id case_step
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
  clear ass
  rcases case_step with ⟨w₁, hyp_tran, hyp_deri⟩
  have w₁eq : w₁ =
      [Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
       Symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
  · clear * - hyp_tran
    -- only the first rule is applicable
    rcases hyp_tran with ⟨r, rin, u, v, bef, aft⟩
    have bef_len := congr_arg List.length bef
    rw [List.length_append_append, List.length_append_append,
        List.length_singleton, List.length_singleton] at bef_len 
    have u_nil : u = []
    · clear * - bef_len
      rw [← List.length_eq_zero]
      linarith
    have v_nil : v = []
    · clear * - bef_len
      rw [← List.length_eq_zero]
      linarith
    have rif_nil : r.inputL = []
    · clear * - bef_len
      rw [← List.length_eq_zero]
      linarith
    have nt_match : Symbol.nonterminal (bigGrammar g₁ g₂).initial = Symbol.nonterminal r.inputN
    · have bef_fst := congr_fun (congr_arg List.get? bef) 0
      rw [u_nil, rif_nil] at bef_fst 
      rw [← Option.some_inj]
      exact bef_fst
    simp [bigGrammar, List.mem_cons] at rin -- TODO
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
      change Sum.inl none = Sum.inl (some (Sum.inl r₀.inputN)) at inl_match 
      have none_eq_some := Sum.inl.inj inl_match
      exact Option.noConfusion none_eq_some
    · exfalso
      rcases rin₂ with ⟨r₀, hr₀g₂, wrap_eq_r⟩
      rw [← wrap_eq_r] at nt_match 
      unfold wrapGrule₂ at nt_match 
      have inl_match := Symbol.nonterminal.inj nt_match
      change Sum.inl none = Sum.inl (some (Sum.inr r₀.inputN)) at inl_match 
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
  use List.drop x.length w
  constructor
  · clear deri_y
    unfold Grammar.Language
    rw [Set.mem_setOf_eq]
    unfold Grammar.Generates
    convert deri_x
    clear deri_x
    have xylen := correspondingStrings_length concat_xy
    rw [List.length_append] at xylen 
    repeat' rw [List.length_map] at xylen 
    apply List.ext_get
    · rw [List.length_map, List.length_take_of_le]
      exact le_trans (Nat.le_add_right x.length y.length) (le_of_eq xylen)
    intros i iltwl iltxl
    rw [List.get_map]
    have i_lt_lenl : i < (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y).length
    · rw [List.length_append]
      sorry
    have i_lt_lenr : i < (List.map Symbol.terminal w).length
    · sorry
    have equivalent_ith := correspondingStrings_get i_lt_lenl i_lt_lenr concat_xy
    /-have iltwxl : i < (List.map (wrapSymbol₁ g₂.nt) x).length
    · rw [List.length_map]
      exact iltxl
    have aaaa :
      List.get (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) ⟨i, i_lt_lenl⟩ =
      List.get (List.map (wrapSymbol₁ g₂.nt) x) ⟨i, iltwxl⟩
    · sorry
    rw [aaaa] at equivalent_ith-/
    have asdf :
      List.get (List.map (wrapSymbol₁ g₂.nt) x ++ List.map (wrapSymbol₂ g₁.nt) y) ⟨i, i_lt_lenl⟩ =
      wrapSymbol₁ g₂.nt (x.get ⟨i, iltxl⟩)
    · sorry
    rw [asdf, List.get_map] at equivalent_ith
    set I : Fin x.length := ⟨i, iltxl⟩
    cases' x.get I with t n₁
    · simp [wrapSymbol₁, correspondingSymbols] at equivalent_ith
      sorry
    sorry /-ext1 i
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
    rename' h => i_lt_len_x
    have i_lt_len_lwx : i < (List.map (wrapSymbol₁ g₂.nt) x).length :=
      by
      rw [List.length_map]
      exact i_lt_len_x
    have i_lt_len_w : i < w.length :=
      by
      apply lt_of_lt_of_le i_lt_len_x
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
    rw [List.get?_take i_lt_len_x]
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
    · exact i_lt_len_x
    clear * - equivalent_ith
    rw [List.nthLe_get? i_lt_len_x]
    cases' x.nth_le i i_lt_len_x with t n <;> unfold wrapSymbol₁ at equivalent_ith  <;>
      unfold corresponding_symbols at equivalent_ith 
    · have symbol_ith := congr_arg (@Symbol.terminal T g₁.nt) equivalent_ith
      rw [List.nthLe_get? i_lt_len_w]
      rw [Option.map_some']
      exact congr_arg Option.some symbol_ith
    · exfalso
      exact equivalent_ith-/
  constructor
  · clear deri_x
    unfold Grammar.Language
    rw [Set.mem_setOf_eq]
    unfold Grammar.Generates
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
    rename' h => i_lt_len_y
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
      exact i_lt_len_y
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
      y.nth_le i i_lt_len_y =
        (List.drop x.length (List.map Symbol.terminal w)).nthLe i i_lt_len_dxw :=
      by
      have xli_lt_len_w : x.length + i < w.length :=
        by
        clear * - i_lt_len_y xylen
        linarith
      rw [List.nthLe_map _ _ i_lt_len_y] at eqiv_symb 
      rw [List.nthLe_drop'] at *
      rw [List.nthLe_map]; swap
      · exact xli_lt_len_w
      rw [List.nthLe_map] at eqiv_symb ; swap
      · rw [List.length_map]
        exact xli_lt_len_w
      clear * - eqiv_symb
      cases' y.nth_le i i_lt_len_y with t n
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
      some (y.nth_le i i_lt_len_y) =
        some ((List.map Symbol.terminal (List.drop x.length w)).nthLe i i_lt_len_mtw) :=
      by
      rw [goal_as_ith_drop]
      clear * -
      congr
      rw [List.map_drop]
    clear * - goal_as_some_ith
    rw [← List.nthLe_get? i_lt_len_y] at goal_as_some_ith 
    rw [← List.nthLe_get? i_lt_len_mtw] at goal_as_some_ith 
    convert goal_as_some_ith
    rw [List.get?_map]-/
  apply List.take_append_drop

end VeryComplicated

end HardDirection

/-- The class of recursively-enumerable languages is closed under concatenation. -/
theorem RE_of_RE_c_RE (L₁ : Language T) (L₂ : Language T) :
  IsRE L₁  ∧  IsRE L₂  →  IsRE (L₁ * L₂)  :=
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
