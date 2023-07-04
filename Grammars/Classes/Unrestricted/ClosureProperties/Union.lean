import Grammars.Classes.Unrestricted.Basics.Lifting
import Grammars.Utilities.ListUtils

variable {T : Type}

def unionGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (Option (Sum g₁.nt g₂.nt)) none (
    ⟨[], none, [], [Symbol.nonterminal (some (Sum.inl g₁.initial))]⟩ :: (
    ⟨[], none, [], [Symbol.nonterminal (some (Sum.inr g₂.initial))]⟩ :: (
    List.map (liftRule (some ∘ Sum.inl)) g₁.rules ++
    List.map (liftRule (some ∘ Sum.inr)) g₂.rules)))


variable {g₁ g₂ : Grammar T}

private def oN₁_of_N : (unionGrammar g₁ g₂).nt → Option g₁.nt
  | none => none
  | some (Sum.inl n) => some n
  | some (Sum.inr _) => none

private def oN₂_of_N : (unionGrammar g₁ g₂).nt → Option g₂.nt
  | none => none
  | some (Sum.inl _) => none
  | some (Sum.inr n) => some n


def lg₁ : LiftedGrammar T :=
  LiftedGrammar.mk g₁ (unionGrammar g₁ g₂) (Option.some ∘ Sum.inl) oN₁_of_N
    (by
      intro x y hyp
      apply Sum.inl_injective
      apply Option.some_injective
      exact hyp
    )
    (by
      intro x y hyp
      cases' x with x'
      · right
        rfl
      cases' x' with x''; swap
      · right
        rfl
      cases' y with y'
      · rw [hyp]
        right
        rfl
      cases' y' with y''; swap
      · tauto
      left
      simp only [oN₁_of_N, Option.some.injEq] at hyp
      apply congr_arg
      apply congr_arg
      exact hyp
    )
    (by
      intro
      rfl
    )
    (by
      intro r hyp
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      rw [List.mem_map]
      use r
      constructor
      · exact hyp
      rfl
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      simp [unionGrammar] at rin
      rcases rin with req₁ | req₂ | rin₁ | rin₂
      · exfalso
        rw [req₁] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rw [req₂] at rnt
        exact Option.noConfusion rnt
      · exact rin₁
      · exfalso
        rcases rin₂ with ⟨r₂, r₂_in, r₂_lift⟩
        rw [← r₂_lift] at rnt
        have rnti := Option.some.inj rnt
        exact Sum.noConfusion rnti
    )

def lg₂ : LiftedGrammar T :=
  LiftedGrammar.mk g₂ (unionGrammar g₁ g₂) (Option.some ∘ Sum.inr) oN₂_of_N
    (by
      intro x y hyp
      apply Sum.inr_injective
      apply Option.some_injective
      exact hyp
    )
    (by
      intro x y hyp
      cases' x with x'
      · right
        rfl
      cases' x' with _ x''
      · right
        rfl
      cases' y with y'
      · rw [hyp]
        right
        rfl
      cases' y' with _ y''
      · tauto
      left
      simp only [oN₂_of_N, Option.some.injEq] at hyp
      apply congr_arg
      apply congr_arg
      exact hyp
    )
    (by
      intro
      rfl
    )
    (by
      intro r hyp
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      rw [List.mem_map]
      use r
      constructor
      · exact hyp
      rfl
    )
    (by
      rintro r ⟨rin, n₁, rnt⟩
      simp [unionGrammar] at rin
      rcases rin with req₁ | req₂ | rin₁ | rin₂
      · exfalso
        rw [req₁] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rw [req₂] at rnt
        exact Option.noConfusion rnt
      · exfalso
        rcases rin₁ with ⟨r₁, r₁_in, r₁_lift⟩
        rw [← r₁_lift] at rnt
        have rnti := Option.some.inj rnt
        exact Sum.noConfusion rnti
      · exact rin₂
    )


lemma in_L₁_or_L₂_of_in_union {w : List T}
    (ass : w ∈ (unionGrammar g₁ g₂).Language) :
  w ∈ g₁.Language ∨ w ∈ g₂.Language :=
by
  unfold Grammar.Language at ass ⊢
  rw [Set.mem_setOf_eq] at ass ⊢
  rw [Set.mem_setOf_eq]
  unfold Grammar.Generates at ass ⊢
  have hyp := Grammar.tran_or_id_of_deri ass
  clear ass
  cases' hyp with hypo hypot
  · exfalso
    have zeroth := congr_fun (congr_arg List.get? hypo) 0
    cases w
    · exact Option.noConfusion zeroth
    · rw [List.get?, List.map_cons, List.get?] at zeroth 
      have nt_eq_ter := Option.some.inj zeroth
      exact Symbol.noConfusion nt_eq_ter
  rcases hypot with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩
  have uv_nil :  u = []  ∧  v = []
  · have bef_len := congr_arg List.length bef
    clear * - bef_len
    rw [List.length_singleton] at bef_len 
    repeat' rw [List.length_append] at bef_len 
    rw [List.length_singleton] at bef_len 
    constructor <;>
    · rw [← List.length_eq_zero]
      linarith
  rw [uv_nil.1, List.nil_append, uv_nil.2, List.append_nil] at bef aft 
  have same_nt : (unionGrammar g₁ g₂).initial = r.inputN
  · clear * - bef
    have elemeq :
      [Symbol.nonterminal (unionGrammar g₁ g₂).initial] = [Symbol.nonterminal r.inputN]
    · have bef_len := congr_arg List.length bef
      rw [List.length_append_append, List.length_singleton, List.length_singleton] at bef_len 
      have rl_first : r.inputL.length = 0
      · clear * - bef_len
        linarith
      have rl_third : r.inputR.length = 0
      · clear * - bef_len
        linarith
      rw [List.length_eq_zero] at rl_first rl_third 
      rw [rl_first, rl_third] at bef 
      exact bef
    exact Symbol.nonterminal.inj (List.head_eq_of_cons_eq elemeq)
  simp [unionGrammar] at rin
  rcases rin with req₁ | req₂ | rin₁ | rin₂
  · rw [req₁] at aft 
    dsimp only at aft 
    rw [aft] at deri 
    left
    have sinked := sink_deri lg₁ deri
    clear * - sinked
    specialize sinked (by
        unfold GoodString
        simp only [List.mem_singleton, forall_eq]
        use g₁.initial
        rfl
      )
    convert sinked
    unfold sinkString
    rw [List.filterMap_map]
    convert_to List.map Symbol.terminal w = List.filterMap (Option.some ∘ Symbol.terminal) w
    rw [← List.filterMap_map]
    rw [List.filterMap_some]
  · rw [req₂] at aft 
    dsimp only at aft 
    rw [aft] at deri 
    right
    have sinked := sink_deri lg₂ deri
    clear * - sinked
    specialize sinked (by
        unfold GoodString
        simp only [List.mem_singleton, forall_eq]
        use g₂.initial
        rfl
      )
    convert sinked
    unfold sinkString
    rw [List.filterMap_map]
    convert_to List.map Symbol.terminal w = List.filterMap (Option.some ∘ Symbol.terminal) w
    rw [← List.filterMap_map]
    rw [List.filterMap_some]
  · suffices True = False
      by contradiction
    rcases rin₁ with ⟨r₁, _, r_of_r₁⟩
    convert congr_arg
        (fun z => Symbol.nonterminal (liftRule (Option.some ∘ Sum.inl) r₁).inputN ∈ z)
        bef.symm
    · rw [true_iff]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_singleton, r_of_r₁]
    · rw [List.mem_singleton, Symbol.nonterminal.injEq]
      simp [liftRule, unionGrammar]
  · suffices True = False
      by contradiction
    rcases rin₂ with ⟨r₂, _, r_of_r₂⟩
    convert congr_arg
        (fun z => Symbol.nonterminal (liftRule (Option.some ∘ Sum.inr) r₂).inputN ∈ z)
        bef.symm
    · rw [true_iff]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.mem_singleton, r_of_r₂]
    · rw [List.mem_singleton, Symbol.nonterminal.injEq]
      simp [liftRule, unionGrammar]

lemma in_union_of_in_L₁ {w : List T} (ass : w ∈ g₁.Language) :
  w ∈ (unionGrammar g₁ g₂).Language :=
by
  unfold Grammar.Language at ass ⊢
  rw [Set.mem_setOf_eq] at ass ⊢
  unfold Grammar.Generates at ass ⊢
  apply Grammar.deri_of_tran_deri
  · use ⟨[], none, [], [Symbol.nonterminal (some (Sum.inl g₁.initial))]⟩
    constructor
    · apply List.mem_cons_self
    use [], []
    constructor <;> rfl
  rw [List.nil_append, List.append_nil]
  change lg₁.g.Derives
      (liftString lg₁.liftNt [Symbol.nonterminal g₁.initial])
      (List.map Symbol.terminal w)
  convert lift_deri (@lg₁ T g₁ g₂) ass
  unfold liftString
  rw [List.map_map]
  rfl

lemma in_union_of_in_L₂ {w : List T} (ass : w ∈ g₂.Language) :
  w ∈ (unionGrammar g₁ g₂).Language :=
by
  unfold Grammar.Language at ass ⊢
  rw [Set.mem_setOf_eq] at ass ⊢
  unfold Grammar.Generates at ass ⊢
  apply Grammar.deri_of_tran_deri
  · use ⟨[], none, [], [Symbol.nonterminal (some (Sum.inr g₂.initial))]⟩
    constructor
    · apply List.mem_cons_of_mem
      apply List.mem_cons_self
    use [], []
    constructor <;> rfl
  rw [List.nil_append, List.append_nil]
  change lg₂.g.Derives
      (liftString lg₂.liftNt [Symbol.nonterminal g₂.initial])
      (List.map Symbol.terminal w)
  convert lift_deri (@lg₂ T g₁ g₂) ass
  unfold liftString
  rw [List.map_map]
  rfl

/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : Language T) (L₂ : Language T) :
  IsRE L₁  ∧  IsRE L₂  →  IsRE (L₁ + L₂)  :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  use unionGrammar g₁ g₂
  apply Set.eq_of_subset_of_subset
  · intro w ass
    rw [Language.mem_add]
    rw [← eq_L₁, ← eq_L₂]
    exact in_L₁_or_L₂_of_in_union ass
  · intro w ass
    cases' ass with case₁ case₂
    · rw [← eq_L₁] at case₁ 
      exact in_union_of_in_L₁ case₁
    · rw [← eq_L₂] at case₂ 
      exact in_union_of_in_L₂ case₂
