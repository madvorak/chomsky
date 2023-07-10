import Grammars.Classes.Unrestricted.Basics.Definition

/-- Transformation rule for a grammar in the Kuroda Normal Form. -/
inductive KurodaRule (T : Type) (N : Type)
  | two_two (A B C D : N) : KurodaRule T N
  | one_two (A B C : N) : KurodaRule T N
  | one_one (A : N) (t : T) : KurodaRule T N
  | one_nil (A : N) : KurodaRule T N

/-- Grammar in the Kuroda Normal Form that generates words
    over the alphabet `T` (a type of terminals). -/
structure KurodaGrammar (T : Type) where
  nt : Type
  initial : nt
  rules : List (KurodaRule T nt)

variable {T : Type}

/-- One step of transformation by a grammar in the Kuroda Normal Form. -/
def KurodaGrammar.Transforms (g : KurodaGrammar T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : KurodaRule T g.nt,
    r ∈ g.rules  ∧
    ∃ u v : List (Symbol T g.nt),
      match r with
      | KurodaRule.two_two A B C D =>
          w₁ = u ++ [Symbol.nonterminal A, Symbol.nonterminal B] ++ v  ∧
          w₂ = u ++ [Symbol.nonterminal C, Symbol.nonterminal D] ++ v
      | KurodaRule.one_two A B C =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v  ∧
          w₂ = u ++ [Symbol.nonterminal B, Symbol.nonterminal C] ++ v
      | KurodaRule.one_one A t =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v  ∧
          w₂ = u ++ [Symbol.terminal t] ++ v
      | KurodaRule.one_nil A =>
          w₁ = u ++ [Symbol.nonterminal A] ++ v  ∧
          w₂ = u ++ v

/-- Any number of steps of transformation by a grammar in the Kuroda Normal Form. -/
def KurodaGrammar.Derives (g : KurodaGrammar T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def KurodaGrammar.Generates (g : KurodaGrammar T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def KurodaGrammar.Language (g : KurodaGrammar T) : Language T :=
  setOf g.Generates

-- end of definition

def grule_of_kurodaRule {N : Type} : KurodaRule T N → Grule T N
  | KurodaRule.two_two A B C D => Grule.mk [] A [Symbol.nonterminal B] [Symbol.nonterminal C, Symbol.nonterminal D]
  | KurodaRule.one_two A B C => Grule.mk [] A [] [Symbol.nonterminal B, Symbol.nonterminal C]
  | KurodaRule.one_one A t => Grule.mk [] A [] [Symbol.terminal t]
  | KurodaRule.one_nil A => Grule.mk [] A [] []

def grammar_of_kurodaGrammar (k : KurodaGrammar T) : Grammar T :=
  Grammar.mk k.nt k.initial (List.map grule_of_kurodaRule k.rules)

lemma kuroda_tran_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Transforms w₁ w₂  ↔  (grammar_of_kurodaGrammar k).Transforms w₁ w₂  :=
by
  constructor
  · rintro ⟨r, rin, u, v, ass⟩
    use grule_of_kurodaRule r
    constructor
    · simp only [grammar_of_kurodaGrammar, List.mem_map]
      exact ⟨r, rin, rfl⟩
    use u, v
    cases r with
    | two_two A B C D =>
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [grule_of_kurodaRule, List.append_nil, List.append_assoc, List.singleton_append]
        rw [← List.append_assoc]
        exact bef
      · simp only [grule_of_kurodaRule]
        exact aft
    | one_two A B C =>
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [grule_of_kurodaRule, List.append_nil]
        exact bef
      · simp only [grule_of_kurodaRule]
        exact aft
    | one_one A t =>
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [grule_of_kurodaRule, List.append_nil]
        exact bef
      · simp only [grule_of_kurodaRule]
        exact aft
    | one_nil A =>
      cases' ass with bef aft
      constructor
      · simp only [grule_of_kurodaRule, List.append_nil]
        exact bef
      · simp only [grule_of_kurodaRule, List.append_nil]
        exact aft
  · rintro ⟨r, rin, u, v, ass⟩
    simp [grammar_of_kurodaGrammar, grule_of_kurodaRule] at rin
    rcases rin with ⟨r₀, rink, hyp⟩
    cases r₀ with
    | two_two A B C D =>
      use KurodaRule.two_two A B C D
      constructor
      · exact rink
      use u, v
      dsimp only at hyp ⊢
      rw [← hyp] at ass
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [List.append_nil, List.append_assoc, List.singleton_append] at bef
        rw [← List.append_assoc] at bef
        exact bef
      · exact aft
    | one_two A B C =>
      use KurodaRule.one_two A B C
      constructor
      · exact rink
      use u, v
      dsimp only at hyp ⊢
      rw [← hyp] at ass
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [List.append_nil] at bef
        exact bef
      · exact aft
    | one_one A t =>
      use KurodaRule.one_one A t
      constructor
      · exact rink
      use u, v
      dsimp only at hyp ⊢
      rw [← hyp] at ass
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [List.append_nil] at bef
        exact bef
      · exact aft
    | one_nil A =>
      use KurodaRule.one_nil A
      constructor
      · exact rink
      use u, v
      dsimp only at hyp ⊢
      rw [← hyp] at ass
      dsimp only at ass
      cases' ass with bef aft
      constructor
      · simp only [List.append_nil] at bef
        exact bef
      · rw [List.append_nil] at aft
        exact aft

lemma kuroda_tran_rel_eq (k : KurodaGrammar T) :
  k.Transforms = (grammar_of_kurodaGrammar k).Transforms :=
by
  ext w₁ w₂
  apply kuroda_tran_iff

lemma kuroda_deri_iff (k : KurodaGrammar T) (w₁ w₂ : List (Symbol T k.nt)) :
  k.Derives w₁ w₂  ↔  (grammar_of_kurodaGrammar k).Derives w₁ w₂  :=
by
  unfold KurodaGrammar.Derives
  rw [kuroda_tran_rel_eq]
  rfl

lemma kuroda_gene_iff (k : KurodaGrammar T) (w : List T) :
  k.Generates w  ↔  (grammar_of_kurodaGrammar k).Generates w  :=
by
  unfold KurodaGrammar.Generates
  rw [kuroda_deri_iff]
  rfl

theorem kuroda_lang_eq (k : KurodaGrammar T) :
  k.Language = (grammar_of_kurodaGrammar k).Language :=
by
  ext w
  apply kuroda_gene_iff

-- big hard theorem will follow

theorem kurodaGrammar_always_exists (L : Language T) :
  IsGG L  →  ∃ k : KurodaGrammar T, k.Language = L  :=
sorry
