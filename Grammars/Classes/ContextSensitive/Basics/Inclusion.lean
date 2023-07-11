import Grammars.Classes.ContextSensitive.Basics.Toolbox
import Grammars.Classes.Unrestricted.Basics.Toolbox
import Mathlib.Tactic.Linarith

variable {T : Type}

def woption {N : Type} : Symbol T N → Symbol T (Option N)
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (some n)

def grule_of_CSrule {N : Type} (r : CSrule T N) : Grule T (Option N) :=
  Grule.mk (r.contextLeft.map woption) (some r.inputNonterminal) (r.contextRight.map woption) (
    r.contextLeft.map woption ++ r.outputString.map woption ++ r.contextRight.map woption)

def grammar_of_csg (g : CSgrammar T) : Grammar T :=
  let R := Grule.mk [] none [] [Symbol.nonterminal g.initial] :: List.map grule_of_CSrule g.rules
  Grammar.mk (Option g.nt) none (if g.allow_empty then Grule.mk [] none [] [] :: R else R)

private lemma inductionTODO {g : CSgrammar T} {w : List (Symbol T g.nt)}
    (ass : g.Derives [Symbol.nonterminal g.initial] w) :
  (grammar_of_csg g).Derives [Symbol.nonterminal none] (List.map woption w) :=
by
  induction' ass with a b _ step ih
  · apply Grammar.deri_of_tran
    use Grule.mk [] none [] [Symbol.nonterminal (some g.initial)]
    constructor
    · dsimp only [grammar_of_csg]
      cases g.allow_empty
      · simp
      · simp
    use [], []
    simp [woption]
  apply Grammar.deri_of_deri_tran ih
  rcases step with ⟨r, rin, u, v, bef, aft⟩
  use grule_of_CSrule r
  constructor
  · clear * - rin
    dsimp only [grammar_of_csg]
    by_cases empty_allowed : g.allow_empty
    · simp [empty_allowed]
      right
      right
      exact ⟨r, rin, rfl⟩
    · simp [empty_allowed]
      right
      exact ⟨r, rin, rfl⟩
  use List.map woption u, List.map woption v
  constructor
  · convert congr_arg (List.map woption) bef
    simp [List.map_append, grule_of_CSrule, woption]
  · convert congr_arg (List.map woption) aft
    simp [List.map_append, grule_of_CSrule, woption]

private lemma oppositeTODO {g : CSgrammar T} {w : List (Symbol T g.nt)}
    (ass : (grammar_of_csg g).Derives [Symbol.nonterminal (some g.initial)] (List.map woption w)) :
  g.Derives [Symbol.nonterminal g.initial] w :=
by
  let g' := grammar_of_csg g
  have ass' : Grammar.Derives g' [Symbol.nonterminal (some g.initial)] (List.map woption w)
  · exact ass
  sorry

private lemma missingTODO {g : CSgrammar T} {w : List T}
    (ass : (grammar_of_csg g).Derives [Symbol.nonterminal none] (List.map Symbol.terminal w)) :
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) :=
by
  sorry

lemma csLanguage_eq_grammarLanguage (g : CSgrammar T) :
  g.Language = (grammar_of_csg g).Language :=
by
  unfold Grammar.Language
  ext1 w
  by_cases emptyStr : w = []
  · by_cases emptyCan : g.allow_empty
    · convert_to True ↔ True
      · rw [iff_true]
        simp only [CSgrammar.Language, CSgrammar.Generates, emptyStr, emptyCan, and_true]
        rw [Set.mem_setOf_eq]
        left
        rfl
      · rw [iff_true, Set.mem_setOf_eq, emptyStr]
        apply Grammar.deri_of_tran
        rw [List.map_nil]
        use Grule.mk [] none [] []
        constructor
        · simp [grammar_of_csg, emptyCan]
        use [], []
        simp [grammar_of_csg]
      rfl
    · convert_to False ↔ False
      · simp only [CSgrammar.Language, CSgrammar.Generates, emptyStr, emptyCan, and_false]
        rw [Set.mem_setOf_eq]
        simp only [List.map, false_or, iff_false]
        intro imposs
        cases' CSgrammar.eq_or_deriTran_of_deri imposs with case_id case_tr
        · cases case_id
        rcases case_tr with ⟨x, _, r, rin, u, v, bef, aft⟩
        have imposs := congr_arg List.length aft
        rw [List.length_nil, List.length_append, List.length_append, List.length_append, List.length_append] at imposs
        clear * - imposs
        have := r.output_nonempty
        linarith
      · sorry
      rfl
  rw [Set.mem_setOf_eq]
  constructor
  · unfold CSgrammar.Language
    rw [Set.mem_setOf]
    unfold CSgrammar.Generates
    intro ass
    cases' ass with impos hyp
    · exfalso
      apply emptyStr
      exact impos.1
    unfold Grammar.Generates
    convert inductionTODO hyp
    apply List.ext_get
    · simp only [List.length_map]
    intro n hnl hnr
    simp [woption]
  · unfold Grammar.Generates
    intro ass
    unfold CSgrammar.Language
    rw [Set.mem_setOf]
    unfold CSgrammar.Generates
    right
    exact missingTODO ass

theorem CS_subclass_RE {L : Language T} :
  IsCS L  →  IsGG L  :=
by
  rintro ⟨g, eq_L⟩
  use grammar_of_csg g
  rw [← eq_L]
  rw [csLanguage_eq_grammarLanguage]
