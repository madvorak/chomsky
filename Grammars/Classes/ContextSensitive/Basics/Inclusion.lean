import Grammars.Classes.ContextSensitive.Basics.Toolbox
import Grammars.Classes.Unrestricted.Basics.Toolbox
import Mathlib.Tactic.Linarith

variable {T : Type}

def ssss {N : Type} : Symbol T N → Symbol T (Option N)
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (some n)

def wwww {N : Type} (r : CSrule T N) : Grule T (Option N) :=
  Grule.mk (r.contextLeft.map ssss) (some r.inputNonterminal) (r.contextRight.map ssss) (
    r.contextLeft.map ssss ++ r.outputString.map ssss ++ r.contextRight.map ssss)
--  (r.contextLeft ++ [Symbol.nonterminal r.inputNonterminal] ++ r.contextRight).map ssss)

def grammar_of_csg (g : CSgrammar T) : Grammar T :=
  let R := Grule.mk [] none [] [Symbol.nonterminal g.initial] :: List.map wwww g.rules
  Grammar.mk (Option g.nt) none (if g.allow_empty then Grule.mk [] none [] [] :: R else R)

private lemma inductionTODO {g : CSgrammar T} {w : List (Symbol T g.nt)}
    (ass : g.Derives [Symbol.nonterminal g.initial] w) :
  (grammar_of_csg g).Derives [Symbol.nonterminal none] (List.map ssss w) :=
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
    simp [ssss]
  apply Grammar.deri_of_deri_tran ih
  rcases step with ⟨r, rin, u, v, bef, aft⟩
  use wwww r
  constructor
  · clear * - rin
    dsimp only [grammar_of_csg]
    by_cases empty_allowed : g.allow_empty
    · simp [empty_allowed] -- TODO
      right
      right
      exact ⟨r, rin, rfl⟩
    · simp [empty_allowed] -- TODO
      right
      exact ⟨r, rin, rfl⟩
  use List.map ssss u, List.map ssss v
  constructor
  · convert congr_arg (List.map ssss) bef
    simp [List.map_append, wwww, ssss]
  · convert congr_arg (List.map ssss) aft
    simp [List.map_append, wwww, ssss]

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
        cases' CSgrammar.id_or_tran_of_deri imposs with case_id case_tr
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
    simp [ssss]
  · sorry

theorem CS_subclass_RE {L : Language T} :
  IsCS L  →  IsGG L  :=
by
  rintro ⟨g, eq_L⟩
  use grammar_of_csg g
  rw [← eq_L]
  rw [csLanguage_eq_grammarLanguage]
