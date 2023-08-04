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

private lemma CSderi_of_general {g : CSgrammar T} {w : List (Symbol T g.nt)}
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
    · simp only [empty_allowed, ite_true, List.mem_cons, List.mem_map]
      right; right
      exact ⟨r, rin, rfl⟩
    · simp only [empty_allowed, ite_false, List.mem_cons, List.mem_map]
      right
      exact ⟨r, rin, rfl⟩
  use List.map woption u, List.map woption v
  constructor
  · convert congr_arg (List.map woption) bef
    simp [List.map_append, grule_of_CSrule, woption]
  · convert congr_arg (List.map woption) aft
    simp [List.map_append, grule_of_CSrule, woption]

private lemma backwardsTODO {g : CSgrammar T} {w : List (Symbol T g.nt)}
    (ass : (grammar_of_csg g).Derives [Symbol.nonterminal (some g.initial)] (List.map woption w)) :
  g.Derives [Symbol.nonterminal g.initial] w :=
by -- TODO instead of wrapping in assumption, dewrap in goal
  sorry

private lemma missingTODO {g : CSgrammar T} {w : List T}
    (ass : (grammar_of_csg g).Derives [Symbol.nonterminal none] (List.map Symbol.terminal w))
    (wnn : w ≠ []) :
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) :=
by -- maybe useless
  cases' Grammar.eq_or_tran_deri_of_deri ass with imposs possib
  · exfalso
    have contra := congr_fun (congr_arg (List.get?) imposs) 0
    simp [List.get?, forall_true_left, List.get?_map] at contra
    cases' w <;> simp at contra
  rcases possib with ⟨y, ⟨r, rin, u, v, bef, aft⟩, rest⟩
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
        cases' CSgrammar.eq_or_deri_tran_of_deri imposs with case_id case_tr
        · cases case_id
        rcases case_tr with ⟨x, -, r, rin, u, v, bef, aft⟩
        have contra := congr_arg List.length aft
        rw [List.length_nil, List.length_append, List.length_append, List.length_append, List.length_append] at contra
        clear * - contra
        have routlen := r.output_nonempty
        linarith
      · rw [iff_false, Set.mem_setOf_eq, emptyStr]
        intro imposs
        cases' Grammar.eq_or_deri_tran_of_deri imposs with case_id case_tr
        · cases' w with d l <;> simp at case_id
        rcases case_tr with ⟨x, -, r, rin, u, v, bef, aft⟩
        have routlen : r.output.length > 0
        · simp only [grammar_of_csg, emptyCan, ite_false, List.mem_cons, List.mem_map] at rin
          cases' rin with ris rof
          · simp [ris]
          rcases rof with ⟨r₁, -, eqr⟩
          rw [← eqr]
          simp only [grule_of_CSrule, List.append_assoc, List.length_append, add_pos_iff]
          right; left
          rw [List.length_map]
          exact r₁.output_nonempty
        have contra := congr_arg List.length aft
        rw [List.length_map, List.length_nil, List.length_append, List.length_append] at contra
        clear * - contra routlen
        linarith
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
    convert CSderi_of_general hyp
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
    exact missingTODO ass emptyStr

theorem CS_subclass_RE {L : Language T} :
  IsCS L → IsGG L :=
by
  rintro ⟨g, eq_L⟩
  use grammar_of_csg g
  rw [← eq_L]
  rw [csLanguage_eq_grammarLanguage]
