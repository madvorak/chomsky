import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Lemmas
--import Mathlib.Algebra.Order.WithZero
import Mathlib.Tactic.Have

namespace List

variable {α β : Type _} {x y z : List α}

section ListAppendAppend

lemma length_append_append :
  (x ++ y ++ z).length = x.length + y.length + z.length :=
by
  rw [List.length_append, List.length_append]

lemma map_append_append {f : α → β} :
  (x ++ y ++ z).map f = x.map f ++ y.map f ++ z.map f :=
by
  rw [List.map_append, List.map_append]

lemma filterMap_append_append {f : α → Option β} :
  (x ++ y ++ z).filterMap f = x.filterMap f ++ y.filterMap f ++ z.filterMap f :=
by
  rw [List.filterMap_append, List.filterMap_append]

lemma reverse_append_append :
  (x ++ y ++ z).reverse = z.reverse ++ y.reverse ++ x.reverse :=
by
  rw [List.reverse_append, List.reverse_append, List.append_assoc]

lemma mem_append_append {a : α} :
  a ∈ x ++ y ++ z ↔ a ∈ x ∨ a ∈ y ∨ a ∈ z :=
by
  rw [List.mem_append, List.mem_append, or_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a) ↔ (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a) :=
by
  rw [List.forall_mem_append, List.forall_mem_append, and_assoc]

lemma join_append_append {X Y Z : List (List α)} :
  (X ++ Y ++ Z).flatten = X.flatten ++ Y.flatten ++ Z.flatten :=
by
  rw [List.flatten_append, List.flatten_append]

end ListAppendAppend

section ListReplicate

lemma replicate_succ_eq_singleton_append (s : α) (n : ℕ) :
  List.replicate n.succ s = [s] ++ List.replicate n s :=
rfl

lemma replicate_succ_eq_append_singleton (s : α) (n : ℕ) :
  List.replicate n.succ s = List.replicate n s ++ [s] :=
by
  change List.replicate (n + 1) s = List.replicate n s ++ [s]
  rw [List.replicate_add]
  rfl

end ListReplicate

section ListJoin

private lemma cons_drop_succ {m : ℕ} (mlt : m < x.length) :
  x.drop m = x.get ⟨m, mlt⟩ :: x.drop m.succ :=
by
  induction' x with d l ih generalizing m
  · exfalso
    rw [length] at mlt
    exact Nat.not_lt_zero m mlt
  cases m
  · rw [get]
    simp
  rw [drop, drop, get]
  apply ih

lemma take_join_of_lt {L : List (List α)} {n : ℕ} (notall : n < L.flatten.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length,
    k < (L.get ⟨m, mlt⟩).length ∧
    L.flatten.take n = (L.take m).flatten ++ (L.get ⟨m, mlt⟩).take k :=
sorry

lemma drop_join_of_lt {L : List (List α)} {n : ℕ} (notall : n < L.flatten.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length,
    k < (L.get ⟨m, mlt⟩).length ∧
    L.flatten.drop n = (L.get ⟨m, mlt⟩).drop k ++ (L.drop m.succ).flatten :=
by
  obtain ⟨m, k, mlt, klt, left_half⟩ := take_join_of_lt notall
  use m, k, mlt, klt
  have L_two_parts := congr_arg List.flatten (List.take_append_drop m L)
  rw [List.flatten_append] at L_two_parts
  have whole := List.take_append_drop n L.flatten
  rw [left_half] at whole
  have important := Eq.trans whole L_two_parts.symm
  rw [append_assoc] at important
  have right_side := List.append_cancel_left important
  have auxi : (drop m L).flatten = (L.get ⟨m, mlt⟩ :: drop m.succ L).flatten
  · apply congr_arg
    apply cons_drop_succ
  rw [List.flatten] at auxi
  rw [auxi] at right_side
  have near_result :
    take k (L.get ⟨m, mlt⟩) ++ drop n L.flatten =
    take k (L.get ⟨m, mlt⟩) ++ drop k (L.get ⟨m, mlt⟩) ++ (drop m.succ L).flatten
  · convert right_side
    rw [List.take_append_drop]
  rw [append_assoc] at near_result
  exact List.append_cancel_left near_result

def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

infixl:100 " ^^ " => nTimes

end ListJoin

lemma mem_doubleton {a b c : α} :
  a ∈ [b, c] ↔ a = b ∨ a = c :=
by
  rw [List.mem_cons, List.mem_singleton]

variable [DecidableEq α]

section ListCountIn

def countIn (l : List α) (a : α) : ℕ :=
  List.sum (List.map (fun s => ite (s = a) 1 0) l)

lemma countIn_nil (a : α) :
  countIn [] a = 0 :=
rfl

lemma countIn_cons (a b : α) :
  countIn (b::x) a = ite (b = a) 1 0 + countIn x a :=
by
  unfold countIn
  rw [List.map_cons]
  rw [List.sum_cons]

lemma countIn_append (a : α) :
  countIn (x ++ y) a = countIn x a + countIn y a :=
by
  unfold countIn
  rw [List.map_append]
  sorry--rw [List.sum_append]

lemma countIn_replicate_eq (a : α) (n : ℕ) :
  countIn (List.replicate n a) a = n :=
by
  unfold countIn
  induction' n with m ih
  · rfl
  rw [List.replicate_succ, List.map_cons, List.sum_cons, ih, if_pos rfl]
  apply Nat.one_add

lemma countIn_replicate_neq {a b : α} (hyp : a ≠ b) (n : ℕ) :
  countIn (List.replicate n a) b = 0 :=
by
  unfold countIn
  induction' n with m ih
  · rfl
  rw [List.replicate_succ, List.map_cons, List.sum_cons, ih, Nat.add_zero, ite_eq_right_iff]
  intro impos
  exfalso
  exact hyp impos

lemma countIn_singleton_eq (a : α) :
  countIn [a] a = 1 :=
List.countIn_replicate_eq a 1

lemma countIn_singleton_neq {a b : α} (hyp : a ≠ b) :
  countIn [a] b = 0 :=
List.countIn_replicate_neq hyp 1

lemma countIn_pos_of_in {a : α} (hyp : a ∈ x) :
  countIn x a > 0 :=
by
  induction' x with d l ih
  · exfalso
    rw [List.mem_nil_iff] at hyp
    exact hyp
  by_contra contr
  rw [not_lt] at contr
  rw [Nat.le_zero] at contr
  rw [mem_cons] at hyp
  unfold countIn at contr
  unfold List.map at contr
  simp at contr
  cases' hyp with a_eq_d a_in_l
  · exact contr.left a_eq_d.symm
  specialize ih a_in_l
  have zero_in_tail : countIn l a = 0
  · unfold countIn
    exact contr.right
  rw [zero_in_tail] at ih
  exact Nat.lt_irrefl 0 ih

lemma countIn_zero_of_notin {a : α} (hyp : a ∉ x) :
  countIn x a = 0 :=
by
  induction' x with d l ih
  · rfl
  unfold countIn
  rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, ite_eq_right_iff]
  constructor
  · simp only [Nat.one_ne_zero]
    exact (List.ne_of_not_mem_cons hyp).symm
  · exact ih (List.not_mem_of_not_mem_cons hyp)

lemma countIn_join (L : List (List α)) (a : α) :
  countIn L.flatten a = List.sum (List.map (fun w => countIn w a) L) :=
by
  induction' L with d l ih
  · rfl
  · rw [List.flatten, List.countIn_append, List.map, List.sum_cons, ih]

end ListCountIn

end List
