/-
Copyright (c) 2026 Brooke Gill, Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill, Chi-Yun Hsu
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.List.Basic
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Languages.RegularLanguage

namespace Cslib.Language

open RegularExpression List Cslib.Automata Set Computability
open scoped Cslib.FLTS

variable {State Symbol : Type*} [Inhabited Symbol] [DecidableEq Symbol]
  [hfin : Finite State] (dfa : DA.FinAcc State Symbol)

noncomputable instance : Fintype State := Fintype.ofFinite State
#check Fintype.equivFin State
variable (i : Fin (Fintype.card State))
#check (Fintype.equivFin State).symm i
/- We use Kleene's Algorithm for DFA to prove a regular language can be expressed as a regex. -/
/-
regex_of_dfa i j k is the regex for the path from state i to state j passing through states < k.
When k = 0, i = j, the regex is ε union all characters from state i to state i.
When k = 0, i ≠ j, the regex is all characters from state i to state j.
For k + 1, the regex is the union of regex_of_dfa i j k and
regex_of_dfa i k k concat (regex_of_dfa k k k)^* concat regex_of_dfa k j k.
-/
#check Fin.cases
/-
Using Fin (Fintype.card State)+1) instead of ℕ for the domain,
and using Fin.cases might be better.
-/
noncomputable def regex_of_dfa (i j : Fin (Fintype.card State)) : ℕ → RegularExpression Symbol
  | 0 => if i = j then sorry else sorry
  | k + 1 => if k ≥ Fintype.card State then regex_of_dfa i j k else sorry

/- From Yi-Siong's PR. -/
theorem matches'_sum_map {α : Type*} (L : List α) (f : α → RegularExpression α) :
    (L.map f).sum.matches' = ⋃ x ∈ L, (f x).matches' := by
  induction L with
  | nil => simp [Language.zero_def]
  | cons b L' ih =>
    simp only [List.map_cons, List.sum_cons, matches', add_eq_sup, List.mem_cons,
      iUnion_iUnion_eq_or_left, ih]
    rfl

theorem IsRegular.regex {l : Language Symbol} (h : l.IsRegular) :
    ∃ r : RegularExpression Symbol, matches' r = l := by
  classical
  obtain ⟨State, h_fin, ⟨da, acc⟩, rfl⟩ := Cslib.Language.IsRegular.iff_dfa.mp h
  let : Fintype State := Fintype.ofFinite State
  let equiv : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let acc_List : List (Fin (Fintype.card State)) := (acc.toFinset.map equiv.toEmbedding).sort (· ≤ ·)
  let regex : RegularExpression Symbol := (acc_List.map (fun i => regex_of_dfa (equiv da.start) i (Fintype.card State))).sum
  use regex
  ext xs
  simp [regex, Acceptor.Accepts]
  /- Deal with each accepted state separately: Use `matches'_sum_map` -/




  sorry

theorem IsRegular.char (a : Symbol) : ({[a]} : Language Symbol).IsRegular := by
  rw [Cslib.Language.IsRegular.iff_dfa]
  let flts := Cslib.FLTS.mk (fun (s : Fin 3) (x : Symbol) ↦ if (s = 0 ∧ x = a) then 1 else 2)
  use Fin 3, inferInstance, ⟨DA.mk flts 0, {1}⟩
  ext xs
  induction xs using List.reverseRec with
  | nil =>
    simp only [Fin.isValue, Acceptor.mem_language, Acceptor.Accepts, Cslib.FLTS.mtr, foldl_nil,
      mem_singleton_iff, zero_ne_one, false_iff, flts]
    change [] ∉ ( { [a] } : Set (List Symbol) )
    simp
    -- Replace the above two lines by `exact fun h => nomatch h`
  | append_singleton xs x ih =>
    simp only [Fin.isValue, Acceptor.mem_language, Acceptor.Accepts, mem_singleton_iff,
      Cslib.FLTS.mtr_concat_eq] at ih ⊢
    sorry

theorem IsRegular.iff_regex {l : Language Symbol} :
    l.IsRegular ↔ ∃ r : RegularExpression Symbol, matches' r = l := by
/- Tactic proof -/
--   constructor
--   · intro h
--     exact IsRegular.regex h
--   · intro ⟨r, hr⟩
--     induction r generalizing l with
--     | zero => simp [← hr]
--     | epsilon => simp [← hr]
--     | char a => simp [← hr, IsRegular.char a]
--     | plus P Q hP hQ => simpa [← hr] using Cslib.Language.IsRegular.add (hP rfl) (hQ rfl)
--     | comp P Q hP hQ => simpa [← hr] using Cslib.Language.IsRegular.mul (hP rfl) (hQ rfl)
--     | star P hP => simpa [← hr] using Cslib.Language.IsRegular.kstar (hP rfl)
  refine ⟨fun h ↦ IsRegular.regex h, fun ⟨r, hr⟩ ↦ ?_⟩
  induction r generalizing l with
  | zero => simp [← hr]
  | epsilon => simp [← hr]
  | char a => simp [← hr, IsRegular.char a]
  | plus P Q hP hQ => simpa [← hr] using
    Cslib.Language.IsRegular.add (hP ⟨P, rfl⟩ rfl) (hQ ⟨Q, rfl⟩ rfl)
  | comp P Q hP hQ => simpa [← hr] using
    Cslib.Language.IsRegular.mul (hP ⟨P, rfl⟩ rfl) (hQ ⟨Q, rfl⟩ rfl)
  | star P hP => simpa [← hr] using Cslib.Language.IsRegular.kstar (hP ⟨P, rfl⟩ rfl)

end Language
