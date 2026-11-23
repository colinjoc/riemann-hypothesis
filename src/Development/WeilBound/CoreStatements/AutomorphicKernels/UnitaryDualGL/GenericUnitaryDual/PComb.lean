module

public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace PositivityTheory.Gud.Pf

/-- A sign-symmetric list is its zero part together with its positive pairs. -/
theorem symmetric_filter_decomposition {α : Type*} (l : List (α × ℝ))
    (hl : (l.map (fun p => (p.1, -p.2))).Perm l) :
    ((l.filter (fun p => p.2 = 0)) ++
      (l.filter (fun p => 0 < p.2)).flatMap (fun p => [p, (p.1, -p.2)])).Perm l := by
  have hn := hl.filter (fun p => decide (p.2 < 0))
  simp only [List.filter_map, Function.comp_def, neg_lt_zero] at hn
  have hp := List.map_append_flatMap_perm (l.filter (fun p => 0 < p.2))
    id (fun p => [(p.1, -p.2)])
  simp only [List.map_id, ← List.map_eq_flatMap] at hp
  have hs := ((List.filter_append_perm (fun p => decide (0 < p.2))
    (l.filter (fun p => !decide (p.2 = 0)))).append_left (l.filter (fun p => p.2 = 0))).trans
      (List.filter_append_perm (fun p => decide (p.2 = 0)) l)
  simp only [List.filter_filter, ← decide_not, ← Bool.decide_and,
    not_lt, and_iff_left_of_imp ne_of_gt, ← lt_iff_le_and_ne] at hs
  exact ((hp.symm.trans (hn.append_left _)).append_left _).trans hs

theorem list_symmetric_pair_decomposition {α : Type*} : ∀ (n : ℕ) (l : List (α × ℝ)), l.length = n →
    List.Perm (l.map (fun p => (p.1, -p.2))) l →
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := by
  intro n l _ hl
  refine ⟨(l.filter (fun p => p.2 = 0)).map Prod.fst,
    l.filter (fun p => 0 < p.2), ?_, ?_⟩
  · simp [List.mem_filter, and_comm]
  · convert symmetric_filter_decomposition l hl using 2
    rw [List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro p hp
    exact Prod.ext rfl (of_decide_eq_true (List.mem_filter.mp hp).2).symm

theorem comb {α : Type*} (l : List (α × ℝ)) (hl : List.Perm (l.map (fun p => (p.1, -p.2))) l) :
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := list_symmetric_pair_decomposition l.length l rfl hl

theorem perm_ofFn {β : Type*} {h : ℕ} (x : Fin h → β) (l : List β) (hp : List.Perm l (List.ofFn x)) :
    ∃ (y : Fin h → β), List.ofFn y = l ∧ ∃ σ : Equiv.Perm (Fin h), y = fun j => x (σ j) := by
  classical
  have hlen : l.length = h := by rw [hp.length_eq, List.length_ofFn]
  subst hlen
  refine ⟨l.get, List.ofFn_get l, ?_⟩
  have key : ∀ (f : Fin l.length → β) (c : β), Fintype.card {a // f a = c} = (List.ofFn f).count c := by
    intro f c
    rw [Fintype.card_subtype, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map,
      Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun a _ => eq_comm)
  have hcard : ∀ c, Fintype.card {a // l.get a = c} = Fintype.card {b // x b = c} := by
    intro c
    rw [key, key, List.ofFn_get, hp.count_eq]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)),
    funext fun j => (Equiv.ofFiberEquiv_map _ j).symm⟩

end PositivityTheory.Gud.Pf
