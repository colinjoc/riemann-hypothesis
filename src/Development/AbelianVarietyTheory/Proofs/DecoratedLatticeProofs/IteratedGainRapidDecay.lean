module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Finset

namespace GlobalTheory.IterGain

noncomputable def words {ι : Type} [DecidableEq ι] (B : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => insert [] ((words B k ×ˢ B).image (fun p => p.1 ++ [p.2]))

theorem nil_mem {ι : Type} [DecidableEq ι] (B : Finset ι) (k : ℕ) : [] ∈ words B k := by
  cases k <;> simp [words]

theorem append_mem {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by
  exact mem_insert_of_mem (mem_image_of_mem _ (mk_mem_product hl hi))

theorem mem_letters {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by
  intro k
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp only [words, forall_mem_insert, forall_mem_image, List.forall_mem_append]
    simpa using fun l i hl => And.intro (ih l hl)

/-- The empty word and unique snocs partition each successor level. -/
theorem sum_words_snoc {ι M : Type} [DecidableEq ι] [AddCommMonoid M]
    (B : Finset ι) (k : ℕ) (c : List ι → M) :
    ∑ l ∈ words B (k + 1), c l = c [] + ∑ i ∈ B, ∑ l ∈ words B k, c (l ++ [i]) := by
  rw [words, sum_insert (by simp), sum_image (fun _ _ _ _ h =>
    Prod.ext_iff.mpr (List.append_singleton_inj.mp h)), sum_product, sum_comm]

theorem root_le {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := (pow_le_pow_iff_left₀ hx hy hm).1 h

theorem step {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    simp [words, mul_comm]
  | succ k ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := ih
    set X1 := (K / δ₀) ^ (k + 1)
    set D := K ^ k * Ck * C ^ A
    set X2 := C * K * D
    refine ⟨max X1 X2, by positivity, ?_⟩
    intro ψ hψ c hc0 hc g
    have hQg := zero_lt_one.trans_le (hQ1 g)
    set T := ∑ l ∈ words B (k + 1), c l with hT
    have hT0 : 0 ≤ T := sum_nonneg hc0
    have hqg := hq g
    obtain ⟨δ, hδ, _, hδq, hcase⟩ := hgain g
    have hδQ : δ * Q g ≤ K := by
      apply root_le hm (by positivity) (by positivity)
      simpa [mul_pow, hQm, hKm, mul_comm] using hδq
    rcases hcase with hδ0 | ⟨Ω, hΩ, hbound⟩
    · have hQM : Q g ≤ K / δ₀ := by
        rw [le_div_iff₀ hδ₀]; nlinarith
      have h0 := hc [] (nil_mem B _) g
      have hcT : c [] ≤ T := single_le_sum hc0 (nil_mem B _)
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (T * q g ^ A) * X1 := by
             dsimp only [X1]
             gcongr
             exact h0.trans (by gcongr)
        _ = X1 * q g ^ A * T := by ring
        _ ≤ max X1 X2 * q g ^ A * T := by gcongr; exact le_max_left _ _
    · set S : ι → ℝ := fun i => ∑ l ∈ words B k, c (l ++ [i])
      set P := D * q g ^ A / Q g ^ k
      have hmain : ‖ψ g‖ ≤ C * δ * (P * ∑ i ∈ B, S i) := by
        rw [mul_sum]
        apply hbound ψ hψ
        intro i hi
        have hSi : 0 ≤ S i := sum_nonneg (fun l hl => hc0 _ (append_mem hl hi))
        refine ⟨by positivity, ?_⟩
        intro w hw
        have hQw := hQ1 w
        have hqw := hq w
        have hb := hCk (Dr i ψ) (hcl ψ hψ i hi) (fun l => c (l ++ [i]))
          (fun l hl => hc0 _ (append_mem hl hi))
          (fun l hl g' => by
            simpa [List.foldr_append] using hc (l ++ [i]) (append_mem hl hi) g') w
        have hQgw : Q g ≤ K * Q w := by
          apply root_le hm hQg.le (by positivity)
          simpa [mul_pow, hQm, hKm] using (hΩ w hw).2
        dsimp only [P]
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hQg _)]
        calc ‖Dr i ψ w‖ * Q g ^ k ≤ ‖Dr i ψ w‖ * (K * Q w) ^ k := by gcongr
          _ = K ^ k * (‖Dr i ψ w‖ * Q w ^ k) := by ring
          _ ≤ K ^ k * (Ck * q w ^ A * S i) := by gcongr
          _ ≤ K ^ k * (Ck * (C * q g) ^ A * S i) := by
              gcongr
              exact (hΩ w hw).1
          _ = D * q g ^ A * S i := by dsimp [D]; ring
      have hSsum : ∑ i ∈ B, S i ≤ T := by
        rw [hT, sum_words_snoc]
        exact le_add_of_nonneg_left (hc0 [] (nil_mem B _))
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (C * δ * (P * T)) * Q g ^ (k + 1) := by
            gcongr
            exact hmain.trans (by gcongr)
        _ = C * (δ * Q g) * (D * q g ^ A * T) := by
            dsimp [P]; field_simp; ring
        _ ≤ C * K * (D * q g ^ A * T) := by gcongr
        _ = X2 * q g ^ A * T := by dsimp [X2]; ring
        _ ≤ max X1 X2 * q g ^ A * T := by gcongr; exact le_max_right _ _

end GlobalTheory.IterGain

namespace GlobalTheory

theorem exists_root_ge_one {x : ℝ} {m : ℕ} (hx : 1 ≤ x) (hm : m ≠ 0) :
    ∃ y : ℝ, 1 ≤ y ∧ y ^ m = x :=
  ⟨x ^ ((m : ℝ)⁻¹), Real.one_le_rpow hx (by positivity),
    Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hm⟩

open GlobalTheory.IterGain in
theorem iterated_gain_rapid_decay : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) →
    (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) →
    (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) →
    ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧
      ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
        ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  intro G ι B q 𝓒 Dr b C δ₀ hδ₀ hq hcl hgain A N
  classical
  let m := b + 1
  have hm : m ≠ 0 := Nat.succ_ne_zero b
  let C1 := max C 1
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hq0 : ∀ g, 0 ≤ q g := fun g => zero_le_one.trans (hq g)
  obtain ⟨K, hK1, hKm⟩ := exists_root_ge_one hC1 hm
  choose Q hQ1 hQm using fun g => exists_root_ge_one (hq g) hm
  obtain ⟨Ck, _, hCk⟩ := step B q 𝓒 Dr m C1 δ₀ K Q A hm hδ₀ hC1 hK1 hKm hq hQ1 hQm hcl
    (by
      intro g
      obtain ⟨δ, hδ, hδ1, hqδ, hcase⟩ := hgain g
      refine ⟨δ, hδ, hδ1, ?_, hcase.imp id ?_⟩
      · exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hδ.le hδ1 (Nat.le_succ b)) (hq0 g)).trans (hqδ.trans hCC1)
      · rintro ⟨Ω, hΩ, hbd⟩
        refine ⟨Ω, fun w hw => ⟨?_, ?_⟩, ?_⟩
        · exact (hΩ w hw).1.trans (by gcongr; exact hq0 _)
        · exact (hΩ w hw).2.trans (by gcongr; exact hq0 _)
        · intro ψ hψ c hc
          have hs := sum_nonneg (fun i hi => (hc i hi).1)
          exact (hbd ψ hψ c hc).trans (by gcongr)
    ) (m * (A + N))
  refine ⟨words B (m * (A + N)), Ck, mem_letters B _, ?_⟩
  intro ψ hψ c hc g
  have hqA : 0 < q g ^ A := pow_pos (zero_lt_one.trans_le (hq g)) _
  have h := hCk ψ hψ c (fun l hl =>
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hc l hl g)) hqA) hc g
  rw [pow_mul, hQm, pow_add] at h
  nlinarith only [h, hqA]

end GlobalTheory
