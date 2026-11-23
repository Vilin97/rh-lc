module

public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.InitialPointNumericBound
public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.WinLvl
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthBasisLat
public import Formalism.PeriodIntegrals.DiagRank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.FirstCoefficientLeDiv
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfMinimalVector

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.DiagRank

open Finset

theorem det_one_sub_p_ne {p : ℕ} [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (1 - (p : ℤ_[p]) • M).det ≠ 0 := by

  intro h0
  have h1 := congrArg (PadicInt.toZMod (p := p)) h0
  rw [RingHom.map_det, map_zero] at h1
  have hI : (PadicInt.toZMod (p := p)).mapMatrix (1 - (p : ℤ_[p]) • M) = 1 := by
    ext i j
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [hI, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem exists_int_mul {p : ℕ} [Fact p.Prime] (D : ℤ) (x : ℚ_[p]) (hx : x ≠ 0 → D < x.valuation) :
    ∃ u : ℤ_[p], x = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hv := hx h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (D + 1) ≠ 0 := zpow_ne_zero _ hp0
  have hnp : ‖(p : ℚ_[p]) ^ (D + 1)‖ = (p : ℝ) ^ (-(D + 1)) := by
    rw [norm_zpow, Padic.norm_p, inv_zpow', zpow_neg]
  refine ⟨⟨x / (p : ℚ_[p]) ^ (D + 1), ?_⟩, ?_⟩
  · rw [PadicInt.mem_subring_iff, norm_div, hnp, Padic.norm_eq_zpow_neg_valuation h0]
    rw [div_le_one (zpow_pos (by linarith) _)]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  · show x = (p : ℚ_[p]) ^ (D + 1) * (x / (p : ℚ_[p]) ^ (D + 1))
    field_simp

open Classical in
theorem diagRank : PI.DiagRank := by
  unfold PI.DiagRank
  intro p _ n m X Y c D h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ hp0
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m),
      S = Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D) := ⟨_, rfl⟩
  rw [← hS]
  have hsplit : ∀ a, a ∉ S → ∃ u : ℤ_[p], c a = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
    intro a ha
    apply exists_int_mul D (c a)
    intro hc
    by_contra hle
    exact ha (by rw [hS]; simp [hc, not_lt.mp hle])
  choose! u hu using hsplit

  obtain ⟨s, hs⟩ : ∃ s : Fin m → ℚ_[p], s = fun a => if a ∈ S then c a / (p : ℚ_[p]) ^ D else 0 :=
    ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : Fin m → ℤ_[p], u' = fun a => if a ∈ S then 0 else u a := ⟨_, rfl⟩
  have key : ∀ a, c a = (p : ℚ_[p]) ^ D * s a + (p : ℚ_[p]) ^ (D + 1) * (u' a : ℚ_[p]) := by
    intro a
    by_cases ha : a ∈ S
    · simp [hs, hu', ha]; field_simp
    · simp [hs, hu', ha, hu a ha]
  have hent : ∀ i j, ∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) =
      (if i = j then 1 else 0) - (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by
    intro i j
    have h1 := h i j
    have h2 : ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = (p : ℚ_[p]) ^ D *
        (∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) +
          (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p])) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [key a, zpow_add₀ hp0, zpow_one]
      ring
    have h3 : (if i = j then (p : ℚ_[p]) ^ D else 0) = (p : ℚ_[p]) ^ D * (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h2, h3] at h1
    exact eq_sub_of_add_eq (mul_left_cancel₀ hpD h1)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℤ_[p], N = fun i j => ∑ a, X i a * u' a * Y j a :=
    ⟨_, rfl⟩
  obtain ⟨Xq, hXq⟩ : ∃ Xq : Matrix (Fin n) (Fin m) ℚ_[p], Xq = fun i a => (X i a : ℚ_[p]) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin n) ℚ_[p], B = fun a j => (Y j a : ℚ_[p]) := ⟨_, rfl⟩
  have heq : Xq * Matrix.diagonal s * B = PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N) := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    subst hXq hB
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hent i j, hN]
    show _ = ((_ : ℤ_[p]) : ℚ_[p])
    have hc : ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by

      rw [show ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = PadicInt.Coe.ringHom (∑ a, X i a * u' a * Y j a) from rfl, map_sum]
      rfl
    split_ifs <;> push_cast <;> rw [hc]
  have hdet : (PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N)).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact det_one_sub_p_ne N (Subtype.ext h0)
  have hrank : (Xq * Matrix.diagonal s * B).rank = n := by
    rw [heq, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc n = (Xq * Matrix.diagonal s * B).rank := hrank.symm
    _ ≤ (Xq * Matrix.diagonal s).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal s).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {a // s a ≠ 0} := Matrix.rank_diagonal s
    _ = (Finset.univ.filter (fun a => s a ≠ 0)).card := Fintype.card_subtype _
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro a ha
      by_contra haS
      simp [hs, haS] at ha

end PI.UnitaryGroupMassFormula.DiagRank

end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiagRank

section

@[expose] public section

theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
end
end

-- Source module: Formalism.PeriodIntegrals.LatMin

section

@[expose] public section

namespace PI

open MvPolynomial

def LatMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

end PI
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne

section

@[expose] public section

namespace PI.LatMinWork

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have h1 : ‖((2 : ℤ) : ℚ_[p])‖ ≤ 1 := by
    first
      | exact Padic.norm_int_le_one 2
      | exact padicNormE.norm_int_le_one 2
  have h3 : ¬ ‖((2 : ℤ) : ℚ_[p])‖ < 1 := fun h => h2 (by
    first
      | exact Padic.norm_intCast_lt_one_iff.mp h
      | exact (Padic.norm_int_lt_one_iff_dvd 2).1 h
      | exact (padicNormE.norm_int_lt_one_iff_dvd 2).1 h)
  have := le_antisymm h1 (not_lt.1 h3)
  exact_mod_cast this

variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]

lemma bound_span (B : V → V → ℚ_[p])
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (S : Set V) (w : V) (M : ℝ) (hM : 0 ≤ M) (hS : ∀ b ∈ S, ‖B b w‖ ≤ M) :
    ∀ v ∈ Submodule.span ℤ_[p] S, ‖B v w‖ ≤ M := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : B 0 w = 0 := by simpa using hsm 0 0 w
    rw [h0, norm_zero]; exact hM
  | add x y _ _ hx hy =>
    rw [hadd]
    exact (show ‖B x w + B y w‖ ≤ max ‖B x w‖ ‖B y w‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [hsm, norm_mul]
    have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
      first
        | exact c.2
        | simpa using PadicInt.norm_le_one c
    calc ‖(c : ℚ_[p])‖ * ‖B x w‖ ≤ 1 * ‖B x w‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hx

theorem main (hp2 : p ≠ 2) (B : V → V → ℚ_[p]) (L : Submodule ℤ_[p] V) (hL : L.FG)
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (hsym : ∀ u ∈ L, ∀ v ∈ L, B u v = B v u) (hne : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) :
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨u0, hu0, v0, hv0, hne0⟩ := hne
  have hSL : ∀ a ∈ S, a ∈ L := fun a ha => hS ▸ Submodule.subset_span ha
  have hB0 : ∀ v, B 0 v = 0 := fun v => by simpa using hsm 0 0 v
  have hSn : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · subst h
      rw [Finset.coe_empty, Submodule.span_empty] at hS
      rw [← hS, Submodule.mem_bot] at hu0
      subst hu0
      exact absurd (hB0 v0) hne0
    · exact h
  obtain ⟨q, hq, hqmax⟩ := (S ×ˢ S).exists_max_image (fun q : V × V => ‖B q.1 q.2‖) (hSn.product hSn)
  obtain ⟨a, b⟩ := q
  have ha : a ∈ S := (Finset.mem_product.1 hq).1
  have hb : b ∈ S := (Finset.mem_product.1 hq).2
  have hmaxS : ∀ a' ∈ S, ∀ b' ∈ S, ‖B a' b'‖ ≤ ‖B a b‖ := fun a' ha' b' hb' =>
    hqmax (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)
  have hM0 : 0 ≤ ‖B a b‖ := norm_nonneg _
  have h1 : ∀ b' ∈ S, ∀ u ∈ L, ‖B u b'‖ ≤ ‖B a b‖ := fun b' hb' u hu => by
    rw [← hS] at hu
    exact bound_span B hsm hadd (↑S) b' _ hM0 (fun a' ha' => hmaxS a' ha' b' hb') u hu
  have hbound : ∀ u ∈ L, ∀ v ∈ L, ‖B u v‖ ≤ ‖B a b‖ := by
    intro u hu v hv
    rw [hsym u hu v hv]
    have h2 : ∀ b' ∈ (S : Set V), ‖B b' u‖ ≤ ‖B a b‖ := fun b' hb' => by
      rw [hsym b' (hSL b' hb') u hu]; exact h1 b' hb' u hu
    rw [← hS] at hv
    exact bound_span B hsm hadd (↑S) u _ hM0 h2 v hv
  have hMpos : 0 < ‖B a b‖ := lt_of_lt_of_le (norm_pos_iff.2 hne0) (hbound u0 hu0 v0 hv0)
  have haL := hSL a ha
  have hbL := hSL b hb
  have hx : ∃ x ∈ L, ‖B x x‖ = ‖B a b‖ := by
    by_cases haa : ‖B a a‖ = ‖B a b‖
    · exact ⟨a, haL, haa⟩
    by_cases hbb : ‖B b b‖ = ‖B a b‖
    · exact ⟨b, hbL, hbb⟩
    have habL := L.add_mem haL hbL
    refine ⟨a + b, habL, ?_⟩
    have e : B (a + b) (a + b) = 2 * B a b + (B a a + B b b) := by
      rw [hadd, hsym a haL _ habL, hsym b hbL _ habL, hadd, hadd, hsym b hbL a haL]; ring
    have hlt : ‖B a a + B b b‖ < ‖B a b‖ := lt_of_le_of_lt (show ‖B a a + B b b‖ ≤ max ‖B a a‖ ‖B b b‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (lt_of_le_of_ne (hbound a haL a haL) haa) (lt_of_le_of_ne (hbound b hbL b hbL) hbb))
    have h2ab : ‖2 * B a b‖ = ‖B a b‖ := by rw [norm_mul, norm_two_eq_one hp2, one_mul]
    rw [e, (show ‖2 * B a b + (B a a + B b b)‖ = max ‖2 * B a b‖ ‖B a a + B b b‖ by
      first
        | exact Padic.add_eq_max_of_ne (by rw [h2ab]; exact hlt.ne')
        | exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2ab]; exact hlt.ne')), h2ab]
    exact max_eq_left hlt.le
  obtain ⟨x, hxL, hxn⟩ := hx
  have hxx : B x x ≠ 0 := fun h => by rw [h, norm_zero] at hxn; linarith
  refine ⟨x, hxL, hxx, fun u hu => ?_⟩
  have hc : ‖B u x / B x x‖ ≤ 1 := by
    rw [norm_div, hxn, div_le_one hMpos]; exact hbound u hu x hxL
  exact ⟨(⟨B u x / B x x, hc⟩ : {y : ℚ_[p] // ‖y‖ ≤ 1}), (div_mul_cancel₀ _ hxx).symm⟩

end PI.LatMinWork

namespace PI

end PI
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatMin

section

@[expose] public section

namespace PI

theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.FockGramWindow

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem restWinE_proved (D : Formalism.BasicNotions.D7) : RestWinE D := by
  intro Cc _
  refine ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨2, two_pos, fun CYb Cde Ck CD Cb a1 _ _ a4 a5 => ?_⟩⟩⟩
  intro Ckap Cs CM hCM X _ hH
  have hS : SegFacts C0 CE1 CE2 X := segFacts a1 (by linarith) (by linarith) (by linarith) (by linarith) hH
  have hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ) := by
    obtain ⟨h0, -⟩ := hH
    obtain ⟨-, hpk, -⟩ := h0
    exact hpk
  exact restWin_of_lvl (by linarith) (by linarith) (by linarith) hH CM winLvl (restWinNum_proved hS hpk CM hCM)
    (a_mem_win hS)

theorem theorem_A_closed_form_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound (restWinE_proved D)

end Formalism.MainNotions.G.GramWindowAlt

end
end
end
