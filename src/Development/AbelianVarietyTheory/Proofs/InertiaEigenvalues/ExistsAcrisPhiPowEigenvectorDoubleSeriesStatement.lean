module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntiltStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorHasSumAdicCompleteFrobenius

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem abssum_eigen_lim : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  intro l _ A _ _ φ h w hw
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(l : A)} ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  let S : ℕ → A := fun N => ∑ k ∈ Finset.range N, (l : A) ^ k * w k
  have hS : ∀ m n, m ≤ n → (l : A) ^ m ∣ S n - S m := by
    intro m n hmn
    simp only [S]
    rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro k hk
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _
  obtain ⟨W, hW⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) (M := A) inferInstance (f := S)
    (fun {m n} hmn => by rw [SModEq.sub_mem, key]; exact dvd_sub_comm.1 (hS m n hmn))
  have hWN : ∀ N, ∃ c : A, W = S N + (l : A) ^ N * c := by
    intro N
    have h1 := SModEq.sub_mem.1 (hW N)
    rw [key] at h1
    obtain ⟨c, hc⟩ := dvd_sub_comm.1 h1
    exact ⟨c, by rw [← hc]; ring⟩
  simp only [← RingHom.coe_pow] at hw ⊢
  have hSψ : ∀ N, (φ ^ h) (S N) = (l : A) * S N := by
    intro N

    simp only [S, map_sum, map_mul, map_pow, map_natCast, hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨W, ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    obtain ⟨c, hc⟩ := hWN n
    rw [hc, map_add (f := _), map_mul, map_pow, map_natCast, hSψ]
    exact ⟨(φ ^ h) c - (l : A) * c, by ring⟩
  · intro Θ hΘ
    have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
      rw [show (l : ℂ_[l]) = (((l : ℚ_[l])) : ℂ_[l]) by simp, PadicComplex.norm_extends', Padic.norm_p]
    have hlt : ‖(l : ℂ_[l])‖ < 1 := by
      rw [hl]
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Fact.out : l.Prime).one_lt
    have hbound : ∀ k, ‖(l : ℂ_[l]) ^ k * Θ (w k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hΘ _)
    have hsum : Summable (fun k => (l : ℂ_[l]) ^ k * Θ (w k)) :=
      Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hlt) hbound
    rw [hsum.hasSum_iff_tendsto_nat]
    have hpart : ∀ N, ∑ i ∈ Finset.range N, (l : ℂ_[l]) ^ i * Θ (w i) = Θ (S N) := by
      intro N

      simp [S, map_sum, map_mul, map_pow, map_natCast]
    simp only [hpart]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt)
    obtain ⟨c, hc⟩ := hWN N
    rw [hc, map_add (f := _), sub_add_cancel_left, norm_neg, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hΘ _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  first | exact @GlobalTheory.abssum_eigen_lim | exact GlobalTheory.abssum_eigen_lim | (intros; apply GlobalTheory.abssum_eigen_lim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeries

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem exists_acris_Lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  intro l _ h y hh hy
  choose w hw hθ using fun k => GlobalTheory.T.exists_frobeniusSeries_acris_untilt l h (y k) hh (hy k)
  haveI : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := (GlobalTheory.MemLoc.acris_basic l).1
  obtain ⟨W, hW, hsum⟩ := GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius l (Acris l) (GlobalTheory.MemLoc.phiA l) h w hw
  refine ⟨W, hW, fun Θ hΘ htm j => ?_⟩
  set φ := GlobalTheory.MemLoc.phiA l
  have hS := hsum (Θ.comp (φ ^ j)) (fun a => hΘ _)
  simp only [RingHom.coe_comp, RingHom.coe_pow, Function.comp_apply] at hS
  unfold abelian₂
  rw [← hS.tsum_eq]
  congr 1
  funext k
  rw [hθ k Θ hΘ htm j]

end GlobalTheory.PSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeriesStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.exists_acris_Lam | exact GlobalTheory.PSer.exists_acris_Lam | (intros; apply GlobalTheory.PSer.exists_acris_Lam <;> assumption)
end
end
