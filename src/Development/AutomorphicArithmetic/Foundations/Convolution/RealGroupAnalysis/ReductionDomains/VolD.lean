module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.ReductionDirichlet
import GroundTheory.AutomorphicForms.ReductionIdele
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IsClosedRangeNU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IdeleCover

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.ideleCover :
    ∀ (F : Type) [Field F] [NumberField F] (c : ℝ), 0 < c → ∃ (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C ∧ 1 < ab ρ ∧ ∀ a : IdeleGroup F, c ≤ ab a → ∃ (t : Fˣ) (n : ℕ), ∃ x ∈ C, IdeleGroup.diagonal F t * a = ρ ^ n * x := by
  intro F _ _ c hc
  set ρ : IdeleGroup F := Reduction.posIdele (K := F) 2 two_pos with hρ
  have hr : ab ρ = 2 ^ Module.finrank ℚ F := Reduction.ideleModule_posIdele (K := F) 2 two_pos
  have h1 : 1 < ab ρ := by
    rw [hr]
    exact one_lt_pow₀ one_lt_two Module.finrank_pos.ne'
  have hr0 : 0 < ab ρ := one_pos.trans h1
  obtain ⟨S, hS, hSm⟩ := Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc (c * ab ρ)
  refine ⟨S, ρ, hS, h1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx h1
  have hp : 0 < ab ρ ^ n := pow_pos hr0 n
  have hm : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ab a / ab ρ ^ n := by
    have : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ)
        = ((IdeleGroup.ideleModule F ρ : ℝ) ^ n)⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv, map_pow]
    rw [this, div_eq_inv_mul]
    rfl
  obtain ⟨t, ht⟩ := hSm ((ρ ^ n)⁻¹ * a)
    (by
      rw [hm, le_div_iff₀ hp]
      have := (le_div_iff₀ hc).1 hn1
      linarith)
    (by
      rw [hm, div_le_iff₀ hp]
      have h2 := (div_lt_iff₀ hc).1 hn2
      rw [pow_succ] at h2
      nlinarith)
  refine ⟨t, n, _, ht, ?_⟩
  rw [mul_left_comm, mul_inv_cancel_left]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.volD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F), M₀.μ M₀.D < ⊤ := by
  intro F _ _ _ M₀
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨C, ρ, hC, hρ, hcov⟩ := M.ideleCover F c hc
  obtain ⟨hSm, hfin⟩ := M.siegJ F M₀ C ρ hC hρ
  obtain ⟨⟨σ, hσ⟩, hcos⟩ := M.rowCosets F
  set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS
  set u : G1 F → ℝ≥0∞ := Set.indicator S 1 with hu
  have hum : Measurable u := measurable_one.indicator hSm
  have hSinv : ∀ (b : A F) g, nU b * g ∈ S ↔ g ∈ S := by
    have key : ∀ (b : A F) g, g ∈ S → nU b * g ∈ S := by
      rintro b g ⟨b', n, x, hx, k, hk, rfl⟩
      exact ⟨b + b', n, x, hx, k, hk, by rw [M.nU_add]; simp only [mul_assoc]⟩
    refine fun b g => ⟨fun h => ?_, key b g⟩
    have := key (-b) _ h
    rwa [M.nU_neg, inv_mul_cancel_left] at this
  have huinv : ∀ (b : A F) g, u (nU b * g) = u g := by
    intro b g
    by_cases h : g ∈ S
    · rw [hu, Set.indicator_of_mem h, Set.indicator_of_mem ((hSinv b g).2 h)]; rfl
    · rw [hu, Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hSinv b g).1 h'))]
  have hcover : ∀ g : G1 F, 1 ≤ ∑' r, u (ratS F (σ r) * g) := by
    intro g
    obtain ⟨γ, b, a, k, hk, heq, hle⟩ := hred g
    obtain ⟨t, n, x, hx, hta⟩ := hcov a hle
    have hmem : mD (IdeleGroup.diagonal F t) * ratS F γ ∈ Gam F :=
      (Gam F).mul_mem (M.mD_diag_mem t) ⟨γ, rfl⟩
    obtain ⟨⟨r, ξ⟩, hp, -⟩ := hcos σ hσ ⟨_, hmem⟩
    have hp' : mD (IdeleGroup.diagonal F t) * ratS F γ = nU (rt ξ) * ratS F (σ r) := hp
    have hin : nU (rt ξ) * (ratS F (σ r) * g) ∈ S := by
      refine ⟨((IdeleGroup.diagonal F t : (A F)ˣ) : A F) ^ 2 * b, n, x, hx, k, hk, ?_⟩
      rw [← mul_assoc, ← hp', mul_assoc, heq, ← hta, M.mD_mul, ← mul_assoc, ← mul_assoc, M.mD_mul_nU]
      simp only [mul_assoc]
    have hone : u (ratS F (σ r) * g) = 1 := by
      rw [← huinv (rt ξ), hu, Set.indicator_of_mem hin]; rfl
    calc (1 : ℝ≥0∞) = u (ratS F (σ r) * g) := hone.symm
      _ ≤ ∑' r, u (ratS F (σ r) * g) := le_tsum (fun r => u (ratS F (σ r) * g)) r
  have hfs : ∀ g, ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) = u g := by
    intro g
    simp only [huinv]
    rw [lintegral_const, Measure.restrict_apply_univ, adeleMeasure_fundamentalSet, mul_one]
  calc M₀.μ M₀.D = ∫⁻ _ in M₀.D, 1 ∂M₀.μ := by simp
    _ ≤ ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := lintegral_mono fun g => hcover g
    _ = M.J0 M₀ u := by
      rw [M.unfL F M₀ σ u hσ hum (fun ξ g => huinv _ g)]
      simp only [hfs]
    _ < ⊤ := hfin
end
end
