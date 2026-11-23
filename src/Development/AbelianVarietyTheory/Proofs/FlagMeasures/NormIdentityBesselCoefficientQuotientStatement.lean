module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupIntegralEqInnerBesselFormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerBesselFunctionalEqIntegralSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselFubiniIntegrandProdStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableMatrixCoefficientQuotientMeasureStatement
import Mathlib.MeasureTheory.Function.L2Space
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalEquivariantUnipotentCharacter

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem Afun_isSPsiEquiv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu v hv ξ
  intro h hh m hm g hg
  have hRep : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hz : inWb k r z := hSide.1
  have hT : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hCl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hSsub : Sset k r z ⊆ GG k r := hCl.2.2.2.1.1
  have hhm : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hRep).1
  have hgu : σ g u ∈ DD σ w := hstab g hg u hu
  have hmul : σ (h * m * g) = (σ (h * m)).comp (σ g) := hRep.1.2 _ (hSsub hhm) _ hg
  have hD1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H)
    (fun g hg v hv => hstab g hg v hv) hDec (σ g u) hgu v hv).2.1 (h * m) hhm
  have hPi := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).1 h hh m hm).2
  unfold Afun
  rw [hmul, ContinuousLinearMap.comp_apply, hD1.1, hPi]
  rfl

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalEquivariantUnipotentCharacterStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFunctional_equivariant_unipotent_character : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  first | exact @GlobalTheory.SgInf.Afun_isSPsiEquiv | exact GlobalTheory.SgInf.Afun_isSPsiEquiv | (intros; apply GlobalTheory.SgInf.Afun_isSPsiEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSchurTranslatedMatrixCoefficient

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem schur_translated_coef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ σ w a μG d hStd u u₁ v t ht
  obtain ⟨_, ⟨⟨h1, hmul⟩, hiso, _⟩, _, _, ⟨_, _, hnull, _⟩, ⟨_, hS⟩, _⟩ := hStd
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hH
  have htu : IsUnit t.det := (hgrp.2.2 t ht).1
  have hti : t⁻¹ ∈ GG k r := (hgrp.2.2 t ht).2
  have htt : t * t⁻¹ = 1 := Matrix.mul_nonsing_inv t htu
  let L : H →ₗᵢ[ℂ] H := ⟨(σ t : H →ₗ[ℂ] H), fun x => hiso t ht x⟩
  have hinv : σ t (σ t⁻¹ v) = v := by
    have := hmul t ht t⁻¹ hti
    rw [htt, h1] at this
    have h' := congrArg (fun f : H →L[ℂ] H => f v) this
    simpa using h'.symm
  have hadj : ∀ x : H, ⟪v, σ t x⟫_ℂ = ⟪σ t⁻¹ v, x⟫_ℂ := by
    intro x
    have := L.inner_map_map (σ t⁻¹ v) x
    conv_lhs => rw [← hinv]
    exact this
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) =
      coef σ u v (Matrix.of y) * star (coef σ u₁ (σ t⁻¹ v) (Matrix.of y)) := by
    have hmem : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hnull
    filter_upwards [hmem] with y hy
    congr 2
    simp only [coef]
    rw [hmul t ht _ hy, ContinuousLinearMap.comp_apply, hadj]
  rw [integral_congr_ae hae]
  exact (hS u v u₁ (σ t⁻¹ v)).2

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSchurTranslatedMatrixCoefficientStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselSchur_translated_matrixCoefficient : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  first | exact @GlobalTheory.SgInf.schur_translated_coef | exact GlobalTheory.SgInf.schur_translated_coef | (intros; apply GlobalTheory.SgInf.schur_translated_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegral

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem coef_mul_inner_Afun_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w := hstab _ hy u₁ hu₁
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab
    hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1
  have hint2 := hint.apply_continuousLinearMap ξ
  have hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) =
      ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS := by
    unfold Afun be
    exact ContinuousLinearMap.integral_apply hint ξ
  have hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS := by
    rw [hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]
    congr 1; funext s; rw [inner_conj_symm]
  rw [hinner, ← integral_const_mul]
  have hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0 := hSide.2.2.2.1.2.2.1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS0
  filter_upwards [hae] with s hs
  have hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y)) :=
    hStd.2.1.1.2 _ (hSG hs) _ hy
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
  have hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y) := by
    simp only [coef, hmul, ContinuousLinearMap.comp_apply]
  rw [hc, mul_assoc]
  rfl

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegralStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  first | exact @GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | exact GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | (intros; apply GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotient

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem phiIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun y : Mt k r => coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) μG ∧
    ∫ y, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ ∂μG =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  haveI : SigmaFinite μG := hHaarG.1
  haveI : SigmaFinite μS := hHaarS.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hF := GlobalTheory.T.integrable_bessel_fubini_integrand_prod k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have haeG : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hHaarG.2.2.1
  have haeS : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaarS.2.2.1
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS :=
    haeG.mono fun y hy => GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  refine ⟨hF.integral_prod_left.congr (hae.mono fun y hy => hy.symm), ?_⟩
  rw [integral_congr_ae hae, integral_integral_swap hF]
  have hin : ∀ᵐ t ∂μS, (∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μG) =
      (⟪u₁, u⟫_ℂ / (d : ℂ)) * (⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ) := by
    filter_upwards [haeS] with t ht
    rw [integral_mul_const, GlobalTheory.T.besselSchur_translated_matrixCoefficient k r σ w a μG d hStd u u₁ v _ (hcl.2.2.2.1.1 ht)]
    ring
  rw [integral_congr_ae hin, integral_const_mul, GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm k r σ w a μG d z c π μS hStd hSide v hv ξ]
  ring

theorem innerIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν →
    ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun x : Mt k r => ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ) ν ∧
    ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hUnS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hSide.1 hSide.2.1 μS).1 hHaarS
  obtain ⟨-, hνG, -, hWeil, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHaarG hHaarS hUnS hν
  obtain ⟨hφ, hφint⟩ := phiIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  obtain ⟨hWi, hWe⟩ := hWeil ℂ _ hφ
  have haeν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := ae_iff.2 hνG
  have hae : ∀ᵐ x ∂ν, (∫ s, (fun y : Mt k r => coef σ u v (Matrix.of y) *
        ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) (lmulM (Matrix.of s) x) ∂μS) =
      ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ :=
    haeν.mono fun x hx => (GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx).symm
  refine ⟨hWi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← hWe, hφint]

theorem normIdentity_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hwD : w ∈ DD σ w := by
    have h1 := mem_DD σ w hcl.1.2.2.1
    rwa [hStd.2.1.1.1, ContinuousLinearMap.one_apply] at h1
  have hAi := GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure k r σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  obtain ⟨hIi, -⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  have hIe := (innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ).2
  have hsq : Integrable (fun x : Mt k r => ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ ^ 2) ν := by
    refine hIi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    exact inner_self_eq_norm_sq _
  obtain ⟨-, hwe⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν w hwD w hwD v hv ξ
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hL : (∫ x, ⟪Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)⟫_ℂ ∂ν)
      = ((∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hL, hww, one_mul] at hwe
  have hX : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ =
      ((d * ∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [eq_div_iff hd'] at hwe
    rw [← hwe]; push_cast; ring
  refine ⟨GlobalTheory.T.besselFunctional_equivariant_unipotent_character k r σ w a μG d z c π μS hStd hSide u hu v hv ξ, hAi,
    (memLp_two_iff_integrable_sq_norm hAi.aestronglyMeasurable).2 hsq, hIe, ?_, ?_⟩
  · rw [hX, Complex.ofReal_re]
    exact mul_nonneg hd.le (integral_nonneg fun x => by positivity)
  · rw [hX, Complex.ofReal_im]

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.norm_identity_besselCoefficient_quotient : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  first | exact @GlobalTheory.SgInf.normIdentity_besselCoef | exact GlobalTheory.SgInf.normIdentity_besselCoef | (intros; apply GlobalTheory.SgInf.normIdentity_besselCoef <;> assumption)
end
end
