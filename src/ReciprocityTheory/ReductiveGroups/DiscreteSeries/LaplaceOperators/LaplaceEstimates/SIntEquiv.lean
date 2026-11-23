module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.PsiGen

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.EquivA

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem equivA_measurable_rmulF (a : Mat k r) : Measurable (rmulF a : Mt k r → Mt k r) := by
  have : Continuous (rmulF a : Mt k r → Mt k r) := by
    unfold rmulF
    exact Continuous.matrix_mul continuous_id continuous_const
  exact this.measurable

theorem equivA_measurable_conjM (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) := by
  have : Continuous (conjM a : Mt k r → Mt k r) := by
    unfold conjM
    exact Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const
  exact this.measurable

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem shift_measurePreserving (hSF : HaarUniqueSF) (hCW : ClosedW) (hHW : HaarWExists) (hCN : ClosedN)
    (hHN : HaarNExists) (hc : ConjInvRaw) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW μN : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    MeasurePreserving (fun p : Mt k r × Mt k r =>
      Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r) (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r))
      (μW.prod μN) (μW.prod μN) := by
  have hW' := isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW
  have hN' := haarUp_N hSF hCN hHN hN
  have hσW : SigmaFinite μW := hW.1
  have hσN : SigmaFinite μN := hN.1
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hconj := conjInv_N hSF hCN hHN hc hz hT hN h₀⁻¹ hi
  have h1 : MeasurePreserving (rmulF h₀ : Mt k r → Mt k r) μW μW :=
    ⟨equivA_measurable_rmulF h₀, hW'.right h₀ hh₀⟩
  have h2 : MeasurePreserving (fun x : Mt k r => rmulF m₀ (conjM h₀⁻¹ x)) μN μN :=
    (⟨equivA_measurable_rmulF m₀, hN'.right m₀ hm₀⟩ : MeasurePreserving (rmulF m₀ : Mt k r → Mt k r) μN μN).comp
      ⟨equivA_measurable_conjM h₀⁻¹, hconj⟩
  have h3 := h1.prod h2
  convert h3 using 1
  funext p
  simp only [Prod.map, rmulF, conjM, Matrix.nonsing_inv_nonsing_inv _ hu]
  rfl

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem integrand_shift (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (c : Fin r → ℂ)
    {π : Lap.Mat k r → (Vp →L[ℂ] Vp)} (hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π) (f : Lap.Mat k r → ℂ) (ξ : Vp)
    {h₀ m₀ g h m : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) :
    f (h * m * (h₀ * m₀ * g)) • Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π h m ξ =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (f (h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g) •
        Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π (h * h₀) (h₀⁻¹ * m * h₀ * m₀) ξ) := by
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hhi : h⁻¹ ∈ UWset k r z := uw_inv hh
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hii : h₀⁻¹⁻¹ = h₀ := Matrix.nonsing_inv_nonsing_inv _ hu
  have hcN : h₀⁻¹ * m * h₀ ∈ Nset k r := by
    have := (hUN k r z hz h₀⁻¹ hi m hm).1
    rwa [hii] at this
  have hψ : Formalism.MainNotions.S.psiGen k r z c (h₀⁻¹ * m * h₀ * m₀) =
      Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m₀ := by
    rw [psiGen_mul hz c hcN hm₀]
    congr 1
    have := psiGen_conj hz c hi hm
    rwa [hii] at this
  have hmat : h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * m * (h₀ * m₀ * g) := by
    have e : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * (h₀ * h₀⁻¹) * m * (h₀ * m₀ * g) := by
          simp only [Matrix.mul_assoc]
      _ = h * m * (h₀ * m₀ * g) := by rw [e, Matrix.mul_one]
  have hπ1 : π h₀ (π (h * h₀)⁻¹ ξ) = π h⁻¹ ξ := by
    rw [Matrix.mul_inv_rev, hπ.1.2 _ hi _ hhi, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← hπ.1.2 _ hh₀ _ hi, Matrix.mul_nonsing_inv _ hu, hπ.1.1, one_apply_eq_self]
  have hn : Formalism.MainNotions.S.psiGen k r z c m₀ * star (Formalism.MainNotions.S.psiGen k r z c m₀) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiGen_norm]
    simp
  unfold Lap.chiInv
  have key : ∀ F : ℂ, F * star (Formalism.MainNotions.S.psiGen k r z c m) = Formalism.MainNotions.S.psiGen k r z c m₀ *
      (F * (star (Formalism.MainNotions.S.psiGen k r z c m₀) * star (Formalism.MainNotions.S.psiGen k r z c m))) := fun F => by
    linear_combination (-(F * star (Formalism.MainNotions.S.psiGen k r z c m))) * hn
  rw [hmat, hψ, map_smul, map_smul, hπ1]
  simp only [smul_smul, star_mul]
  congr 1
  exact key _

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SIntEquiv

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ}

def biEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := (a * Matrix.of x * b : Mat k r)
  invFun x := (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.mul_nonsing_inv _ hb,
      Matrix.mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha, Matrix.nonsing_inv_mul _ hb,
      Matrix.mul_one]
  measurable_toFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable

theorem sInt_equiv {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
    [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Mt k r)} (hB : IsBData z c u π μW μN) (f : Mat k r → ℂ) (ξ : Vp) (g : Mat k r)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ g) := by
  obtain ⟨hz, hT, -, hHC, hW, hN⟩ := hB
  have hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π := hcTypeW_uRep k r z u Vp π hz hT hHC
  have hMP := Mult1.S0.A.shift_measurePreserving Mult1.haarUniqueSF' Formalism.FourierDecayAlt.P.weyl_subgroup_closed
    Formalism.FourierDecayAlt.P.weyl_haar_exists Formalism.FourierDecayAlt.P.unipotent_radical_closed Formalism.FourierDecayAlt.P.unipotent_haar_exists
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof hz hT hW hN hh₀ hm₀
  have hd := TransportGeo.uh_det hh₀.1
  have hdm := TransportGeo.uh_det hm₀.1
  let e := MeasurableEquiv.prodCongr (biEquiv (1 : Mat k r) h₀ (by simp) hd)
    (biEquiv h₀⁻¹ (h₀ * m₀) (TransportGeo.uh_det (TransportGeo.uh_inv hh₀.1))
      (TransportGeo.uh_det (TransportGeo.uh_mul hh₀.1 hm₀.1)))
  have he : (fun p : Mt k r × Mt k r => Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r)
      (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r)) = e := by
    funext p
    refine Prod.ext ?_ ?_
    · show (Matrix.of p.1 * h₀ : Mat k r) = 1 * Matrix.of p.1 * h₀
      rw [Matrix.one_mul]
    · exact Matrix.mul_assoc _ h₀ m₀
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  set F : Mt k r × Mt k r → Vp := fun p => f (Matrix.of p.1 * Matrix.of p.2 * g) •
    chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  let L : Vp →ₗᵢ[ℂ] Vp := ⟨(π h₀ : Vp →ₗ[ℂ] Vp), hπ.2.1 h₀ hh₀⟩
  have h1 : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      ∫ p, Formalism.MainNotions.S.psiGen k r z c m₀ • L (F (e p)) ∂(μW.prod μN) := by
    unfold sInt
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [← he]
    exact Mult1.S0.A.integrand_shift Formalism.FourierDecayAlt.P.weyl_subgroup_closed Formalism.FourierDecayAlt.P.unipotent_radical_closed
      Formalism.QuantumDeterminants.unitary_weyl_normal_holds hz c hπ f ξ hh₀ hm₀ hp.1 hp.2
  rw [he] at hMP
  rw [h1, integral_smul, L.integral_comp_comm (fun p => F (e p)), hMP.integral_comp' F]
  rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end
end
