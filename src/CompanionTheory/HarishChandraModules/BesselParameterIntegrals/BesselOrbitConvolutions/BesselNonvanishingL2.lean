module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeBessel
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselIntegralConvergenceOfGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.NonnegNormSums.IntegrandCont
import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
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
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingFromL2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSFdeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdSm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.OOConv
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadAOf
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadBOf
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.VanishingOfL2Equivariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFixM

-- Source module: CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeConv

section

section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem bessel_integral_convergence_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  obtain ⟨hHC, hσ, hgap, hOK, hw0, hz, hT, hc, hπ, hW, hN, hG, hQ⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  have hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0 := hw0
  have : SigmaFinite μN := hN.1
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  have ha1 : 1 + Formalism.FourierDecayAlt.ThreeDimData.AG k r < a := one_add_AG_lt_aOf hOK
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have ha : 1 ≤ a := by linarith
  have hM := Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN
  have hgr0 := hGS k r z μW μN μG νq (a - 1) hz hT hW hN hG hQ (by linarith)
  have hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN) := by
    simpa only [neg_sub] using hgr0
  have hDI : PI.WBL.Cv.BeC.DecInf σ a := by
    intro v0 hv0
    obtain ⟨C, Ws, hWs, hb⟩ := hIn.2.1 k r ε lam h H σ hHC hσ hgap hOK v0 hv0
    refine ⟨C, Ws, hWs, fun w hw x hx => ?_⟩
    have e := hb w hw x hx
    simp only [dsigW_eq_bessel_integrability] at e
    exact e
  have hB := PI.WBL.Cv.BeC.beConv_of_low z c π μW μN σ a (PI.WBL.Cv.grpAll k r z)
    (PI.WBL.Cv.sigAll k r ε lam H σ hσ') (PI.WBL.Cv.piAll k r z u Wp π hz hT hπ) (PI.WBL.Cv.psiAll k r z c hz) hM
    (fun w => Formalism.MainNotions.LeviCoordinates.discrete_series_continuousOn hσ' w) ha hgr hDI hw0'

  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    hIn.2.2.1 k r ε lam H σ hHC hσ w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')
  have hDDs : ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    have hle : Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 ≤ Formalism.MainNotions.DoubleDerivativeSmoothness.smoothSub σ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ' ha hb) hw0s hg
    intro v hv; exact hle hv
  have hAs : ∀ v, Formalism.FourierDecayAlt.ThreeDimData.IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rintro v (hv | hv)
    · exact hDDs v hv
    · exact hIn.2.2.1 k r ε lam H σ hHC hσ v hv
  obtain ⟨h1, -, h3, -, h5, h6⟩ := hB
  refine ⟨fun x hx v hv => h1 x hx v hv, fun v hv g hg m hm x hx => ?_, fun x hx v hv => h6 x hx v hv,
    fun x hx v hv => ⟨h1 v (hAs v hv) x (Or.inl hx), h5 x (Or.inl hx) v (hAs v hv)⟩⟩
  have e := h3 g hg m hm x hx v hv
  rw [ContinuousLinearMap.smul_comp] at e
  exact e

end G

end Formalism.FourierDecayAlt.P

end
end
end

-- Source module: CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DoubleCosetDecomposition

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem double_coset_decomposition : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS x hx y hy
  obtain ⟨hHC, hσ, hgap, hOK, hw0, -⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  obtain ⟨P, hP, hw⟩ := hw0
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 ε lam h H σ hHC hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  exact Formalism.MainNotions.InverseNormDecayBounds.decDD hσ' ha hD x hx y hy

end G

end Formalism.FourierDecayAlt.P

end
end
end

-- Source module: CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.KFinFormOf

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness

theorem bessel_add {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ}
    {σ : Mx k r → (H →L[ℂ] H)} {π : Mx k r → (Wp →L[ℂ] Wp)} {B B' : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B)
    (hB' : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B') :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => B x + B' x) := by
  obtain ⟨a1, a2, a3, C, Ws, hWs, hC⟩ := hB
  obtain ⟨b1, b2, b3, C', Ws', hWs', hC'⟩ := hB'
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, |C| + |C'|, Ws ++ Ws',
    fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W), fun v hv => ?_⟩
  · simp only [a1 v hv w hw, b1 v hv w hw]; abel
  · simp only [a2 c v hv, b2 c v hv, smul_add]
  · simp only [a3 g hg m hm v hv, b3 g hg m hm v hv, map_add (f := _), smul_add]
  · have hnn : ∀ L : List (List (Mx k r)),
        0 ≤ (L.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W v‖).sum := fun L =>
      List.sum_nonneg fun t ht => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
        exact norm_nonneg _
    rw [List.map_append, List.sum_append]
    have h1 := (hC v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hnn Ws))
    have h2 := (hC' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (hnn Ws'))
    have h3 := mul_nonneg (abs_nonneg C) (hnn Ws')
    have h4 := mul_nonneg (abs_nonneg C') (hnn Ws)
    refine (norm_add_le _ _).trans ?_
    nlinarith

theorem kFinForm_of (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl _ hid v hv x hx
  have hK := hIn.2.2.1
  have hvs := hK k r ε lam H σ hS.1 hS.2.1 v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hB := bessel_add
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ)
    (bessel_smul hl (-⟪l v, ξ⟫_ℂ))
  have h0 := bessel_ne_zero_of_cyclic_orbit (Sm.smoothCyc_of_kFinSmooth hK) hK k r ε lam H σ w0 Wp z c π hS.1
    hS.2.1 hS.2.2.2.2.1 _ hB (fun y hy => by
      have hadj := (hBC4 y hy v (Or.inr hv)).2
      refine ext_inner_left ℂ fun η => ?_
      have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN y v) ξ η
      rw [hadj, hid v hvs y hy] at e
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
        inner_conj_symm] at e
      rw [inner_add_right, ← e, inner_smul_right, inner_zero_right]
      ring) x hx
  rw [neg_smul, add_neg_eq_zero] at h0
  rw [h0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
end
end

-- Source module: CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.NormId

section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

namespace G

theorem normIdSm_of (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) (hMS : MeasSideP) :
    CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm := by
  intro hIn hSch k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide x hx v hv ξ
  obtain ⟨hDL, hDI, hKS, -⟩ := hIn
  obtain ⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩ := hSide
  have : SigmaFinite μW := hμW.1
  have : SigmaFinite μN := hμN.1
  have hds' : IsDSHpk k r ε lam σ := hds
  have hHaar : IsHaarOn (UH (Hpk k r)) μG := hμG
  have hq' : IsQuotMeas μG (muSof μW μN) νq := hq
  have hGr := Cv.grpAll k r z
  have hSg := Cv.sigAll k r ε lam H σ hds'
  have hPi := Cv.piAll k r z u Wp π hz hT hπ
  have hPs := Cv.psiAll k r z c hz
  have hM := hMS k r z u Wp π μW μN hz hT hπ hμW hμN
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hds hμG
  have hS : SchurOn μG σ := ⟨d, hd, hSd⟩
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  obtain ⟨ha1, hAG, hAS⟩ := thresholds hOK.2.2.1
  have hb : 0 ≤ a - 1 := by linarith
  have hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) μG :=
    hGG k r μG _ hμG hAG
  have hSS : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2))) (μW.prod μN) :=
    hGS k r z μW μN μG νq _ hz hT hμW hμN hμG hq hAG
  obtain ⟨P, hP, hn1, hmem⟩ := hw0
  have hw0' : IsLowUnitH k r ε lam σ w0 := ⟨P, hP, hn1, hmem⟩
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  have hK0 : IsKFinHpk (k := k) (r := r) σ w0 := Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0'
  have hsm0 : w0 ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds w0 hK0
  have hD : DiagonalMatrixCoefficientPowerDecay σ w0 a := hDL k r hOK.1 ε lam h H σ hlam hds hgap hOK.2.1 P hP w0 w0 hmem hmem
  have hI : DecInfU σ a := hDI k r ε lam h H σ hlam hds hgap hOK

  have hB : (∀ y ∈ smoothVecs (k := k) (r := r) σ, DecBd σ (a - 1) v y) ∧ DecBd σ (a - 1) v v := by
    rcases hv with hvD | hvK
    · exact ⟨fun y hy => decBd_DD_left hds' hSg hb (decBd_of_decInfU hI hK0 hy) v hvD,
        decBd_mono (by linarith) (decDD hds' (by linarith) hD v hvD v hvD)⟩
    · have hvs : v ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hds v hvK
      exact ⟨fun y hy => decBd_of_decInfU hI hvK hy, decBd_of_decInfU hI hvK hvs⟩
  have hfd : ∀ y : H, y ≠ 0 → fdegH μG σ y = d := fun y hy => fdegH_eq ⟨hd, hSd⟩ hy

  obtain ⟨-, heq0, him⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hw0ne hb (hB.1 w0 hsm0) hB.2
    hGg hSS ξ
  have hre : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re := by
    have h0 : 0 ≤ ∫ y, ‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) w0) v ξ‖ ^ 2 ∂νq :=
      integral_nonneg fun _ => by positivity
    rw [heq0, hfd w0 hw0ne, hn1, re_inner_swap] at h0
    have : 0 ≤ (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d := by simpa using h0
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  refine ⟨?_, him, hre⟩
  have hfd0 : PI.BesselPeriodGGP.fdegH μG σ w0 = d := hfd w0 hw0ne
  rw [hfd0]
  by_cases hx0 : x = 0
  · subst hx0
    have e0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN 0 v = 0 := by
      simp [Formalism.FourierDecayAlt.ThreeDimData.be, Formalism.FourierDecayAlt.ThreeDimData.beInt]
    unfold PI.BesselPeriodGGP.l2SG
    simp [e0]
  · obtain ⟨hint, heq, -⟩ := normId_gen_bd hds' hHaar hq' hGr hSg hPi hPs hM hS hx0 hb (hB.1 x hx) hB.2
      hGg hSS ξ
    rw [hfd x hx0, re_inner_swap] at heq
    unfold PI.BesselPeriodGGP.l2SG
    show ∫⁻ y, (‖PI.WBL.be z c π μW μN σ (σ (Matrix.of y) x) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂νq =
      ENNReal.ofReal (‖x‖ ^ 2 * (⟪ξ, PI.WBL.be z c π μW μN σ v v ξ⟫_ℂ).re / d)
    rw [← heq, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
    apply lintegral_congr
    intro y
    simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm, enorm_eq_nnnorm]

end G

end PI.WBL.NIS

end
end
end

-- Source module: CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2

section

@[expose] public section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.P

theorem decDD : DecDD := G.double_coset_decomposition
theorem beConv : BeConv := G.bessel_integral_convergence_of_growth growth_spherical_bound
theorem beBessel : BeBessel := PI.WBL.S5.G.beBessel_of growth_spherical_bound
theorem normIdSm : NormIdSm :=
  PI.WBL.NIS.G.normIdSm_of growth_spherical_bound growth_group_bound PI.WBL.NIS.measSideP
theorem kFinForm : KFinForm := kFinForm_of beConv beBessel
theorem zeroCase : ZeroCase := UnipotentHaarMeasurability.G.zeroCase_of beConv normIdSm schur_hermitian
theorem zeroCaseDD : ZeroCaseDD := UnipotentHaarMeasurability.G.zeroCaseDD_of beConv normIdSm schur_hermitian
theorem ooConv : OOConv :=
  S3dx4.G.ooConv_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound decDD beConv
theorem quadConv : QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => S3dx4.G.quadA_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound
      decDD beConv hIn D hS1 hS2 hbe hbe' hγ,
    S3dx4.G.quadB_of norm_inverse_bound growth_spherical_bound growth_group_bound decDD hIn D hS1 hbe⟩
theorem bessel_nonvanishing_L2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2 schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound decDD beConv

end CompanionTheory.D.Upq.BesselFunctionalConstruction
end
end
