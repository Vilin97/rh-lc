module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.SpanBall
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ProductMoment
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.EigStrOfMem
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefFacts

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dif_neg h']
      simp
  · simp only [dif_neg h]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP.PolTop

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end

end Formalism.FourierDecayAlt.P.CutBP
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefOfOfWsp

section

@[expose] public section

noncomputable section

namespace CompanionTheory.WaveGrid.WAt

open MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants CompanionTheory.WaveGrid CompanionTheory.WaveGrid.SpanBall
open CompanionTheory.WaveGrid.MomL (mnr momL ew_sum_le)
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT KDecay Wsp Letters IsCoef wsp_orth gap_of_box CoefCC CoefEig PhZero BetaInfZero)
open scoped InnerProductSpace ENNReal

def UniqG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), IsHCParam lam →
    ∀ h : ℝ, GapAtLeast ε lam h → ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : B.Mat k r → (H' →L[ℂ] H')),
      PI.UpqRep.IsDSHpk k r ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

section one

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem kfin_map {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {σ : B.Mat k r → (H →L[ℂ] H)} {σ' : B.Mat k r → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)) {v : H} (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) :
    PI.UpqRep.IsKFinHpk (k := k) (r := r) σ' (U v) := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S.map U.toLinearEquiv.toLinearMap, inferInstance, Submodule.mem_map_of_mem hvS, ?_⟩
  rintro g hg _ ⟨x, hx, rfl⟩
  exact ⟨σ g x, hst g hg x hx, hU g hg.1 x⟩

theorem coefOf_of_wsp (hU : UniqG) (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (hg : GapAtLeast ε μ h) (hh : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h) (R : BranchingSupport.Rep k r) (hR : R.IsDS ε μ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) : BallW.CoefOf R F := by
  have key : ∃ (ι : Type) (_ : Fintype ι) (x y : ι → R.H) (X : ι → (Wq →L[ℂ] Wp)),
      (∀ i, x i ∈ R.TK ∧ y i ∈ R.TK) ∧ ∀ g ∈ B.GV k r, F g = ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i := by
    have hTK := (GlobalTheory.rep_basic_of_isDS hK k r ε μ R hR).2.2.2.2.2.2.1
    induction hF using Submodule.span_induction with
    | mem F h' =>
      obtain ⟨φ, T, ⟨H, i1, i2, i3, σ, v, w, -, hσ, hv, hw, hφ⟩, rfl⟩ := h'
      obtain ⟨U, hUσ⟩ := hU k r ε μ hR.1 h hg hh H σ hσ R.H R.σ hR.2
      refine ⟨Unit, inferInstance, fun _ => U w, fun _ => U v, fun _ => T,
        fun _ => ⟨hTK _ (kfin_map U hUσ hw), hTK _ (kfin_map U hUσ hv)⟩, fun g hg => ?_⟩
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hφ g hg, ← hUσ g hg, U.inner_map_map]
    | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, fun i => i.elim, fun g _ => by simp⟩
    | add F F' _ _ h h' =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      obtain ⟨ι', _, x', y', X', h1', h2'⟩ := h'
      refine ⟨ι ⊕ ι', inferInstance, Sum.elim x x', Sum.elim y y', Sum.elim X X', ?_, fun g hg => ?_⟩
      · rintro (i | i)
        exacts [h1 i, h1' i]
      · rw [Fintype.sum_sum_type, Pi.add_apply, h2 g hg, h2' g hg]
        rfl
    | smul c F _ h =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      refine ⟨ι, inferInstance, x, y, fun i => c • X i, h1, fun g hg => ?_⟩
      rw [Pi.smul_apply, h2 g hg, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨ι, _, x, y, X, h1, h2⟩ := key
  intro l l'
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, Fintype.card ι, fun i => x (e i), fun i => y (e i), fun i => X (e i), fun i => h1 _, fun g hg => ?_, rfl⟩
  rw [h2 g hg]
  exact (Equiv.sum_comp e fun i => ⟪x i, R.σ g (y i)⟫_ℂ • X i).symm

theorem bound_of_inCC {A : ℝ} {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : B.InCC A m F) :
    ContinuousOn F (B.GV k r) ∧ ∃ c, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨GlobalTheory.CoefZero.continuousOn_of_ckOn hc1, max c 0, le_max_right _ _, fun g hg => ?_⟩
  have h1 : B.gN g ^ A * ‖F g‖ ≤ c := hc2 [] [] (by simp) (by simp) (by simp) g hg
  have hp := BetaSesquilinearity.gN_pos hg
  rw [Real.rpow_neg hp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hp _), mul_comm]
  exact h1.trans (le_max_left _ _)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normSq_eq (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A 5 F) : B.normSq D F = ENNReal.ofReal (B.beta D F F).re := by
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := b_any_of_xi k r Wp Wq D A hA
  obtain ⟨c, hc⟩ := JCx2.sq_inCC_mono le_rfl (by norm_num : 4 ≤ 5) hF
  have hfin := (hC F F c c hF hF hc hc).1
  set g : (Fin r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _)
  have hJ : StronglyMeasurable fun q : (Fin r → ℂ) × ℂ => B7.JM D F (1, 1) q :=
    (B7.sm_JM D (bound_of_inCC hF).1).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin r → ℂ) × ℂ => ‖B7.hsL (B7.JM D F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hgm : Measurable g := by
    have e : g = fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B7.hsL (B7.JM D F (1, 1) q)‖ ^ 2 := by
      funext q
      by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
      · simp only [hg, hw, zero_mul]
      have hw' := hw
      unfold bcWeight at hw'
      split_ifs at hw' with hle
      · have hq : q ∈ B7.Q0 D := by
          refine ⟨fun a ha => left_ne_zero_of_mul hw' (Finset.prod_eq_zero (Finset.mem_univ a) ?_), ?_⟩
          · rw [ha, norm_zero, zero_pow]
            unfold Mdim
            have := a.isLt
            omega
          · refine hle.lt_or_eq.resolve_right fun h => right_ne_zero_of_mul hw' ?_
            rw [← h, sub_self, zero_pow (by omega)]
        rw [B7.JM_eq D F (1, 1) hq, bessel_function_trivial_index k r Wp Wq D F, B7.hsL_apply]
      · exact absurd rfl hw'
    rw [e]
    exact (B7.measurable_bcWeight _ _).mul (hN.pow_const 2)
  have hβ : B.beta D F F = ((∫ q, g q : ℝ) : ℂ) := by
    unfold B.beta betaBig
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    rw [inner_self_eq_norm_sq_to_K]
    push_cast [hg]
    rfl
  rw [hβ, Complex.ofReal_re, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hgm.aestronglyMeasurable]
  exact (ENNReal.ofReal_toReal hfin).symm

theorem normSq_le_sum (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type} (S : Finset ι)
    (F : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ i ∈ S, B.InCC A 5 (F i))
    (ho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B.beta D (F i) (F j) = 0) {i : ι} (hi : i ∈ S) :
    B.normSq D (F i) ≤ B.normSq D (∑ j ∈ S, F j) := by
  classical
  have e : (∑ j ∈ S, F j) = fun g => ∑ j : S, F j g := by
    funext g
    rw [Finset.sum_apply, Finset.sum_coe_sort S (fun j => F j g)]
  have hS : B.InCC A 5 fun g => ∑ j : S, F j g := JCx2.sq_inCC_sum _ _ fun j _ => hF j j.2
  have h1 : ∀ j : S, B.beta D (fun g => ∑ l : S, F l g) (F j) = B.beta D (F j) (F j) := fun j => by
    have h := CutBP.beta_sum_left D hA (fun _ : S => (1 : ℂ)) (fun l : S => F l) (fun l => hF l l.2) (hF j j.2)
      Finset.univ
    simp only [one_smul, one_mul] at h
    exact h.trans (Finset.sum_eq_single j (fun l _ hl => ho l l.2 j j.2 fun e => hl (Subtype.ext e))
      fun h => absurd (Finset.mem_univ j) h)
  have h2 := (CutBP.beta_sum_right D hA (fun j : S => F j) (fun j => hF j j.2) hS Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => h1 j)
  have h3 : ∀ j : S, 0 ≤ (B.beta D (F j) (F j)).re := fun j => by
    obtain ⟨t, ht, e⟩ := CutBP.beta_self_real D (F j)
    rw [e, Complex.ofReal_re]
    exact ht
  have h4 := normSq_eq hk D hA hS
  rw [h2, Complex.re_sum] at h4
  rw [e, h4, normSq_eq hk D hA (hF i hi)]
  have h5 := Finset.single_le_sum (f := fun j : S => (B.beta D (F j) (F j)).re) (fun j _ => h3 j)
    (Finset.mem_univ (⟨i, hi⟩ : S))
  exact ENNReal.ofReal_le_ofReal h5

end one

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem V_dmin (p : KB.Pl P Wp Wq) {f F₀ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (he : ∀ g ∈ B.GV P.k P.r, F₀ g = f g) {j : ℕ}
    (hj : j ≤ P.r) (a : ℕ) (γ : C.LPt) (h0 : mnr hj γ ^ a ≠ 0) :
    p.V (fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a • F₀ g) γ = mnr hj γ ^ a • p.V f γ := by
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ h0
    filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
    have hGq : Dmin P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) ⟨j + 1, by omega⟩ = mnr hj γ := by
      rw [BigCellZetaMinors.dmin_sgs _ hq]
      unfold Dmin mnr
      rw [h2.choose_spec.2.1]
    unfold D.orbIntegrand B.rho
    simp only [hGq, he _ (B7.sgs_mem p.T.base hq h2.choose_spec.1), ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
    rw [smul_comm]
  · simp
  · simp

theorem mnr_bigPt_ne {r j : ℕ} (hj : j ≤ r) (c : Fin (r + 1) → ℂ) (hc : D.IsLocPt (TBB.bigPt r c) (r + 1)) :
    mnr hj (TBB.bigPt r c) ≠ 0 := by
  unfold mnr
  rw [show D.ptMatN (TBB.bigPt r c) (r + 1) = _ from PBJ.Dens.ptMatN_bigPt c, PBM.hMat_one,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun a _ =>
    (hc.1 (1, c _) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨_, rfl⟩)).2

end place

theorem V_sum : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (A : ℝ), c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (ι : Type) (S : Finset ι) (F : ι → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (∀ i ∈ S, B.InCC A 5 (F i)) →
    ∀ γ, p.V (∑ i ∈ S, F i) γ = ∑ i ∈ S, p.V (F i) γ := by
  obtain ⟨c₃, H⟩ := PolTop.vector_valued_orbital_linear
  refine ⟨c₃, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p A hA ι S F hF γ
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := V_csmul p (fun _ => 0) 0 γ
    simp only [zero_smul] at this
    rw [Finset.sum_empty, Finset.sum_empty]
    exact this
  | insert i S hi ih =>
    have hS : B.InCC A 5 (∑ j ∈ S, F j) := by
      have := JCx2.sq_inCC_sum S F fun j hj => hF j (Finset.mem_insert_of_mem hj)
      convert this using 2 with g
      rw [Finset.sum_apply]
    obtain ⟨h1, c1, hc1, b1⟩ := bound_of_inCC (hF i (Finset.mem_insert_self _ _))
    obtain ⟨h2, c2, hc2, b2⟩ := bound_of_inCC hS
    have hpos : ∀ g ∈ B.GPos p.T.base, 0 ≤ B.gN g ^ (-A) := fun g hg => Real.rpow_nonneg (BetaSesquilinearity.gN_pos hg.1).le _
    have key := H P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ A hA (F i) (∑ j ∈ S, F j) (c1 + c2) (by linarith)
      (h1.mono fun g hg => hg.1) (h2.mono fun g hg => hg.1)
      (fun g hg => (b1 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg)))
      (fun g hg => (b2 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg))) 1 1
    simp only [one_smul] at key
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]
    exact key

theorem weighted : ∃ c₃ : ℝ, ∀ {t : ∀ n : ℕ, (Fin n → Bool) → ℝ}, ZuckT t → ZuckDualT t → PI.KFinSmooth → CoefCC →
    CoefEig → PhZero → BetaInfZero → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    [CompleteSpace Wp] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ε : Fin (2 * P.r + P.k + 1) → Bool)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (j : ℕ) (hj : j ≤ P.r) (a : ℕ) (A h : ℝ) (K : C.LPt → ℝ≥0∞),
    KFinDSCoef ε lam f → PI.ZuckTensor.GapAtLeast ε lam h → t _ ε + 1 + 2 * (((P.r + 1) * a : ℕ) : ℝ) < h →
    KDecay P.k P.r ε A (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) → B.AB P.k P.r ≤ A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
    (∀ ν ∈ ball _ ((P.r + 1) * a), ∀ F ∈ Wsp P.k P.r Wp Wq ε (fun s => lam s + (ν s : ℝ)),
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ K γ * TBB.jN2 p F) →
    ENNReal.ofReal (‖mnr hj γ‖ ^ (2 * a) * TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ (2 * ((P.r + 1) * a))) * K γ * momL p f hj a := by
  obtain ⟨c₃, HV⟩ := V_sum
  refine ⟨c₃, ?_⟩
  intro t hZ hZd hK h4 h5 h6 h7 P Wp Wq _ _ _ _ _ _ _ p f ε lam j hj a A h K hf hg ht hD hA hA3 γ hγ hG hB
  classical
  by_cases h0 : mnr hj γ ^ a = 0
  · rw [two_mul, pow_add, ← norm_pow, h0]
    simp
  obtain ⟨F₀, hF₀, he⟩ := Coef.kfin_wsp hf
  set q : B.Mat P.k P.r → ℂ := fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a with hq
  have hqL : q ∈ Letters P.k P.r ^ ((P.r + 1) * a) := by
    have h1 : (fun g : B.Mat P.k P.r => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩) ∈
        Letters P.k P.r ^ (P.r + 1) :=
      CompanionTheory.LimBd.Main.letters_pow_mono (show j + 1 ≤ P.r + 1 by omega)
        (CompanionTheory.LimBd.Main.det_mem_pow _ fun a b => CompanionTheory.LimBd.Main.herm_letter _ _)
    rw [pow_mul]
    exact Submodule.pow_mem_pow _ h1 a
  obtain ⟨F, hF, hsum⟩ := mul_mem_sumOn hZ hZd hqL hg ht hF₀
  set S := ball (2 * P.r + P.k + 1) ((P.r + 1) * a) with hS
  have hgν : ∀ ν ∈ S, PI.ZuckTensor.GapAtLeast ε (fun s => lam s + (ν s : ℝ)) (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) :=
    fun ν hν => gap_of_box (lam := lam) (μ := fun s => lam s + (ν s : ℝ)) (c := (((P.r + 1) * a : ℕ) : ℝ)) (fun s => by simpa using abs_ball hν s) hg
      (by linarith)
  have hcc : ∀ ν ∈ S, B.InCC A 5 (F ν) := fun ν hν => w_inCC hK h4 hD (hgν ν hν) (hF ν) 5
  have hVd : ∀ γ', mnr hj γ' ^ a ≠ 0 → p.V (∑ ν ∈ S, F ν) γ' = mnr hj γ' ^ a • p.V f γ' := fun γ' h' => by
    rw [← hsum]
    exact V_dmin p he hj a γ' h'
  have hE : ∀ ν ∈ S, TBB.jN2 p (F ν) ≤ momL p f hj a := by
    intro ν hν
    have h1 := normSq_le_sum p.hl.2.2 p.T.base hA S F hcc (fun ν₁ h₁ ν₂ h₂ hne =>
      wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _ h₁) (hgν _ h₂) (fun e => hne (funext fun s => by
        have := congrFun e s
        simp only [add_right_inj, Int.cast_inj] at this
        exact this)) (hF _) (hF _)) hν
    rw [← GlobalTheory.T.jN2_eq_normSq_base, ← GlobalTheory.T.jN2_eq_normSq_base] at h1
    refine h1.trans (lintegral_mono fun c => ENNReal.ofReal_le_ofReal ?_)
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · have hne : mnr hj (TBB.bigPt P.r c) ^ a ≠ 0 := pow_ne_zero _ (mnr_bigPt_ne hj c hc.1)
      rw [TBBx2.Tri.Ew_top p _ hc.1, TBBx2.Tri.Ew_top p _ hc.1, hVd _ hne, TBBx2.Tri.hsVec_smul, norm_smul, norm_pow]
      refine le_of_eq ?_
      rw [mul_comm 2 a, pow_mul]
      ring
    · rw [TBBx4.ew_zero_of p _ hc, TBBx4.ew_zero_of p _ hc, mul_zero]
  have hpt := ew_sum_le p f S F (fun _ => 1) (mnr hj γ ^ a) γ fun _ _ => by
    rw [← hVd γ h0, HV P Wp Wq p A hA3 _ S F hcc γ]
    simp
  simp only [norm_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hpt
  rw [norm_pow, ← pow_mul, mul_comm a 2] at hpt
  have hcard : (S.card : ℝ) ≤ ((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ ((P.r + 1) * a) := by
    exact_mod_cast card_ball _ _
  refine (ENNReal.ofReal_le_ofReal hpt).trans ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_sum_of_nonneg fun ν _ => TBBx4.ew_nonneg p _ _]
  have h2 : ∑ ν ∈ S, ENNReal.ofReal (TBB.Ew p (fun _ => 1) (F ν) (P.r + 1) [] γ) ≤
      ENNReal.ofReal (S.card : ℝ) * (K γ * momL p f hj a) := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun ν hν =>
      (hB ν hν _ (hF ν)).trans (mul_le_mul' le_rfl (hE ν hν))).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, ENNReal.ofReal_natCast]
  refine (mul_le_mul' le_rfl h2).trans ?_
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), two_mul ((P.r + 1) * a), pow_add]
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul hcard hcard (Nat.cast_nonneg _) (by positivity))) le_rfl) le_rfl

end CompanionTheory.WaveGrid.WAt
end
end
end
