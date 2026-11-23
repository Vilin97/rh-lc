module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIdentityTranslatesKFiniteLargeGapStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasuresStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentitiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinNeZeroOfCwCont
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCellStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import CompanionTheory.AutomorphicTheory.RankOneTori.MatGroupOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinCoefTorusNe

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapAmpTK

open GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.GapAmpTK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.AmpTKGap

theorem isCoef_kfin_and_torus_translate : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  intro H k r L l l' κ τ hκ hτ f hf
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (GlobalTheory.AmpTK.rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hmain := (GlobalTheory.isCoef_of_translate_smul_exists H.1.1.2.2.1 k r L.ε L.lam (GlobalTheory.AmpTK.rep L) L.Wp L.Wq l l' hDS).1
  have hd := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH (k := k) (r := r) hκ hτ
  have h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ BranchingSupport.GG k r := by
    have := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd hdi
    rwa [Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ] at this
  obtain ⟨P, Q, hQ, hP, h⟩ := hf
  refine ⟨hmain f ⟨1, h1, 1, h1, P, Q, hQ, hP, fun g => ?_⟩, hmain _ ⟨_, hd, _, hdi, P, Q, hQ, hP, fun g => ?_⟩⟩
  · exact (congrArg f (by simp : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * 1 = g)).trans (h g)
  · exact (congrArg f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj_cjI hκ hτ g)).trans (h g)

end GlobalTheory.AmpTKGap

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGapStatement

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  first | exact @GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | exact GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | (intros; apply GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorOfHyps

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem kfin_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_zero {k r : ℕ} (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) :
    IsCoef (rep L) l l' (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp, by simp⟩

end GlobalTheory.AmpTK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.CellPts

theorem cell_points : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  intro k r L h μG hO hC h1 h0 hc hμG γ g μR ν hG hrep hrel hroot hq
  have hR := Formalism.MainStatements.RankOne.root_haar hO.1 L hc hrep hroot
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' g) :=
    ⟨Formalism.MainNotions.BigCellDensity.wPt γ, Formalism.MainNotions.BigCellDensity.dPt γ, Formalism.MainNotions.BigCellDensity.dPt_ne γ, by
      rw [hrep.2, ← Formalism.MainNotions.BigCellDensity.ptMatN_swap, Formalism.MainNotions.BigCellDensity.ptMatN_mono]⟩
  have hpos : 0 < Gf k r L.z L.z' g := by
    refine lt_of_le_of_ne (gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g hrep.1) fun e => hG ?_
    rw [← Formalism.MainNotions.BigCellDensity.gTie k r L.z L.z' γ g hrep.1 hrep.2, ← e]
  obtain ⟨νR, hν⟩ := Formalism.MainStatements.RankOne.quot_exists hrep.1 hμG hR
  refine ⟨hR, ⟨νR, hν⟩, ?_⟩
  exact GlobalTheory.CellMaj.cellConv k r L h μG g μR νR ν h1 hO hC ⟨hrep.1, hpos, hmono, hrel, hR, hq, hν⟩ hmono

end GlobalTheory.CellPts
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorantStatement

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.smallCell_relevant_points_haar_quotient_majorant : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  first | exact @GlobalTheory.CellPts.cell_points | exact GlobalTheory.CellPts.cell_points | (intros; apply GlobalTheory.CellPts.cell_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTKGapOne

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp GlobalTheory.AmpTK

theorem oneBesselTor_of_gapHyp : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  intro H
  obtain ⟨Cgf, hCgf⟩ := GlobalTheory.T.exists_besselCell_gap_constant
  refine ⟨Cgf, fun D => ?_⟩
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨h, hg, hok, hgc⟩ := hCgf D L.ε L.lam hgap
  have hc0 : L.c ≠ 0 := by
    rw [hc]; unfold cOfDpsi
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hκ₀.ne')
  obtain ⟨μG, hμG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn D.R.k D.R.rS
  obtain ⟨l, l', hBe, hl, hl'⟩ := GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities H _ _ L h hg hok hc0 hκN hκNt
  have hBig : ∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb D.R.k * μ = Hb D.R.k → OneAt L l l' (bigCell D.R.k D.R.rS c μ) (pairMeas L) := by
    intro c μ hc' hμ
    obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.bigCell_trivialStabiliser_and_measures _ _ L μG hok.1 hκNt hκN hc0 hμG c μ hc' hμ
    obtain ⟨b, hb0, hb, hint⟩ := GlobalTheory.T.pair_space_majorant_integrable_big_cell _ _ L h hok hgc hκNt hκN hc0 c μ hc' hμ
    exact GlobalTheory.T.besselAmplitude_identity_translates_kFinite_largeGap H _ _ L h μG l l' hg hok hc0 hμG hBe _ _ _ _ h1 h2 h3 h4 h5 b hb0 hb hint
  have hCell : ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
      (μR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OneAt L l l' g ν := by
    intro γ g μR ν h0 h1 h2 h3 h4
    obtain ⟨hR, ⟨νR, hQ⟩, b, hb0, hb, hint⟩ := GlobalTheory.T.smallCell_relevant_points_haar_quotient_majorant _ _ L h μG hok hgc hκNt hκN hc0 hμG γ g μR ν h0 h1 h2 h3 h4
    exact GlobalTheory.T.besselAmplitude_identity_translates_kFinite_largeGap H _ _ L h μG l l' hg hok hc0 hμG hBe g μR νR ν h1.1 h2 hR h4 hQ b hb0 hb hint
  obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap H _ _ L l l' κ τ hκ hτ f hf
  by_cases hs0 : s = 0
  · subst hs0
    refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ,
      fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ, fun _ => by simp⟩, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
  · have hs' := hs
    obtain ⟨m, x, y, X, hxy, -, hsdef⟩ := hs'
    have hx : ∃ x ∈ (rep L).TK, l x ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).1, inner_zero_left]
    have hy : ∃ y ∈ (rep L).TK, l' y ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).2, map_zero, inner_zero_right]
    obtain ⟨f₁, s₁, hf₁, hc₁, hs₁⟩ := GlobalTheory.GapAmpTK.exists_kFinCoef_torus_ne H _ _ L l l' κ τ hκ hτ hl hl' hx hy
    refine ⟨f₁, s₁ / s, div_ne_zero hs₁ hs0, hf₁, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]

end GlobalTheory.AmpTKGapOne
end
end
end
