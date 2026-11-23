module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt

section

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.L2.Theta

namespace Formalism.L2.SG.EvalTOntoExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)


theorem instances : SigmaFinite (X.B.I.muA X.B.μf) ∧ (X.B.I.muA X.B.μf).IsMulLeftInvariant ∧
    (X.B.I.muA X.B.μf).IsMulRightInvariant := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.muf_right X
  exact ⟨rr_muA_sigmaFinite X.B.I X.B.μf, rr_muA_left X.B.I X.B.μf, rr_muA_right X.B.I X.B.μf⟩

end Formalism.L2.SG.EvalTOntoExt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomain

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem exists_cutoff_srat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  intro D X u Fs hFs
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  haveI : DiscreteTopology (Srat X u) := Formalism.L2.SG.Pf.srat_discrete X u
  haveI : Countable (Srat X u) := Formalism.L2.SG.Pf.countable_of_discrete _
  obtain ⟨_, hleft, _⟩ := Formalism.L2.SG.EvalTOntoExt.instances X
  obtain ⟨F', hF'm, h1, h2⟩ := Formalism.L2.SG.Pf.exists_strictFund (Srat X u)
  have hF' := Formalism.L2.SG.Pf.isFund_of_strict (Srat X u) hF'm h1 h2 (X.B.I.muA X.B.μf)
  refine ⟨F'.indicator 1, measurable_one.indicator hF'm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := h1 x
    rw [tsum_eq_single (⟨s, hs⟩ : Srat X u)]
    · simp [Set.indicator_of_mem hsx]
    · intro t ht
      have hne : ((t : X.B.I.GA) * x) ∉ F' := by
        intro htx
        apply ht
        have := h2 _ hsx ((t : X.B.I.GA) * s⁻¹) ((Srat X u).mul_mem t.2 ((Srat X u).inv_mem hs))
          (by simpa [mul_assoc] using htx)
        exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
      simp [Set.indicator_of_notMem hne]
  · intro F hFm hFinv
    rw [hFs.setLIntegral_eq hF' F (fun g x => by simpa [Subgroup.smul_def, smul_eq_mul] using hFinv g g.2 x)]
    rw [← lintegral_indicator hF'm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ F' <;> simp [Set.indicator, hx]

end GlobalTheory.Core.Mi.Fold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomainStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  first | exact @GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | exact GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | (intros; apply GlobalTheory.Core.Mi.Fold.exists_cutoff_srat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomain

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unfold

theorem lintegral_unfold : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  intro D X h u ψ A B 𝓢 h𝓢 f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (D.sp.Y 0).gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (D.sp.Y 0).gram
  have hH : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hgrp := (GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).2
  have : Countable (GQ (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (D.sp.Y 0).gram
  have : Countable ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) := Function.Injective.countable
    (f := fun x : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) => (⟨x.1.1, x.2⟩ : GQ (D.sp.Y 0))) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : GQ (D.sp.Y 0) → GA D (D.sp.Y 0)) e))
  have : SMulInvariantMeasure ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (besGrp B.d B.o) B.lev.μR :=
    ⟨fun γ S _ => by
      show B.lev.μR ((fun y => (γ : besGrp B.d B.o) * y) ⁻¹' S) = B.lev.μR S
      exact measure_preimage_mul _ (γ : besGrp B.d B.o) S⟩
  have hιm : Measurable (fun s : besGrp B.d B.o => f (iotaX X h s.1)) :=
    hf.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [h𝓢.lintegral_eq_tsum'' (fun s => f (iotaX X h s.1))]
  rw [← lintegral_tsum (f := fun (γ : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (x : besGrp B.d B.o) => f (iotaX X h (γ • x).1))
    (fun γ => (hιm.comp (measurable_const_smul γ)).aemeasurable)]
  refine lintegral_congr fun s => ?_
  let e : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) ≃ Srat X u := Equiv.ofBijective
    (fun γ => ⟨iotaX X h γ.1.1, (hgrp _).1 ⟨Subgroup.mem_subgroupOf.1 γ.2, γ.1.2⟩⟩)
    ⟨fun a b e => Subtype.ext (Subtype.ext ((iotaX X h).injective (congrArg Subtype.val e))), fun σ => by
      have hm := (hgrp ((iotaX X h).symm σ)).2 (by simpa using σ.2)
      exact ⟨⟨⟨_, hm.2⟩, Subgroup.mem_subgroupOf.2 hm.1⟩, Subtype.ext (by simp)⟩⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun γ => ?_
  show f (iotaX X h ((γ : besGrp B.d B.o) * s).1) = f (iotaX X h γ.1.1 * iotaX X h s.1)
  rw [Subgroup.coe_mul, map_mul]

end GlobalTheory.Core.Mi.Unfold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomainStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  first | exact @GlobalTheory.Core.Mi.Unfold.lintegral_unfold | exact GlobalTheory.Core.Mi.Unfold.lintegral_unfold | (intros; apply GlobalTheory.Core.Mi.Unfold.lintegral_unfold <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctions

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem fold_quot : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B 𝓢 h𝓢 Fs hFs
  obtain ⟨c₁, hc₁, hL1⟩ := GlobalTheory.T.haarMeasure_disintegration_besselGroup D X h u ψ A B
  obtain ⟨β, hβm, hβ1, hβF⟩ := GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain D X u Fs hFs
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK0 : X.B.μf X.K2 ≠ 0 := hK.2.2.1.ne'
  have hKT : X.B.μf X.K2 ≠ ⊤ := hK.2.2.2.ne
  refine ⟨c₁ * (X.B.μf X.K2).toReal, mul_pos hc₁ (ENNReal.toReal_pos hK0 hKT), ?_⟩
  intro F hFm hFl hFr hFsupp
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev).1
  haveI : SigmaFinite B.lev.μR := inferInstance
  have hK2m : MeasurableSet X.K2 := (Formalism.L2.SG.Pf.DstarIdxPf.isOpen_levelSubgroup' X).measurableSet
  have hι : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
    (iotaX X h).continuous.comp continuous_subtype_val

  have key : ∀ y : X.B.I.Ginf,
      ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) * F (iotaX X h s.1 * (y, X.xu u) * (1, k))
          ∂X.B.μf ∂B.lev.μR =
        X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR := by
    intro y
    set g : X.B.I.GA := (y, X.xu u) with hg
    have e1 : ∀ s : besGrp B.d B.o,
        ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g * (1, k)) ∂X.B.μf =
          ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂X.B.μf := by
      intro s
      refine setLIntegral_congr_fun hK2m (fun k hk => ?_)
      rw [hFr k hk]
    simp_rw [e1]
    have hmeas : Measurable (Function.uncurry fun (s : besGrp B.d B.o) (k : X.B.I.Gf) =>
        β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g)) := by
      have c1 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g * (1, p.2)) :=
        ((hι.comp continuous_fst).mul continuous_const).mul (continuous_const.prodMk continuous_snd)
      have c2 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g) :=
        (hι.comp continuous_fst).mul continuous_const
      exact (hβm.comp c1.measurable).mul (hFm.comp c2.measurable)
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have e2 : ∀ k ∈ X.K2, ∫⁻ s, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂B.lev.μR =
        ∫⁻ s in 𝓢, F (iotaX X h s.1 * g) ∂B.lev.μR := by
      intro k hk
      have hf : Measurable (fun x : X.B.I.GA => β (x * g * (1, k)) * F (x * g)) :=
        (hβm.comp ((continuous_id.mul continuous_const).mul continuous_const).measurable).mul
          (hFm.comp (continuous_id.mul continuous_const).measurable)
      rw [GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain D X h u ψ A B 𝓢 h𝓢 _ hf]
      refine lintegral_congr fun s => ?_
      have e3 : ∀ σ : Srat X u, β ((σ : X.B.I.GA) * iotaX X h s.1 * g * (1, k)) * F ((σ : X.B.I.GA) * iotaX X h s.1 * g) =
          β ((σ : X.B.I.GA) * (iotaX X h s.1 * g * (1, k))) * F (iotaX X h s.1 * g) := by
        intro σ
        rw [mul_assoc (σ : X.B.I.GA) (iotaX X h s.1) g, hFl _ σ.2, mul_assoc (σ : X.B.I.GA) (iotaX X h s.1 * g)]
      simp only [e3]
      rw [ENNReal.tsum_mul_right, hβ1, one_mul]
    rw [setLIntegral_congr_fun hK2m (fun k hk => e2 k hk), setLIntegral_const, mul_comm]
  calc ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := hβF F hFm hFl
    _ = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) *
          F (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
        refine hL1 (fun x => β x * F x) (hβm.mul hFm) (fun x hx => hFsupp x ?_)
        intro h0; exact hx (by rw [h0, mul_zero])
    _ = ENNReal.ofReal c₁ * ∫⁻ y, X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
        congr 1; exact lintegral_congr key
    _ = _ := by
        rw [lintegral_const_mul' _ _ hKT, ← mul_assoc, ENNReal.ofReal_mul hc₁.le, ENNReal.ofReal_toReal hKT]

end GlobalTheory.Core.Mi.Fold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctionsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Fold.fold_quot | exact GlobalTheory.Core.Mi.Fold.fold_quot | (intros; apply GlobalTheory.Core.Mi.Fold.fold_quot <;> assumption)
end
end
