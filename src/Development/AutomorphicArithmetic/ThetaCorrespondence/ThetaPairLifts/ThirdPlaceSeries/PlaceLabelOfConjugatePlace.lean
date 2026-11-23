module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIffStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInv

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.ConjLocCsd

theorem plMap_conj_eq {R : Ranks} (Hs : Host R) (w w' : HeightOneSpectrum (𝓞 Hs.E)) (h : IsConjPl Hs w w') :
    CT.plMap (Hs.conj : Hs.E ≃+* Hs.E) w = w' := by
  ext y
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E)
  set x := (RingOfIntegers.mapRingEquiv j).symm y with hx
  have hy : RingOfIntegers.mapRingEquiv j x = y := by rw [hx, RingEquiv.apply_symm_apply]
  have hyx : (y : Hs.E) = Hs.conj (x : Hs.E) := by rw [← hy]; rfl
  rw [← hy, CT.mem_plMap, hy]
  exact h x y hyx

theorem main : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  intro R Hs μ hμ w w' hc
  have hcsd := hμ.1 w w' hc
  obtain rfl := plMap_conj_eq Hs w w' hc
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E) with hj
  set i := CT.compEquiv j w with hi
  have hcont : Continuous i := CT.continuous_compEquiv j w
  have halg : ∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x) := fun x => CT.compEquiv_algebraMap j w x
  refine ⟨i, hcont, halg, ?_⟩
  obtain ⟨ξ, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary Hs.E μ⁻¹ w
  set ψ₁ : (w.adicCompletion Hs.E)ˣ →* ℂˣ := (μ.loc (CT.plMap j w)).comp (Units.map i.toRingHom.toMonoidHom) with hψ₁
  have h1 : IsComp μ⁻¹ w ψ₁ := by
    refine ⟨?_, fun x => ?_⟩
    · have hc' : Continuous (Units.map i.toRingHom.toMonoidHom) := Units.continuous_map hcont
      exact (ParLaws.isSmoothChar_loc μ (CT.plMap j w)).preimage hc'
    · have hu : Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap Hs.E (w.adicCompletion Hs.E)).toMonoidHom x)
          = Units.map (algebraMap Hs.E ((CT.plMap j w).adicCompletion Hs.E)).toMonoidHom (Units.map (Hs.conj : Hs.E ≃+* Hs.E).toRingHom.toMonoidHom x) := by
        apply Units.ext
        exact halg (x : Hs.E)
      rw [hψ₁, MonoidHom.comp_apply, hu]
      have := hcsd x
      exact this
  have h2 : IsComp μ⁻¹ w ((μ⁻¹).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
  have he : ψ₁ = (μ⁻¹).loc w := (huniq _ h1).trans (huniq _ h2).symm
  intro x
  have := congrArg (fun f => f x) he
  have hinv : (μ⁻¹).loc w x = (μ.loc w x)⁻¹ := rfl
  simpa only [hψ₁, MonoidHom.comp_apply, hinv] using this

end GlobalTheory.ConjLocCsd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInvStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  first | exact @GlobalTheory.ConjLocCsd.main | exact GlobalTheory.ConjLocCsd.main | (intros; apply GlobalTheory.ConjLocCsd.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminant

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LabConjPlace

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem loc_artin_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (χ : HChar E) (hu : χ.UnrAt w)
    (σ : Weil h) (hσ : (σ : G E Ω) ∈ Ine (F := E) A) : χ.loc w (a σ) = 1 := by
  have h1 := ha.ord_eq σ
  rw [deg_eq_zero_iff.2 hσ, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by simp
  apply hu
  show Valued.v _ = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.LabConjPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletion

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem GlobalTheory.WeilDeligne.WDRep.rho_apply_of_mk_eq_lpOfChar {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {n : ℕ} (b : WDRep h (Fin n → ℂ)) (χ : Weil h →* ℂˣ) (hχ : WeilDeligne.IsSmooth χ)
    (hb : WD.mk b = WD.lpOfChar h χ hχ) (σ : Weil h) (v : Fin n → ℂ) : b.ρ σ v = (χ σ : ℂ) • v := by
  obtain ⟨e, h1, -⟩ := WD.mk_eq_mk.1 hb
  apply e.injective
  rw [h1, map_smul]
  ext k
  simp
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MArtinTr

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
theorem GlobalTheory.LocLanglands.artin_transport_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  intro hL E Ω _ _ _ _ _ A A' w w' h h' c j i hcA hcj hi hij a ha ε H a' ha' ε' H' ξ hξ σ σ' hσ
  set iU : (w.adicCompletion E)ˣ →* (w'.adicCompletion E)ˣ := Units.map i.toRingHom.toMonoidHom with hiU
  have hcont : Continuous iU := Units.continuous_map hi
  have hs : IsSmoothChar (ξ.comp iU) := hξ.comp iU hcont
  obtain ⟨b, b', hb, hb', -, hρ⟩ := _root_.UpperTheory.One.M.New.field hL
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h') c j i hcA hcj hi hij 1
    (IrrRep.det (Fin 1) (ξ.comp iU) hs) (IrrRep.det (Fin 1) ξ hξ) (LinearEquiv.refl ℂ ℂ) (by
      intro g v
      have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g) =
          iU (Matrix.GeneralLinearGroup.det g) := by
        ext
        simp [hiU, RingHom.map_det]
      show (LinearEquiv.refl ℂ ℂ) ((ξ.comp iU (Matrix.GeneralLinearGroup.det g) : ℂ) • v) = _
      show _ = ((ξ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g)) : ℂ) • v)
      rw [hd]
      rfl) (UpperTheory.One.M.good_ofChar _ hs)
  have e1 : WD.mk b = WD.lpOfChar h ((ξ.comp iU).comp a) (ha.smooth hs) := hb.trans (H.one _ hs)
  have e2 : WD.mk b' = WD.lpOfChar h' (ξ.comp a') (ha'.smooth hξ) := hb'.trans (H'.one _ hξ)
  have k := congrFun (congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1)) (hρ σ σ' hσ)) 0
  simp only [b.rho_apply_of_mk_eq_lpOfChar _ _ e1, b'.rho_apply_of_mk_eq_lpOfChar _ _ e2] at k
  simp at k
  exact Units.ext (by simpa [hiU] using k)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjugatePlacesCompletion

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.conjugate_places_completion_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  first | exact @_root_.GlobalTheory.LocLanglands.artin_transport_m_alt | exact _root_.GlobalTheory.LocLanglands.artin_transport_m_alt | (intros; apply _root_.GlobalTheory.LocLanglands.artin_transport_m_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelOfConjugatePlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
end GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LabConjPlace in
theorem GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  intro hPr hL D P hLab S hS i k v hw hχ u _ hlab w' hc s
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  have hw'over : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'over, P.T.tw, WD.lab_lpTw]
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin D.R.m, jj.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχdef
  set μH := P.tp.tup (D.nd.mu i) jj with hμH
  have e1 : (P.chr.e1 χ).1 = μH * P.cf.eta⁻¹ := by
    rw [hχdef, P.chr.tw, P.chr.muC i jj hjj, P.chr.etaTinv]
  have hcomp' : IsComp (P.chr.e1 χ).1 w' ((P.chr.e1 χ).1.loc w') := ⟨ParLaws.isSmoothChar_loc _ w', fun x => rfl⟩
  rw [_root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hPr.fin hL D P χ w' _ hcomp']
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')); obtain ⟨a', ha', ε', H'⟩ := hOpn) | obtain ⟨a', ha', ε', -, H'⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')
  change WD.lab _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocGL.IrrGL.ofChar ((P.chr.e1 χ).1.loc w') hcomp'.1)) = _
  rw [H'.one]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, Hw⟩ := hOpn) | obtain ⟨a, ha, ε, -, Hw⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hlab' : WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) = X - C (u : ZMod (D.host.g k)) := by
    rw [← Hw.one _ hχ]; exact hlab
  have HS : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) := by
    by_contra hn
    rw [WD.lab_of_not hn] at hlab'
    have := congrArg natDegree hlab'
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact absurd this (by norm_num)
  have hdeg : (WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ))).natDegree =
      WD.lpDim (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) := by
    rw [hlab', natDegree_X_sub_C]; simp [WD.lpOfChar]
  have htame := WD.tame_of_natDegree_lab hdeg
  rw [WD.lpOfChar] at htame
  have hwild : ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)), (σ : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) →
      ((S i _ hw).mu.comp a) σ = 1 := by
    intro σ hσ
    have := congrFun (LinearMap.congr_fun ((WD.tame_mk _).mp htame σ hσ) fun _ => 1) 0
    exact Units.ext (by simpa using this)
  have hval := (WD.lab_lpOfChar_eq_iff HS (ha.smooth hχ) hwild u).mp hlab'
  have hμw : μH.loc (D.naut.plGw k v) = (S i _ hw).mu := by
    obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E μH (D.naut.plGw k v)
    exact (huniq _ ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩).trans (huniq _ (hS.mu i _ hw jj hjj)).symm
  obtain ⟨c, hcE, hcA, hcγ⟩ := hγ2 k v w' hc
  set τc : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E) with hτc
  have hcE' : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τc x) := hcE
  have hγ' : γ k w' = GlobalTheory.ConjTransport.conjG c τc hcE' (D.ntypes.tg k v) := by
    ext y
    rw [GlobalTheory.ConjTransport.conjG_apply]
    have := hcγ (c.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hIne' : γ k w' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') := by
    rw [hγ']; exact GlobalTheory.ConjTransport.conjG_mem_Ine c τc hcE' hcA HS.2.1
  have HS' : TeichmullerInertiaLabelCondition (D.nd.plOm.1 w') w' (D.ntypes.teichC k) (γ k w') :=
    ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw'over, hIne', HS.2.2⟩
  have hcsd : IsCSD D.host μH := by
    rw [hμH, ← P.chr.muC i jj hjj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
  obtain ⟨ic, hic, hicE, hicμ⟩ := GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv D.host μH hcsd _ w' hc
  have htr : ∀ (σ : Weil (D.nd.plOm.2 (D.naut.plGw k v))) (σ' : Weil (D.nd.plOm.2 w')),
      (∀ z, c ((σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) z) = (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (c z)) →
      μH.loc w' (a' σ') = ((S i _ hw).mu (a σ))⁻¹ := by
    intro σ σ' hσ
    rw [← _root_.GlobalTheory.T.conjugate_places_completion_alt hL (D.nd.plOm.2 (D.naut.plGw k v)) (D.nd.plOm.2 w') c τc.toRingHom ic
      (fun z => (hcA z).symm) hcE' hic hicE Hw H' (μH.loc w') (ParLaws.isSmoothChar_loc _ _) σ σ' hσ, hicμ, hμw]
  have heta : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') →
      P.cf.eta.loc w' (a' σ') = 1 := fun σ' hσ' => loc_artin_ine ha' _ (P.cf.isEta.unr w') σ' hσ'
  have hξ : ∀ σ', ((P.chr.e1 χ).1.loc w') (a' σ') = μH.loc w' (a' σ') * (P.cf.eta.loc w' (a' σ'))⁻¹ := by
    intro σ'; rw [e1]; rfl
  have hwild' : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 w') →
      (((P.chr.e1 χ).1.loc w').comp a') σ' = 1 := by
    intro σ' hσ'
    have hA' : ∀ y, y ∈ D.nd.plOm.1 w' ↔ c.symm y ∈ D.nd.plOm.1 (D.naut.plGw k v) := fun y => by
      rw [hcA, RingEquiv.apply_symm_apply]
    have hσw : GlobalTheory.ConjTransport.conjG c.symm τc.symm (GlobalTheory.ConjTransport.symm_alg c τc hcE') (σ' : G _ _) ∈
        Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) :=
      GlobalTheory.ConjTransport.conjG_mem_wild c.symm τc.symm _ hA' hσ'
    let σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)) := ⟨_, Ine_le_Weil _ (Wild_le_Ine hσw)⟩
    have h1 := htr σ σ' (fun z => by
      show c (GlobalTheory.ConjTransport.conjG c.symm τc.symm _ (σ' : G _ _) z) = _
      rw [GlobalTheory.ConjTransport.conjG_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply])
    have h2 := hwild σ hσw
    rw [MonoidHom.comp_apply] at h2
    rw [MonoidHom.comp_apply, hξ, h1, heta σ' (Wild_le_Ine hσ'), h2]
    simp
  rw [WD.lab_lpOfChar_eq_iff HS' _ hwild']
  rw [MonoidHom.comp_apply, hξ, htr ⟨D.ntypes.tg k v, Ine_le_Weil _ HS.2.1⟩ _ (fun z => (hcγ z).symm),
    heta _ hIne', inv_one, mul_one]
  have hx : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ≠ 0 :=
    (_root_.map_ne_zero _).2 u.ne_zero
  rw [MonoidHom.comp_apply] at hval
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hval, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
