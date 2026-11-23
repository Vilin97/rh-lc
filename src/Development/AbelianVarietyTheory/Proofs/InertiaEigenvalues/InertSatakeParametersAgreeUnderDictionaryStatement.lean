module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeHeckeEigenvaluesAlgebraicAutomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNeZeroOfSameTransformStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_inertDatum_of_involution_uniformizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  first | exact @GlobalTheory.InertDatumGiven.exists_inertDatum_of | exact GlobalTheory.InertDatumGiven.exists_inertDatum_of | (intros; apply GlobalTheory.InertDatumGiven.exists_inertDatum_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInertStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  first | exact @GlobalTheory.InertSatake.sph_iff_isSat | exact GlobalTheory.InertSatake.sph_iff_isSat | (intros; apply GlobalTheory.InertSatake.sph_iff_isSat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUn

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSatakeGiven

theorem continuous_of_valuation_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_hasSatAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  intro L _ _ _ n U hU w hun hns s ϖ q hs hI hph
  have hsph : (GlobalTheory.DefU.AU.mk ⟨U, hU⟩).Sph w := (GlobalTheory.DefU.AU.sph_mk _ w).2 hph
  obtain ⟨α0, hα⟩ := (GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert L n _ w hun hns).1 hsph
  rw [GlobalTheory.DefU.AU.isSat_mk] at hα
  obtain ⟨s', ϖ', q', hs', hI', hsat⟩ := hα
  have hss : s' = s := by
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap L w).equalizer (continuous_of_valuation_eq s' hI'.2.1)
      (continuous_of_valuation_eq s hI.2.1) (funext fun k => ?_)
    simp only [Function.comp_apply, hs', hs]
  subst hss
  have hqq : q' = q := Nat.pow_left_injective (n := 2) (by norm_num) (hI'.2.2.2.2.2.2.symm.trans hI.2.2.2.2.2.2)
  subst hqq
  obtain ⟨b, hb, hbJ, p, hp, σ, hc, hS⟩ := hsat
  exact ⟨α0, b, hb, hbJ, p, hp, σ, hc, hS.1, fun x hx h0 => (hS.2 x hx h0).of_unif hI' hI⟩

end GlobalTheory.InertSatakeGiven

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUnStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  first | exact @GlobalTheory.InertSatakeGiven.exists_hasSatAt | exact GlobalTheory.InertSatakeGiven.exists_hasSatAt | (intros; apply GlobalTheory.InertSatakeGiven.exists_hasSatAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolutionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inert_of_unramifiedIsometricInvolution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  first | exact @GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | exact GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | (intros; apply GlobalTheory.InertOfUnramInv.inert_of_isUnramInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isUnramified_of_sphericalVector_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → IsUnramU U w := by
  first | exact @GlobalTheory.UnramDict.isUnramU_of_sphAt | exact GlobalTheory.UnramDict.isUnramU_of_sphAt | (intros; apply GlobalTheory.UnramDict.isUnramU_of_sphAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionary

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertDict

theorem satake_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  intro L _ _ _ n F π U hD v w hO
  refine ⟨GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO, fun s ϖ q hs hU => ?_⟩
  obtain ⟨hun, hns, hq⟩ := GlobalTheory.T.inert_of_unramifiedIsometricInvolution L v w hO s ϖ q hs hU
  refine ⟨GlobalTheory.T.exists_inertDatum_of_involution_uniformizer L n v w hO hun hns s ϖ hs (hq ▸ hU), fun Dv α hσ hϖ hsat => ?_⟩
  have hsph : π.SphAt v := by
    obtain ⟨f, hf, hf0, U0, hU0, hU0', -⟩ := hsat
    exact ⟨f, hf, hf0, fun κ hκ ht => hU0 κ ((hU0' κ ht).2 hκ)⟩
  obtain ⟨α0, h0⟩ := GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary L n U hD.1 w hun hns s ϖ q hs hU (GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO hsph)
  subst hσ hϖ hq
  have heq := GlobalTheory.T.inertSatake_heckeEigenvalues_algebraic_automorphic L n F π U hD v w hO Dv α hsat α0 h0
  have hnz := GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform (w.adicCompletion L) Dv.ϖ Dv.σw _ n hU α α0 heq
  refine ⟨fun i => Units.mk0 (α i) (hnz i), fun i => rfl, ?_⟩
  obtain ⟨b, hb, hb2, p, hp, σ, hc, hs1, hs2⟩ := h0
  refine ⟨b, hb, hb2, p, hp, σ, hc, hs1, fun x hx hx0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hs2 x hx hx0
  refine ⟨a1, a2, fun h hh => ?_⟩
  rw [a3 h hh, ← heq h hh]
  rfl

end GlobalTheory.InertDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inert_satake_parameters_agree_under_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  first | exact @GlobalTheory.InertDict.satake_agree | exact GlobalTheory.InertDict.satake_agree | (intros; apply GlobalTheory.InertDict.satake_agree <;> assumption)
end
end
