module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlace

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
namespace GlobalTheory

theorem eventually_cofinite_under_of_eventually_cofinite :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [← hw]
    rfl
  exact (hP.preimage' fun v _ => hfib v).subset fun w hw => hw

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) → ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | exact GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | (intros; apply GlobalTheory.eventually_cofinite_under_of_eventually_cofinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_normV_eq_normV_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | exact GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | (intros; apply GlobalTheory.AboveL.ResDeg.normV_eq_under_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.ConjUnder.cPl_under | exact GlobalTheory.ConjUnder.cPl_under | (intros; apply GlobalTheory.ConjUnder.cPl_under <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNormStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.NormValGen.unrAt_val_of_comp_norm | exact GlobalTheory.NormValGen.unrAt_val_of_comp_norm | (intros; apply GlobalTheory.NormValGen.unrAt_val_of_comp_norm <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.PolNorm

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem pol_norm (hjs : GlobalTheory.Published.JacquetShalikaRigidity) (hgk : GlobalTheory.Published.GelfandKazhdanDual)
    (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M]
    [IsCMField M] [Algebra K M] (a : ℕ) (ha : 1 ≤ a) (π : CuspSub K a) (π' : CuspSub M a) (χ : HChar (maximalRealSubfield K))
    (hpol : GlobalTheory.ContraPair.PolarizedPair π χ) (hbc : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk π').HasSat) :
    ∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair π' χ' ∧
      ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  obtain ⟨χ', hs, hN⟩ := GlobalTheory.T.hecke_char_norm_descent K M a χ hpol.sign
  refine ⟨χ', ⟨hs, ?_⟩, hN⟩
  apply UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hjs hgk M a ha π' (compNorm M χ')

  have hT := GlobalTheory.PolarizedSat.hasSat_conjPlace GlobalTheory.automorphicFormsFiniteGL K a π χ hpol
  have hU : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (compNorm K χ).UnrAt v :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hT' := GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places K M _ (hT.and hU)
  have hbc' := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite.eventually hbc
  filter_upwards [hT', hbc, hbc'] with w ⟨hTw, hUw⟩ hw hcw
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_normV_eq_normV_under_pow K M w
  obtain ⟨hu', hval⟩ := GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm K M (compNorm K χ) (compNorm M χ') hN w f hf hUw
  refine ⟨hu', ?_⟩
  obtain ⟨B, hB1, hB2⟩ := hw f hf
  have hcu := GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under K M w
  have hnc : normV (UpperTheory.V.Af.Bc.cPl w) = normV ((UpperTheory.V.Af.Bc.cPl w).under (𝓞 K)) ^ f := by
    rw [hcu]
    have e1 : normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
      simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj M).toRingEquiv w
    have e2 : normV (UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K))) = normV (w.under (𝓞 K)) :=
      by simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj K).toRingEquiv (w.under (𝓞 K))
    rw [e1, e2, hf]
  obtain ⟨C, hC1, hC2⟩ := hcw f hnc
  rw [hcu] at hC1
  have e := GlobalTheory.T.cuspRep_satakeParameters_unique K a (CG.mk π) _ _ _ hC1 (hTw B hB1)
  refine ⟨_, _, hB2, hC2, ?_⟩
  rw [e, hval]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, mul_pow, inv_pow, mul_inv, inv_inv]

theorem UpperTheory.Gal.NearKilling.polBC :
    GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual → PolBC := by
  intro hjs hgk K M _ _ _ _ _ _ _ a ha π P χ hpol hbc
  obtain ⟨χ', hχ', hN⟩ := pol_norm hjs hgk K M a ha π P χ hpol hbc
  refine ⟨⟨χ', hχ'⟩, fun hq => ?_⟩
  have h1 : compNorm M χ' = 1 := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    rw [hN x, hq, map_pow, compNorm_quadChar, one_pow]
    rfl
  refine ⟨fun v => ?_, ?_⟩
  · have e : (quadChar M ^ a).locInf v (-1) = (quadChar M).locInf v (-1) ^ a := rfl
    rw [e, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow]
    have h := hχ'.dual
    rwa [h1] at h
end
end
