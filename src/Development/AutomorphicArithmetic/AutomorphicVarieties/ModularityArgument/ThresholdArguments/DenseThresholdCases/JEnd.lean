module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartLinkAltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoOfDet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeIdealEnd
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdBornJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjTor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ProjectedFormsLinkOfPrintedHida

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd1W

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.GalN.V
theorem UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 L),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
    intro w
    have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L
      (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
        obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
        ext x
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
    have hbot : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
    have he := UpperTheory.V.CF.ineCard.1 (Lp L) L w
    rw [hbot, Subgroup.card_bot] at he
    exact Ideal.ramificationIdx_eq_one_iff.1 he.symm
  refine fun x h hx ha => ?_
  · obtain ⟨lam, ρ, hc, hs, hP, hr⟩ := _root_.hecke_ideal_end H hn hJ x h hx ha
    have hc' : Continuous (ρ.comp V.pr) := hc.comp (V.pr_cont W.continuous_resP)
    have hs' : Formalism.MainNotions.N.IsSSRep (ρ.comp V.pr) := by
      intro M hM
      obtain ⟨M', hM', hcompl⟩ := hs M (fun g => by
        obtain ⟨g', rfl⟩ := hpr g
        exact hM g')
      exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
    obtain ⟨σ, hσ, hlg, -⟩ := hP.aut
    exact ⟨_, hc', hs', hr,
      _root_.UpperTheory.V.Z.Win.Gu.endShape'_alt H L Ω hunr l s.odd ι n hn σ hσ _ hc' hs' hlg⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEndOf

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
theorem UpperTheory.Gal.projectedFormsSystemPart.arithPointDecomposition_and_irrAutomorphic_of_isJ (hL : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J ∧ IrrArithPointsAutomorphicAway B ι J :=
  fun H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ =>
    ⟨_root_.UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ H l L Ω s n hn V Q c r ι B Λ R K hS J hJ,
      _root_.UpperTheory.Gal.projectedFormsSystemPart.irrArithPointsAutomorphicAway_of_isJ H (hL H) (_root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results H.toClassicalTheorems) (_root_.UpperTheory.V.Z.Ord.endOrd_of_printsH H) (_root_.UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window H.toClassicalTheorems ImaginaryQuadraticEtaCharacter.winOf) l L Ω s n hn V Q c r ι B Λ R K hS J hJ⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
theorem decomposition_and_automorphicAway_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J ∧ IrrArithPointsAutomorphicAway B ι J :=
  _root_.UpperTheory.Gal.projectedFormsSystemPart.arithPointDecomposition_and_irrAutomorphic_of_isJ _root_.UpperTheory.Gal.projectedFormsSystemPart.projected_forms_link_of_printed_hida
end UpperTheory.Gal.projectedFormsSystemPart
end
end
end
