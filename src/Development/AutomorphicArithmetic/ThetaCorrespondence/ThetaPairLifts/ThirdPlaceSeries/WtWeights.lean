module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensionalStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddingsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducibleStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.MvPolynomial

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HeightCounting.FracCharZero

theorem injective_of_finite_dvr {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] :
    Function.Injective (algebraMap A B) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hker : (⊥ : Ideal B).comap (algebraMap A B) ≠ ⊥ := by
    intro h
    apply ha0
    have : a ∈ (⊥ : Ideal B).comap (algebraMap A B) := by simp [Ideal.mem_comap, ha]
    rw [h] at this
    simpa using this
  have hmax : ((⊥ : Ideal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hker
  have hbot : (⊥ : Ideal B).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) ⊥ hmax
  exact IsDiscreteValuationRing.not_a_field B (IsLocalRing.eq_maximalIdeal hbot).symm

theorem charZero_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [CharZero R]
    (f : R →+* S) (hf : Function.Injective f) : CharZero S :=
  ⟨fun m n h => by
    have : f (m : R) = f (n : R) := by simpa [map_natCast] using h
    exact Nat.cast_injective (hf this)⟩

end GlobalTheory.HeightCounting.FracCharZero

namespace GlobalTheory.HeightCounting

theorem TwR.charZero_fractionRing_O : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw),
    CharZero (FractionRing (T.O i)) := by
  intro D T i
  have h1 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    FracCharZero.injective_of_finite_dvr
  have h2 := T.O_inj i
  have h3 := IsFractionRing.injective (T.O i) (FractionRing (T.O i))
  exact FracCharZero.charZero_of_injective
    (((algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))).comp
      (algebraMap ℤ_[T.l i] (T.O0 i))) (h3.comp (h2.comp h1))

end GlobalTheory.HeightCounting
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.charZero_fractionRing_coefficientRing : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), CharZero (FractionRing (T.O i)) := by
  first | exact @GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | exact GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | (intros; apply GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | exact GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | (intros; apply GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUniqueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.highestWeight_doubleDual_coefficientSpace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  first | exact @GlobalTheory.AlgWtF.DDHw.dd_hw_unique | exact GlobalTheory.AlgWtF.DDHw.dd_hw_unique | (intros; apply GlobalTheory.AlgWtF.DDHw.dd_hw_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfIntStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  first | exact @GlobalTheory.WtComb.paramV_eq_infOf | exact GlobalTheory.WtComb.paramV_eq_infOf | (intros; apply GlobalTheory.WtComb.paramV_eq_infOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbeddingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weightTensorDualRep_dual_highestWeight_at_embedding : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ τ₀ : ι,
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) (lam τ₀).w := by
  first | exact @GlobalTheory.AlgWtF.DDHw.dd_hwAt | exact GlobalTheory.AlgWtF.DDHw.dd_hwAt | (intros; apply GlobalTheory.AlgWtF.DDHw.dd_hwAt <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalf

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.EtaTildeShift
theorem sh_half_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  intro D cf jE A t sh h
  have hE : (A.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [A.chr.etaT]; exact cf.isEta.inf⟩
  have h2 := (A.chr.infG _ _ hE (D.eTau t)).1
  have h3 : D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := h2
  rw [h3] at h
  have := (Multiset.singleton_inj.1 h).symm
  refine ⟨0, ?_⟩
  rw [this]; push_cast; ring
end GlobalTheory.EtaTildeShift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalfStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.infG_eq_half_integer : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  first | exact @_root_.GlobalTheory.EtaTildeShift.sh_half_alt | exact _root_.GlobalTheory.EtaTildeShift.sh_half_alt | (intros; apply _root_.GlobalTheory.EtaTildeShift.sh_half_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeights

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT


theorem wt_weights_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  intro _ D cf jE A _ _
  refine ⟨fun l _ j => ⟨⊥, inferInstance⟩, fun b0 b1 Sx T Sp _ => ?_⟩
  have hlam : ∀ (j : Fin D.R.m) (t : D.what₂.Tau), ∃ lam : DomWeight D.R.nV, ∀ sh : ℂ,
      D.naut.infG D.naut.etaT (embT D t) = {sh} → NG.infOf lam.w = NG.paramV D.R (D.hc t) j sh := by
    intro j t
    by_cases h : ∃ sh, D.naut.infG D.naut.etaT (embT D t) = {sh}
    · obtain ⟨sh, hs⟩ := h
      obtain ⟨lam, hl⟩ := GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt D.R (D.hc t) j sh (_root_.GlobalTheory.T.infG_eq_half_integer D cf jE A t sh hs)
      refine ⟨lam, fun sh' hs' => ?_⟩
      rw [hs, Multiset.singleton_inj] at hs'
      rw [← hs']
      exact hl
    · exact ⟨⟨fun _ => 0, antitone_const⟩, fun sh hs => absurd ⟨sh, hs⟩ h⟩
  choose lamF hlamF using hlam
  let lamD : ℕ → D.what₂.Tau → DomWeight D.R.nV := fun j t =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then lamF ⟨j - 1, by omega⟩ t else ⟨fun _ => 0, antitone_const⟩
  have hc : NX.cE D = (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) :=
    RingHom.ext fun x => (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  refine ⟨{ Wt := fun i j _ => Module.Dual (FractionRing (T.O i)) (Formalism.L2.DIV.VV (FractionRing (T.O i)) (lamD j))
            fd := fun i j _ => GlobalTheory.AlgWtF.finDualVV (lamD j)
            rhoW := fun i j b => GlobalTheory.AlgWtF.wtRepF (kEmbT D T i b) (lamD j) }, fun i j b hj hjm => ?_⟩
  haveI := GlobalTheory.T.charZero_fractionRing_coefficientRing D T i
  have hE := GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate D T i b
  have hl : lamD j = lamF ⟨j - 1, by omega⟩ := by
    simp only [lamD, dif_pos (And.intro hj hjm)]
  refine ⟨GlobalTheory.T.contragredient_isIrreducible_finiteDimensional _ _ _ _ (GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible _ _ _ _ _ _ hE), GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings _ _ _ _ _ _,
    fun k => @GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings _ _ _ _ _ _ _ _ _ _ _ _ hE (FractionRing (T.Ok i k)) _ (algKkT D T i k),
    fun t => ⟨_, hc ▸ GlobalTheory.T.weightTensorDualRep_dual_highestWeight_at_embedding _ _ _ _ _ _ hE t⟩, fun t sh lam hs hw => ?_⟩
  rw [hc] at hw
  have h1 := GlobalTheory.T.highestWeight_doubleDual_coefficientSpace_unique _ _ _ _ _ _ hE t lam hw
  rw [h1]
  show NG.infOf (lamD j t).w = _
  rw [hl]
  exact hlamF _ t sh hs
end GlobalTheory.HeightCounting.FormsStep
end
end
end
end
