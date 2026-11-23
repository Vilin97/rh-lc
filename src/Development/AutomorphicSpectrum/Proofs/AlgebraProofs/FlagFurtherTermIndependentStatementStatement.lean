module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagInd
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFrameOfFullFlag
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFurtherTermIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrict
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsLocFrac
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumIntNumLClassListEqOfIsSymmetric

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  first | exact @PositivityTheory.HtPt.Pflag.field_flag_indep | exact PositivityTheory.HtPt.Pflag.field_flag_indep
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumIntNumLClassListEqOfIsSymmetricStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric | exact GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric | (intros; apply GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric <;> assumption)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagVertSymmIndep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem le_of_mem_ratCyc_support {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)}
    (hW : W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support) : P ≤ W := by
  have key : ∀ s, ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0 → P ≤ W := by
    intro s hs
    by_contra hPW
    apply hs
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    rw [if_neg]
    rintro ⟨hmin, -⟩
    exact hPW (le_trans le_sup_left hmin.1.2)
  rw [Finsupp.mem_support_iff] at hW
  simp only [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0
  · by_cases hg : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W = 0
    · simp [hf, hg] at hW
    · exact key g hg
  · exact key f hf

theorem FullFlagVerticalSymmetric.proof (hFib : VerticalDivisorFibreVariety.Statement)
    (hRes : FullFlagRestriction.Statement)
    (hSeg : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
      (ι : K → Type) [∀ k, Fintype (ι k)], IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι) :
    FullFlagVerticalSymmetric.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B hM fl₁ fl₂ I hI G hG n Y R b f g hD
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  congr 1
  have hV := hFib O K ι _ d hM b f g hD W hW
  have : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).IsPrime := hV.1.1
  obtain ⟨hmc, B', -, hfl⟩ := hRes O Ω K ι x d N V B hM (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) hV.1
    (Ideal.map_mono (le_of_mem_ratCyc_support hW))
  obtain ⟨fl₁', h₁, -⟩ := hfl fl₁
  obtain ⟨fl₂', h₂, -⟩ := hfl fl₂
  have hV' : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W))) d := by
    rw [hmc]
    exact hV
  have := SegreFlagIndep.segreFlagIndep_homogeneous_implies_general _ _ ι (hSeg (IsLocalRing.ResidueField O) _ K ι)
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W)) d hV' N _ B' fl₁' fl₂' I hI G hG n Y R
  rw [hmc, h₁, h₂] at this
  exact this

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivFibreVariety

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorFibreVariety.proof : VerticalDivisorFibreVariety.Statement := by
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  exact VerticalDivisorSupportFibre.proof O K ι P d hP b f g hV W (Finsupp.mem_support_iff.mp hW)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatement

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem polyNum_eq_sum {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (V : Ideal (MRing ι F)) (e : ℕ)
    (hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V e) {N : ℕ} (d : Fin N → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (c n : ℕ) (Y : Fin n → K → ℤ) (hG : G.IsHomogeneous c)
    (hcn : c + n = e) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I V e (Fin.append d Y)
                              (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
      ∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList d μ ++ List.ofFn Y) := by
  rw [SegreFlagIndep.prod_X_natAdd, SegreFlagIndep.polyNum_mul_monomial, SegreFlagIndep.monoList_ones]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  have hdeg : α.degree = c := by
    have := hG (mem_support_iff.mp hα)
    rwa [Finsupp.degree_eq_weight_one]
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList d α ++ List.ofFn Y).length = e := by
    rw [List.length_append, SegreFlagIndep.length_monoList, hdeg, List.length_ofFn, hcn]
  rw [SegreFlagIndep.listNum, dite_eq_left hlen,
    Numbers.agree FieldNumbers.IntNumUnique.full (IntNumPoint.proof FieldNumbers.IntNumBase.full)
      FieldNumbers.IntNumBase.full I hI V e _ hV,
    BundleExamples.intNum_get_cast F V _ e hlen]
  refine FlagTypings.intNumL_perm F V (List.Perm.append_right _ ?_)
  rw [BundleExamples.monoList_eq]
  exact FlagTypings.monoList_perm d α

theorem segreFlagIndep (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι := by
  classical
  intro x e hV N E _ _ B fl₁ fl₂ I hI G hG c n Y hGc hcn
  obtain ⟨w, hw⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₁
  obtain ⟨v, hv⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₂
  rw [polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn, polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn]
  have hI' := VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι (pointIdeal F x)
  have hP : IsMultiProjPrime (pointIdeal F x) := ⟨hV.1.1, hI'.1 hV.1.2.1, hV.1.2.2⟩
  exact GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric F Ω K ι x e hP hV.2 N E B w v _ _ hw hv c G hG hGc (List.ofFn Y)
    (by rw [List.length_ofFn]; omega)

end GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem flag_further_term_independent :
    GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagVerticalSymmetric.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagRestriction.proof
      FurtherIndep.segreFlagIndep)

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatementStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flag_further_term_independent_statement : GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | exact GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent <;> assumption)
end
end
