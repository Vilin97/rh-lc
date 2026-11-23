module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPoint
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLast
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtin
import Mathlib.Analysis.Normed.Algebra.GelfandRadius

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPointStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.commutingEndomorphismCondition_of_serLoc : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  first | exact @_root_.GlobalTheory.PassOp.main_alt_alt | exact _root_.GlobalTheory.PassOp.main_alt_alt | (intros; apply _root_.GlobalTheory.PassOp.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLastStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.exists_bound_tieChi_of_prints : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) (8 * (CT : ℝ)) CT := by
  first | exact @_root_.GlobalTheory.NormFromFacts.main_alt_alt | exact _root_.GlobalTheory.NormFromFacts.main_alt_alt | (intros; apply _root_.GlobalTheory.NormFromFacts.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtinStatement

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := by
  first | exact @_root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | exact _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | (intros; apply _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraAlt

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.ExtraFromFacts
theorem main_alt_alt : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.GlobalTheory.NLink.ExtraAlt D C CT := by
  intro hP
  obtain ⟨CT, hCT⟩ := _root_.GlobalTheory.T.exists_bound_tieChi_of_prints hP
  refine ⟨8 * (CT : ℝ), CT, by positivity, ?_⟩
  intro D nch hf h
  refine ⟨?_, hCT D nch hf h⟩
  obtain ⟨hchi, ⟨Q, hDZ, hE⟩, hine, hser⟩ := h
  have hS := _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity hP.artin
  exact _root_.GlobalTheory.T.commutingEndomorphismCondition_of_serLoc D Q hE (hS.2.1 hS.1 D Q) hser hf.Conclusion1.1 hf.what₂.a.tieLab
    hf.adm.1.1.1 hf.adm.1.1.2.2.1 hf.adm.1.1.2.2.2.2.2.2
end GlobalTheory.ExtraFromFacts
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtraBoundOfTwistingEigenFacts

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.exists_const_tieChi_bound_of_facts : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.GlobalTheory.NLink.ExtraAlt D C CT := by
  first | exact @_root_.GlobalTheory.ExtraFromFacts.main_alt_alt | exact _root_.GlobalTheory.ExtraFromFacts.main_alt_alt | (intros; apply _root_.GlobalTheory.ExtraFromFacts.main_alt_alt <;> assumption)
end
end
end
