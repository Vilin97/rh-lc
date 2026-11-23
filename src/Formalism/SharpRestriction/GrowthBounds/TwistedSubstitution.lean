module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aMonomial
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TheoremIIClosedOfTestBound
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TransStep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.SharpRestriction.GrowthBounds.Joints
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
public import Formalism.SharpRestriction.GrowthBounds.PathWeight
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ScaleZeroIff
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LogSizeBoundLe
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosDef
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestXiPOfNS

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.PrimStep

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem rest6a (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  source_integrality_of_substitution transStep substPol 1 one_pos (fun C _ => spStep C) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Closed

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem cleaning_of_admitted : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    SourceCleaning.aux₃ D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := Formalism.MainNotions.G.symbolGeneratorData.classMap_estimate_of_admissible
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩ := hA
  exact ⟨WittFrameLocaliserOrders.theta_kernel_expansion D, WittFrameLocaliserOrders.splitting_package_holds D, WittFrameLocaliserOrders.segment_statement_holds D, WittFrameLocaliserOrders.order_lemma_holds D,
    WittFrameLocaliserOrders.divisibility_of_field_lemma D h21, H D h15 h16 h17 h18 h20 h21⟩

theorem plane_gram_lemmas_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : PlaneGramData.admitted D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, h12, _, h14, h15, _, _, _, _, _, _, _, h23, h24, _⟩ := hA
  have hV : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D := h12
  have hL52 : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D := h23
  have hL61 : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D := h24
  exact ⟨Joints.isotypic_multiplicity_of_reducibility_alt D hV (GLWeightTheory.weight_condition_from_integral_form D),
    ⟨Joints.valuation_clauses_of_lattice_index D hL61.1, Joints.twisted_valuation_second_sentence D⟩,
    ⟨Joints.isotypic_coefficient_of_degree_bound D h14, Joints.third_degree_bound_gives_span_clause D h15, Joints.span_column_clauses D⟩,
    Joints.projection_of_integral_corollary D h11 hV.2 (GLWeightTheory.weight_condition_from_integral_form D), Joints.digit_identity_of_decomposition D hL52.1,
    Joints.derivation_of_lattice_index D hL61.2.1⟩

theorem plane_gram_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) {CH : ℝ} (hCH : 26 ≤ CH) :
    PlaneGramData.aux₃ D CH 2 24 60 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := plane_gram_lemmas_of_admitted D CLa Ck Crk Cdeg hA
  intro p O _ _ _ _ hSet
  exact Formalism.MainNotions.PlaneGram.stmt D hCH p O hSet
    ⟨a1 p O hSet, ⟨a2.1 p O hSet, a2.2 p O hSet⟩, ⟨a3.1 p O hSet, a3.2.1 p O hSet, a3.2.2 p O hSet⟩, a4 p O hSet,
      a5 p O hSet, a6 p O hSet⟩

theorem theorem_II_closed_of_test_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    RemainingInputsAfter D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 → tableLineDegreeFive.ConclusionE D := by
  obtain ⟨C, hC, H⟩ := cleaning_of_admitted
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA h6b => ?_⟩
  exact theorem_II_of_split_cloud_bounds D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 hA (H D CLa Ck Crk Cdeg hA)
    (plane_gram_of_admitted D CLa Ck Crk Cdeg hA le_rfl) (rest6a D CLa Ck Crk Cdeg) h6b

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem stmtE_of_OpNS (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg : ℝ, RestTSOp D CLa Ck Crk Cdeg ∧ RestNS D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D := by
  obtain ⟨C, _, H⟩ := theorem_II_closed_of_test_bound
  intro CLa Ck Crk Cdeg hA
  exact H D CLa Ck Crk Cdeg hA
    (test_bound_of_two_halves D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60
      (restCloudB_of_op D CLa Ck Crk Cdeg (h CLa Ck Crk Cdeg).1)
      (restFlat_of_Xi D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60
        (restXi_of_NS D CLa Ck Crk Cdeg 26 2 24 60 (h CLa Ck Crk Cdeg).2)))

theorem stmtE_of_TenNS (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg : ℝ, RestNS D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_OpNS D fun CLa Ck Crk Cdeg => ⟨restTSOp_of_ten hT D CLa Ck Crk Cdeg, h CLa Ck Crk Cdeg⟩

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.TestSideCounting

theorem stmtE_of_TenMP (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenNS hT D fun CLa Ck Crk Cdeg => restNS_of D CLa Ck Crk Cdeg 26 2 24 60 (hM _ _ _ _) (hP _ _ _ _)

theorem stmtE_of_MP (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenMP tensor_operators_holds D hM hP

end Formalism.MainNotions.TestSideWords
end
end
end
