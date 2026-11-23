module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniformStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImage

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_embedding_fixedField_of_le_complexImage : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  intro s M hle
  let e := IntermediateField.equivMap s.B.LL0 s.B.embLL.toRatAlgHom
  refine ⟨(e.symm.toAlgHom.toRingHom).comp (IntermediateField.inclusion hle).toRingHom, ?_⟩
  ext x
  show s.B.embLL ((e.symm ⟨x.1, hle x.2⟩ : s.B.LL0) : _) = x.1
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x.1, hle x.2⟩)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImageStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField : ∀ (s : Stages) (M : IntermediateField ℚ ℂ), M ≤ s.B.fixedCoefficientFieldInComplex → ∃ j : M →+* s.toD7.LL0, (embLL0 s.toD7).comp j = M.val.toRingHom := by
  first | exact @GlobalTheory.exists_embedding_fixedField_of_le_complexImage | exact GlobalTheory.exists_embedding_fixedField_of_le_complexImage | (intros; apply GlobalTheory.exists_embedding_fixedField_of_le_complexImage <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerate

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.finDimSubfield_finGen : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  intro M hM
  classical
  let b := Module.finBasis ℚ M
  refine ⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have : IsIntegral ℚ (b i) := Algebra.IsIntegral.isIntegral _
    exact (this.map M.val).isAlgebraic
  · intro Lf hS x hx
    have hb : ∀ i, ((b i : M) : ℂ) ∈ Lf := fun i =>
      hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have : x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ) := by rw [← hx']
    rw [this, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_smul]
    exact Lf.sum_mem fun i _ => Lf.smul_mem (hb i)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  first | exact @GlobalTheory.finDimSubfield_finGen | exact GlobalTheory.finDimSubfield_finGen | (intros; apply GlobalTheory.finDimSubfield_finGen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.PositiveBaseCharge

theorem q0_pos_allSt : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) :=
  StepW.of_all fun _ _ _ _ _ _ _ _ _ x => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (Dof x)).1.pos

end GlobalTheory.HeightCounting.Up.PositiveBaseCharge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | exact GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | (intros; apply GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.Up

theorem nonempty_gridData_allSt : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  intro cDep
  unfold AllSt StepW Step
  refine EvG.imp GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices fun K _ _ _ _ H => large₂.mono (fun B f T _ h hk _ _ w _ P x => ?_) H
  obtain ⟨-, -, -, -, -, -, w0, hP⟩ := h hk T w x.o.Z
  refine GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w x.o.Z x.m.z ⟨1, cDep, K.s.b⟩ fun k e => ?_
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases k
  · exact hd.1 (Or.inr (Or.inr (Or.inr e.symm)))
  · exact hd.2.1 (Or.inr (Or.inr e.symm))

end GlobalTheory.HeightCounting.Up
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  first | exact @GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | exact GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt | (intros; apply GlobalTheory.HeightCounting.Up.nonempty_gridData_allSt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValues

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep) GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using GlobalTheory.T.exists_numberField_gridCharacters_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValuesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_grid_unit_gap_field_contains_values : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  first | exact @GlobalTheory.HeightCounting.Up.exists_grid_fieldHas | exact GlobalTheory.HeightCounting.Up.exists_grid_fieldHas | (intros; apply GlobalTheory.HeightCounting.Up.exists_grid_fieldHas <;> assumption)
end
end
