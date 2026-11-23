module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SaturatedLowerSetSpanOfLowerSetTypesSpan
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleWordBasis
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnCongruence
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnMultidegree
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.WedgeSplitTan
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColOKOfPath
public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weight_projector_mem_weight_space {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (htop : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (mu : Fin n → ℤ) (e : Module.End K V) (he : IsWtProj E mu e)
    (x : V) : e x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [htop]; trivial
  refine Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro nu y hy
    by_cases h : nu = mu
    · subst h
      rw [he.1 y hy]
      exact hy
    · rw [he.2 nu h y hy]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

theorem adm_eleven (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj

  have hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact hlat.1 u hu
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, y, hy, -, rfl⟩
    exact hstab u hu y hy
  · intro y hy u hu e he
    exact ⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleLowerSetSpan

section

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_lowerSet_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.SaturatedLowerSetSpan D := saturatedLowerSetSpan_of_lowerSetTypesSpan D (lower_set_types_span D)

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem canonical_translate_jet_identity (D : Formalism.BasicNotions.D7) : CanonicalTranslateJetIdentity D := by
  intro p f _ O _ _ _ _ S hp5 hf hsq N r K _ _ _ LL B z hK hmono hz P g hg c hpos J
  have H : ColOK LL P.mu c := colOK_of_path LL B hK P c
  refine ⟨column_kernel_components_integral p f LL g hg z P.mu c J, fun m hm i hi => lifted_column_multidegree p f LL g z P.mu c hmono hz J m hm i hi,
    fun g' hg' => lifted_column_order p f (frobCong p f hf) S hsq LL g g' hg hg' z P.mu c H hmono hz hpos J, ?_,
    column_order_le_two_power p (by omega) LL.pos z hmono hz P.mu c hpos⟩
  exact lifted_column_congruence p f S LL g hg z P.mu c hmono hz hpos (SgVanish_of LL P.mu c H)
    (fun J => plTanCol_eq_SgW O LL P.mu c H P.dom J) J

end Formalism.MainNotions.LemmaBAlt
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

end Formalism.MainNotions.LemmaBAlt
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds

section

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.G.GLWeightTheory

theorem splitting_third_part_holds (D : Formalism.BasicNotions.D7) : DefiniteRankOne D := by
  intro p _ O _ _ _ _ N n _ LL B th M
  exact ⟨lemma_A3_over_domain LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) O th M,
    lemma_A3_over_field LL B D word_valuation_bounds (valuation_field D).1 (admissible_standardPath_basis D) (admissible_word_basis D) (Formalism.MainNotions.G.FF O) th M⟩

theorem splitting_package_holds (D : Formalism.BasicNotions.D7) : Conclusion2 D :=
  ⟨automorphicSideConclusion_of_pathBasis D (admissible_standardPath_basis D), splitting_third_part_holds D, prvB1_of_D7 D, lemma_B2 D,
    nested_sets_lemma_of_admitted D (adm_fourteen D) (admissible_externalProduct D), coefficientDependence D, canonical_translate_jet_identity D⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities

section

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies.Top
end
end
