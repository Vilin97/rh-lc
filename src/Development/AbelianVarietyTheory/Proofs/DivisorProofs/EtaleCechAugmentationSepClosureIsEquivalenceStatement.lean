module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwiseStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCocone

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem ringCocone_isColimit (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    Nonempty (IsColimit (ringCocone K Ω)) := by
  haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change Ω at x
    have hx : _root_.IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩,
      homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.SepCech
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCoconeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isColimit_finiteSubextensionRingCocone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω], Nonempty (CategoryTheory.Limits.IsColimit (GlobalTheory.SepCech.ringCocone K Ω)) := by
  first | (exact @GlobalTheory.SepCech.ringCocone_isColimit) | (exact GlobalTheory.SepCech.ringCocone_isColimit) | (intros; apply GlobalTheory.SepCech.ringCocone_isColimit  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowConeStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  first | exact @GlobalTheory.SepCech.isLimit_leftFunc_arrCone | exact GlobalTheory.SepCech.isLimit_leftFunc_arrCone | (intros; apply GlobalTheory.SepCech.isLimit_leftFunc_arrCone <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparableStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  first | exact @GlobalTheory.spec_map_smooth_surjective_of_isSeparable | exact GlobalTheory.spec_map_smooth_surjective_of_isSeparable | (intros; apply GlobalTheory.spec_map_smooth_surjective_of_isSeparable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalence

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem aug_comm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (g : Y' ⟶ X) (u : yoneda.obj Y ⟶ yoneda.obj Y')
    (w : u ≫ yoneda.map g = yoneda.map f ≫ 𝟙 _) :
    SimplicialObject.cechNerve.map (Arrow.homMk u (𝟙 _) w : Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map g)) ≫ cechAug g =
      cechAug f := by
  apply NatTrans.ext; funext n
  simp [cechAug, SimplicialObject.cechNerve, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  erw [NatTrans.comp_app, WidePullback.lift_base]

theorem cont (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : ContCone R F (cechCone K Ω) := by
  obtain ⟨hc⟩ := GlobalTheory.T.isColimit_finiteSubextensionRingCocone K Ω
  obtain ⟨hl⟩ := GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone K Ω hc
  refine GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F _ _ _ (fun k => ?_)
  obtain ⟨hk⟩ := GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit _ _ _ hl (fun _ _ _ => show IsIso (𝟙 _) from inferInstance)
    (fun _ => show IsIso (𝟙 _) from inferInstance) k
  refine GlobalTheory.T.continuity_cofiltered_limit_represented_affine R F hF _ _ _ hk (fun L => ?_) ?_
  · obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) inferInstance k
    haveI := hπ
    exact ⟨Z, isAffine_of_isAffineHom π, ⟨e⟩⟩
  · obtain ⟨Z, π, e, -, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) inferInstance k
    exact ⟨Z, ⟨e⟩⟩

theorem cechAug_sepClosure_eqv : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω], Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  intro R _ F hF K Ω _ _ _ _
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hc := cont R F hF K Ω
  have hA : ∀ L : (FinSub K Ω)ᵒᵖ, Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1)))) F := by
    intro L
    haveI := L.unop.2
    haveI : Algebra.IsSeparable K L.unop.1 := Algebra.isSeparable_tower_bot_of_isSeparable K L.unop.1 Ω
    obtain ⟨h1, h2⟩ := GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable K L.unop.1
    exact GlobalTheory.T.etC_a2 R _ F
  have hw : ∀ L : (FinSub K Ω)ᵒᵖ, (cechCone K Ω).π.app L ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) =
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := fun L => aug_comm _ _ _ _
  have hw2 : ∀ ⦃L L' : (FinSub K Ω)ᵒᵖ⦄ (f : L ⟶ L'), (arr K Ω ⋙ SimplicialObject.cechNerve).map f ≫
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L'.unop.1))) =
      cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) := fun L L' f => aug_comm _ _ _ _
  intro n
  constructor
  · refine (injective_iff_map_eq_zero (pull R _ F n)).mpr (fun z hz => ?_)
    let L0 : (FinSub K Ω)ᵒᵖ := op ⟨⊥, inferInstance⟩
    have h0 : pull R ((cechCone K Ω).π.app L0) F n
        (pull R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z) = 0 :=
      (pull_comp R _ _ F n z).symm.trans ((congrArg (fun g => pull R g F n z) (hw L0)).trans hz)
    obtain ⟨L1, f, hf⟩ := (hc n).2 L0 _ h0
    have hf' : pull R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L1.unop.1)))) F n z = 0 :=
      (congrArg (fun g => pull R g F n z) (hw2 f)).symm.trans
        ((pull_comp R ((arr K Ω ⋙ SimplicialObject.cechNerve).map f)
          (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z).trans hf)
    exact ((injective_iff_map_eq_zero (pull R _ F n)).mp (hA L1 n).1) z hf'
  · intro x
    obtain ⟨L, y, hy⟩ := (hc n).1 x
    obtain ⟨z, rfl⟩ := (hA L n).2 y
    refine ⟨z, ?_⟩
    rw [← hy]
    exact (congrArg (fun g => pull R g F n z) (hw L)).symm.trans (pull_comp R _ _ F n z)

end GlobalTheory.SepCech
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalenceStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCechAugmentation_sepClosure_isEquivalence : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], Eqv R (cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  first
  | exact @GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | exact GlobalTheory.SepCech.cechAug_sepClosure_eqv
  | (intros; apply GlobalTheory.SepCech.cechAug_sepClosure_eqv <;> assumption)
end
end
