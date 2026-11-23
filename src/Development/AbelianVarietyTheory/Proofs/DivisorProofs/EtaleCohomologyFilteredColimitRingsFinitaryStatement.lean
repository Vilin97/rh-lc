module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolutionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlatStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (exact GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (intros; apply GlobalTheory.EtC.hyp_spec_coAug_of_etFF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocyclesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  first | exact @GlobalTheory.EtC.HCZero.main | exact GlobalTheory.EtC.HCZero.main | (intros; apply GlobalTheory.EtC.HCZero.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimit

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimitStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.RingCont.main
  | exact GlobalTheory.EtC.RingCont.main
  | (intros; apply GlobalTheory.EtC.RingCont.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.RingContH

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨_, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit R F hF J D c hc n
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj (sp c.pt) n x
    obtain ⟨j, w, y, hw, hwy⟩ := h1 z hz
    refine ⟨j, cl _ n w hw, ?_⟩
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, heq]
    exact ⟨y, hwy⟩
  · obtain ⟨w, hw, rfl⟩ := hsurj (sp (D.obj j)) n y
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, hzero] at hy
    obtain ⟨k, f, y', hy'⟩ := h2 j w hw hy
    refine ⟨k, f, ?_⟩
    obtain ⟨h', hh'⟩ := hpull (sp (D.obj k)) (sp (D.obj j)) (spMap (D.map f).hom) n w hw
    rw [hh', hzero]
    exact ⟨y', hy'⟩

end GlobalTheory.EtC.RingContH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.RingContH.main
  | exact GlobalTheory.EtC.RingContH.main
  | (intros; apply GlobalTheory.EtC.RingContH.main <;> assumption)
end
end
