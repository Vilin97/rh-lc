module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.Algebra.CharP.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamilyStatement
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPointStatement
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.charZero_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ hY hK
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom)
      (Y.germToFunctionField_injective ⊤)
  exact (π.stalkMap (genericPoint Y)).hom.charZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldStalkImageGenericPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    letI := GlobalTheory.NormSheafDescent.algKL π;
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  let := GlobalTheory.NormSheafDescent.fieldK π hK
  let := GlobalTheory.NormSheafDescent.algKL π
  let K := Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)
  have hFinite : FiniteDimensional K Y.functionField := by
    obtain ⟨U, hU, hζU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := Z) (U := ⊤) (x := GlobalTheory.NormSheafDescent.genPt π) trivial
    have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
    have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
    let f : Γ(Z, U) →+* K :=
      (Z.presheaf.germ U (GlobalTheory.NormSheafDescent.genPt π) hζU).hom
    let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField := (Y.germToFunctionField (π ⁻¹ᵁ U)).hom
    let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
    have hsq : ∀ a, algebraMap K Y.functionField (f a) = φ (g a) :=
      fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
    let : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
    have : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := π.finite_app U hU
    have : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ hV
    have hint (b : Γ(Y, π ⁻¹ᵁ U)) : IsIntegral K (φ b) := by
      obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
      refine ⟨p.map f, hp.map f, ?_⟩
      have e : (algebraMap K Y.functionField).comp f = φ.comp g := RingHom.ext hsq
      have hpb' : p.eval₂ g b = 0 := hpb
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
    have : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
    let E := IntermediateField.adjoin K (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))
    have hE : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
    have hmem (b : Γ(Y, π ⁻¹ᵁ U)) : φ b ∈ E := by
      have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) :=
        hs ▸ Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have e : φ (a • x) = algebraMap K Y.functionField (f a) * φ x := by
          rw [hsq, Algebra.smul_def, map_mul]
          rfl
        rw [e]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    have htop : E = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
      exact div_mem (hmem b) (hmem c)
    have : FiniteDimensional K (⊤ : IntermediateField K Y.functionField) := htop ▸ hE
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  exact hFinite
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

theorem isField_stalk_genPt :
    ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ _ hW
  haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)
  refine isField_stalk_of_forall_specializes _ fun z hz => ?_
  obtain ⟨y, rfl⟩ : z ∈ Set.range π := hz.mem_open hW ⟨_, rfl⟩
  exact (hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq

end GlobalTheory.NormSheafDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.isField_stalk_genPt | exact GlobalTheory.NormSheafDescent.isField_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.isField_stalk_genPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.normCoeffIdealFamily_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | exact GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := GlobalTheory.T.isField_stalk_imageOfGenericPoint Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := GlobalTheory.T.exists_idealSheafData_of_isClopen_family Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  first | exact @GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | exact GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | (intros; apply GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists <;> assumption)
end
end
