module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteGroupHomKernelPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

theorem isMonHom_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsMonHom i := by
  letI := grpObjOfIsKernel hp
  refine { one_hom := kerLift_comp hp _ _, mul_hom := ?_ }
  refine (kerLift_comp hp _ _).trans ?_
  rw [Hom.mul_def]
  simp

theorem isCommMonObj_of_isKernel [BraidedCategory C] [IsCommMonObj A]
    (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsCommMonObj H := by
  letI := grpObjOfIsKernel hp
  have := mono_of_isKernel hp
  have := isMonHom_of_isKernel hp
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end General

theorem exists_finite_kernel : ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → ∀ (q : A ⟶ A'), IsMonHom q → IsFinite q.left →
    ∃ (H : Over (Sp k)) (_ : GrpObj H) (_ : IsCommMonObj H) (i : H ⟶ A), IsMonHom i ∧ IsFinite H.hom ∧
      IsPullback i (toUnit _) q η[A'] := by
  intro k _ A A' _ _ hA q hq hf
  have := hA.comm
  have hp : IsPullback (pullback.fst q η[A']) (toUnit (pullback q η[A'])) q η[A'] := by
    rw [toUnit_unique (toUnit _) (pullback.snd q η[A'])]
    exact IsPullback.of_hasPullback _ _
  refine ⟨pullback q η[A'], grpObjOfIsKernel hp, isCommMonObj_of_isKernel hp, pullback.fst _ _,
    isMonHom_of_isKernel hp, ?_, hp⟩
  have hl := hp.map (Over.forget _)
  have h1 : IsFinite (toUnit (pullback q η[A'])).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hl hf
  have h2 : (pullback q η[A']).hom = (toUnit (pullback q η[A'])).left ≫ (𝟙_ (Over (Sp k))).hom :=
    (Over.w _).symm
  rw [h2]
  exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
end GlobalTheory.CompanionTheory.KerPull.Kernel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNat

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerKill

theorem flat_of_isFinite_field (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] (hf : IsFinite H.hom) :
    Flat H.hom := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have e : H.hom = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hw, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

theorem kernel_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  intro K _ A B f hf
  let H := pullback f.hom η[B.X]
  let i : H ⟶ A.X := pullback.fst _ _
  have hp : IsPullback i (toUnit H) f.hom η[B.X] := by
    rw [toUnit_unique (toUnit _) (pullback.snd f.hom η[B.X])]
    exact IsPullback.of_hasPullback _ _
  haveI : Mono i := ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩
  let lift {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) : W ⟶ H :=
    GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift hp g hg
  have lift_comp {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) :
      lift g hg ≫ i = g := GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp g hg
  have kills (W : Over (Sp K)) (x : W ⟶ H) : (x ≫ i) ≫ f.hom = 1 := by
    rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]
  letI : GrpObj H :=
    { one := lift η[A.X] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
      mul := lift (fst H H ≫ i * snd H H ≫ i) (by
        rw [MonObj.mul_comp, kills, kills, _root_.mul_one])
      inv := lift (i ≫ ι[A.X]) (by
        have e : i ≫ f.hom = 1 := by simpa using kills H (𝟙 H)
        have h : (i⁻¹ * i) ≫ f.hom = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
        rw [MonObj.mul_comp, e, _root_.mul_one] at h
        exact h)
      one_mul := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (fst (𝟙_ (Over (Sp K))) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (snd H (𝟙_ (Over (Sp K)))) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        exact _root_.mul_assoc _ _ _
      left_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact inv_mul_cancel i
      right_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact mul_inv_cancel i }
  haveI : IsMonHom i := by
    refine { one_hom := lift_comp _ _, mul_hom := ?_ }
    refine (lift_comp _ _).trans ?_
    rw [Hom.mul_def]
    simp
  haveI : IsCommMonObj A.X := A.ab.comm
  haveI : IsCommMonObj H := by
    refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
    rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hHf : IsFinite H.hom := by
    have hl := hp.map (Over.forget _)
    have h1 : IsFinite (toUnit H).left := MorphismProperty.of_isPullback (P := @IsFinite) hl hf
    have h2 : H.hom = (toUnit H).left ≫ (𝟙_ (Over (Sp K))).hom := (Over.w _).symm
    rw [h2]
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
  have hfl : Flat H.hom := flat_of_isFinite_field K H hHf
  obtain ⟨N, hN, h⟩ := GlobalTheory.FiniteFlatKilled.main K H hHf hfl
  refine ⟨N, hN, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : T ⟶ H, y ≫ i = x := ⟨_, GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp x hx⟩
  rw [← MonObj.comp_pow, ← Category.id_comp i,
    ← MonObj.pow_comp, h, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.AV.KerKill
end
end
end
