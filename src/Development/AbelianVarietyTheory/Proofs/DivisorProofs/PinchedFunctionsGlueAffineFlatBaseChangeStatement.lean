module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushout

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.FlatFibreProduct

open TensorProduct

theorem injective_exact_of_isBaseChange {R R' M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R N₁] [Module R N₂] [Module R N₃]
    [Module R' N₁] [Module R' N₂] [Module R' N₃]
    [IsScalarTower R R' N₁] [IsScalarTower R R' N₂] [IsScalarTower R R' N₃]
    {ι₁ : M₁ →ₗ[R] N₁} {ι₂ : M₂ →ₗ[R] N₂} {ι₃ : M₃ →ₗ[R] N₃}
    (h₁ : IsBaseChange R' ι₁) (h₂ : IsBaseChange R' ι₂) (h₃ : IsBaseChange R' ι₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R'] N₂) (g' : N₂ →ₗ[R'] N₃)
    (hf : ∀ m, f' (ι₁ m) = ι₂ (f m)) (hg : ∀ m, g' (ι₂ m) = ι₃ (g m))
    (hinj : Function.Injective f) (hex : Function.Exact f g) :
    Function.Injective f' ∧ Function.Exact f' g' := by
  have k₁ : ∀ x, h₂.equiv (f.lTensor R' x) = f' (h₁.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hf]
    | add x y hx hy => simp_all
  have k₂ : ∀ x, h₃.equiv (g.lTensor R' x) = g' (h₂.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hg]
    | add x y hx hy => simp_all
  have inj := Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hinj
  have ex := Module.Flat.lTensor_exact R' hex
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · apply h₁.equiv.symm.injective
    apply inj
    apply h₂.equiv.injective
    rw [k₁, k₁]
    simpa using hab
  · obtain ⟨x, rfl⟩ := h₂.equiv.surjective y
    rw [← k₂, LinearEquiv.map_eq_zero_iff, ex x]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨h₁.equiv z, (k₁ z).symm⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := h₁.equiv.surjective z
      refine ⟨w, h₂.equiv.injective ?_⟩
      rw [k₁, hz]

theorem exists_unique_of_flat_of_isPushout : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  intro A B C D A' B' C' D' fB fC u v e eB eC eD aB aC u' v' hfl hB hC hD h1 h2 h3 h4 hfib
  letI : Algebra A A' := e.hom.toAlgebra
  letI : Algebra A B := fB.hom.toAlgebra
  letI : Algebra A C := fC.hom.toAlgebra
  letI : Algebra A D := (fB ≫ u).hom.toAlgebra
  letI : Algebra A' B' := aB.hom.toAlgebra
  letI : Algebra A' C' := aC.hom.toAlgebra
  letI : Algebra A' D' := (aB ≫ u').hom.toAlgebra
  letI : Algebra B B' := eB.hom.toAlgebra
  letI : Algebra C C' := eC.hom.toAlgebra
  letI : Algebra D D' := eD.hom.toAlgebra
  letI : Algebra A B' := (e ≫ aB).hom.toAlgebra
  letI : Algebra A C' := (e ≫ aC).hom.toAlgebra
  letI : Algebra A D' := (e ≫ aB ≫ u').hom.toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' D' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hB.w)
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hC.w)
  haveI : IsScalarTower A D D' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hD.w)
  haveI : Module.Flat A A' := hfl
  have PB : Algebra.IsPushout A A' B B' := CommRingCat.isPushout_iff_isPushout.mp hB
  have PC : Algebra.IsPushout A A' C C' := CommRingCat.isPushout_iff_isPushout.mp hC
  have PD : Algebra.IsPushout A A' D D' := CommRingCat.isPushout_iff_isPushout.mp hD
  have hb₁ : IsBaseChange A' (Algebra.linearMap A A') := IsBaseChange.linearMap A A'
  have hb₂ := IsBaseChange.prodMap _ _ PB.out PC.out
  have hb₃ := PD.out
  let uL : B →ₗ[A] D :=
    { toFun := u.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u.hom (fB.hom a * b) = (fB ≫ u).hom a * u.hom b
        rw [map_mul]; rfl }
  let vL : C →ₗ[A] D :=
    { toFun := v.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v.hom (fC.hom a * c) = (fB ≫ u).hom a * v.hom c
        rw [map_mul, h4]; rfl }
  let u'L : B' →ₗ[A'] D' :=
    { toFun := u'.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u'.hom (aB.hom a * b) = (aB ≫ u').hom a * u'.hom b
        rw [map_mul]; rfl }
  let v'L : C' →ₗ[A'] D' :=
    { toFun := v'.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v'.hom (aC.hom a * c) = (aB ≫ u').hom a * v'.hom c
        rw [map_mul, h3]; rfl }
  let f : A →ₗ[A] B × C := (Algebra.linearMap A B).prod (Algebra.linearMap A C)
  let g : B × C →ₗ[A] D := uL.coprod (-vL)
  let f' : A' →ₗ[A'] B' × C' := (Algebra.linearMap A' B').prod (Algebra.linearMap A' C')
  let g' : B' × C' →ₗ[A'] D' := u'L.coprod (-v'L)
  have hf : ∀ m, f' (Algebra.linearMap A A' m) =
      ((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) (f m) := by
    intro m
    refine Prod.ext ?_ ?_
    · exact congrArg (fun φ => φ.hom m) hB.w
    · exact congrArg (fun φ => φ.hom m) hC.w
  have hg : ∀ m, g' (((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) m) =
      (IsScalarTower.toAlgHom A D D').toLinearMap (g m) := by
    rintro ⟨b, c⟩
    change u'.hom (eB.hom b) + -v'.hom (eC.hom c) = eD.hom (u.hom b + -v.hom c)
    have e₁ : u'.hom (eB.hom b) = eD.hom (u.hom b) := congrArg (fun φ => φ.hom b) h1
    have e₂ : v'.hom (eC.hom c) = eD.hom (v.hom c) := congrArg (fun φ => φ.hom c) h2
    rw [map_add (f := _), map_neg, e₁, e₂]
  have hinj : Function.Injective f := by
    intro a₁ a₂ h
    have hb : fB.hom a₁ = fB.hom a₂ := congrArg Prod.fst h
    have hc : fC.hom a₁ = fC.hom a₂ := congrArg Prod.snd h
    obtain ⟨a, -, ha⟩ := hfib (fB.hom a₁) (fC.hom a₁)
      (by simpa using congrArg (fun φ => φ.hom a₁) h4)
    exact (ha a₁ ⟨rfl, rfl⟩).trans (ha a₂ ⟨hb.symm, hc.symm⟩).symm
  have hex : Function.Exact f g := by
    rintro ⟨b, c⟩
    change u.hom b + -v.hom c = 0 ↔ _
    rw [← sub_eq_add_neg, sub_eq_zero]
    constructor
    · intro h
      obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := hfib b c h
      exact ⟨a, Prod.ext ha₁ ha₂⟩
    · rintro ⟨a, ha⟩
      have hb : fB.hom a = b := congrArg Prod.fst ha
      have hc : fC.hom a = c := congrArg Prod.snd ha
      subst hb hc
      simpa using congrArg (fun φ => φ.hom a) h4
  obtain ⟨inj', ex'⟩ := injective_exact_of_isBaseChange hb₁ hb₂ hb₃ f g f' g' hf hg hinj hex
  intro b' c' h
  have h0 : g' (b', c') = 0 := by
    change u'.hom b' + -v'.hom c' = 0
    rw [h, add_neg_cancel]
  obtain ⟨a', ha'⟩ := (ex' (b', c')).1 h0
  refine ⟨a', ⟨congrArg Prod.fst ha', congrArg Prod.snd ha'⟩, fun y hy => inj' ?_⟩
  rw [ha']
  exact Prod.ext hy.1 hy.2

end GlobalTheory.FlatFibreProduct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushoutStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.existsUnique_preimage_pair_of_pushout_of_compat : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  first | exact @GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout | exact GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout | (intros; apply GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift.FlatBC

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S}
    {iY : Y ⟶ T} (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (h₁ : UY ≤ g ⁻¹ᵁ UX) (h₂ : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) (g.appLE UX UY h₁) (iY.appLE UT UY h₂) :=
  (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX)

theorem appLE_congr_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) (V : A.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

end GlobalTheory.PinchLift.FlatBC

namespace GlobalTheory.PinchLift.FlatBC

theorem glues_affine_of_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hglue V W hV hW hWV a b hab
  have hcl : i'.left ≫ p.left = p'.left ≫ i.left := by
    rw [← Over.comp_left, ← Over.comp_left, hc]
  have hcE : (E ◁ i').left ≫ (E ◁ p).left = (E ◁ p').left ≫ (E ◁ i).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hc]
  have nat : ∀ {Y Y' : Over S} (j : Y' ⟶ Y),
      (E ◁ j).left ≫ (snd E Y).left = (snd E Y').left ≫ j.left := by
    intro Y Y' j
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  haveI : IsAffineHom i.left := inferInstance
  haveI : IsClosedImmersion i'.left := MorphismProperty.of_isPullback hpb.flip ‹_›
  haveI : IsAffineHom p'.left := MorphismProperty.of_isPullback hpb ‹_›
  haveI : Flat (snd E X).left := by
    change Flat (pullback.snd E.hom X.hom); infer_instance
  have eV : p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcl]
  have eW : (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) = (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcE]
  have hDV : i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = (i'.left ≫ p.left) ⁻¹ᵁ V := by
    rw [eV, inf_idem]; rfl
  have hDW : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W := by
    rw [eW, inf_idem]; rfl
  have hDVa : IsAffineOpen (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDV]; exact hV.preimage _
  have H1 := isPullback_whiskerLeft_snd_left E p
  have H2 := isPullback_whiskerLeft_snd_left E i
  have H3 : IsPullback ((E ◁ i').left ≫ (E ◁ p).left) (snd E Z').left (snd E X).left
      (i'.left ≫ p.left) := by
    have := isPullback_whiskerLeft_snd_left E (i' ≫ p)
    rwa [MonoidalCategory.whiskerLeft_comp, Over.comp_left, Over.comp_left] at this
  have hU1 : (E ◁ p).left ⁻¹ᵁ W = (E ◁ p).left ⁻¹ᵁ W ⊓ (snd E X').left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat p, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have hU2 : (E ◁ i).left ⁻¹ᵁ W = (E ◁ i).left ⁻¹ᵁ W ⊓ (snd E Z).left ⁻¹ᵁ (i.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat i, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have nat3 : ((E ◁ i').left ≫ (E ◁ p).left) ≫ (snd E X).left =
      (snd E Z').left ≫ (i'.left ≫ p.left) := by
    rw [Category.assoc, nat p, ← Category.assoc, nat i', Category.assoc]
  have hU3 : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W ⊓
        (snd E Z').left ⁻¹ᵁ (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDW, hDV]
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage (snd E Z').left (i'.left ≫ p.left) V, ← nat3,
      Scheme.Hom.comp_preimage _ (snd E X).left V]
    exact Scheme.Hom.preimage_mono _ hWV
  have P1 := isPushout_appLE_of_isPullback H1 hV (hV.preimage p.left) hW le_rfl hWV hU1 le_rfl
    (hU1.le.trans inf_le_right)
  have P2 := isPushout_appLE_of_isPullback H2 hV (hV.preimage i.left) hW le_rfl hWV hU2 le_rfl
    (hU2.le.trans inf_le_right)
  have P3 := isPushout_appLE_of_isPullback H3 hV hDVa hW hDV.le hWV hU3 (hU3.le.trans inf_le_left)
    (hU3.le.trans inf_le_right)
  have key := GlobalTheory.T.existsUnique_preimage_pair_of_pushout_of_compat (p.left.appLE V (p.left ⁻¹ᵁ V) le_rfl) (i.left.appLE V (i.left ⁻¹ᵁ V) le_rfl)
    (i'.left.appLE (p.left ⁻¹ᵁ V) _ inf_le_left) (p'.left.appLE (i.left ⁻¹ᵁ V) _ inf_le_right)
    ((snd E X).left.appLE V W hWV)
    ((snd E X').left.appLE (p.left ⁻¹ᵁ V) ((E ◁ p).left ⁻¹ᵁ W) (hU1.le.trans inf_le_right))
    ((snd E Z).left.appLE (i.left ⁻¹ᵁ V) ((E ◁ i).left ⁻¹ᵁ W) (hU2.le.trans inf_le_right))
    ((snd E Z').left.appLE _ _ (hU3.le.trans inf_le_right))
    ((E ◁ p).left.appLE W _ le_rfl) ((E ◁ i).left.appLE W _ le_rfl)
    ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) _ inf_le_left)
    ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) _ inf_le_right)
    ((snd E X).left.flat_appLE hV hW hWV) P1 P2
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; exact P3)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat i') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat p') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcE _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcl _ _ _ _)
    (fun b c h => by
      have := hglue V b c h
      rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE] at this) a b hab
  rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]

end GlobalTheory.PinchLift.FlatBC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  first | exact @GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | exact GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | (intros; apply GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange <;> assumption)
end
end
