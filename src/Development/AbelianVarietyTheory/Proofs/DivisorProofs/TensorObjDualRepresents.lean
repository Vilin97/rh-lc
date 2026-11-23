module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDualDim

theorem finrank_dual_eq (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    Module.finrank O (Module.Dual O X) = Module.finrank O X := by
  haveI : Module.FinitePresentation O X := Module.finitePresentation_of_projective O X
  let F := FractionRing O
  let f : X →ₗ[O] F ⊗[O] X := TensorProduct.mk O F X 1
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl
  let g := IsLocalizedModule.map (nonZeroDivisors O) f (Algebra.linearMap O F)
  have h2 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl
  rw [← h1, ← h2, ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    (LinearMap.extendScalarsOfIsLocalizationEquiv (nonZeroDivisors O) F).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem smoothOfRelativeDimension_tensorObj_dual : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  intro S B _ _ O _ _ _ a X _ _ _ _ g hg
  have h := GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor S O (Module.Dual O X) B
    (tensorObj (Module.Dual O X) a) a (tensorAct (Module.Dual O X) a) g
    ⟨GlobalTheory.Serre.isTensor (Module.Dual O X) a⟩ hg
  rwa [finrank_dual_eq] at h

end GlobalTheory.TensorDualDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDualStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (GlobalTheory.Serre.tensorObj (Module.Dual O X) a).hom := by
  first | exact @GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | exact GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | (intros; apply GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorObjDualRepresents

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HomScheme

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem dualTensorHom_lTensor {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (g : N →ₗ[O] N') (z : Module.Dual O X ⊗[O] N) (x : X) :
    dualTensorHom O X N' (g.lTensor _ z) x = g (dualTensorHom O X N z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => simp [dualTensorHom_apply]
  | add z w hz hw => simp [map_add (f := _), hz, hw]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {a : OAct O G} {b : OAct O H}

def homEquiv [Module.Finite O X] [Module.Projective O X] (h : IsTensor H b G a (Module.Dual O X))
    (T : Over S) : Pts b T ≃ₗ[O] (X →ₗ[O] Pts a T) :=
  (h.equiv T).symm.trans (dualTensorHomEquiv O X (Pts a T))

theorem homEquiv_pre [Module.Finite O X] [Module.Projective O X]
    (h : IsTensor H b G a (Module.Dual O X)) {T T' : Over S} (u : T' ⟶ T) (y : Pts b T) (x : X) :
    homEquiv h T' (Pts.pre b u y) x = Pts.pre a u (homEquiv h T y x) := by
  simp only [homEquiv, LinearEquiv.trans_apply]
  rw [h.natural_symm]
  exact dualTensorHom_lTensor _ _ x

theorem tensorObj_dual_represents {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
    {O : Type} [CommRing O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    ∃ u : X → (tensorObj (Module.Dual O X) a ⟶ B),
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) →
          ∃! c : T ⟶ tensorObj (Module.Dual O X) a, ∀ x, c ≫ u x = f x := by
  let M := Module.Dual O X
  let C := tensorObj M a
  let b := tensorAct M a
  let h : IsTensor C b B a M := isTensor M a
  let Φ := homEquiv h
  let u : X → (C ⟶ B) := fun x => (Φ C (Pts.mk b (𝟙 C)) x).hom
  have hnat : ∀ (T : Over S) (c : T ⟶ C) (x : X), (Φ T (Pts.mk b c) x).hom = c ≫ u x := by
    intro T c x
    have := congrArg Pts.hom (homEquiv_pre h c (Pts.mk b (𝟙 C)) x)
    rw [Pts.hom_pre] at this
    rw [← this]
    congr 3
  refine ⟨u, fun x => ?_, fun x y => ?_, fun o x => ?_, fun T f hadd hsmul => ?_⟩
  · refine isMonHom_of_mul_comp _ fun T p q => ?_
    rw [← hnat, ← hnat, ← hnat, Pts.mk_mul, map_add (f := _), LinearMap.add_apply, Pts.hom_add]
  · change (Φ C _ (x + y)).hom = _
    rw [map_add (f := _), Pts.hom_add]
  · change (Φ C _ (o • x)).hom = _
    rw [map_smul, Pts.hom_smul]
  · let F : X →ₗ[O] Pts a T :=
      { toFun := fun x => Pts.mk a (f x)
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun o x => by rw [hsmul]; rfl }
    refine ⟨((Φ T).symm F).hom, fun x => ?_, fun c hc => ?_⟩
    · rw [← hnat, Pts.mk_hom, LinearEquiv.apply_symm_apply]
      rfl
    · have : Φ T (Pts.mk b c) = F := by
        ext1 x
        apply Pts.ext
        rw [hnat, hc]
        rfl
      rw [← this, LinearEquiv.symm_apply_apply]
      rfl

theorem exists_homObj_relDim (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (g : ℕ) (hg : SmoothOfRelativeDimension g B.hom)
    {O : Type} [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    ∃ (C : Over S) (_ : GrpObj C) (u : X → (C ⟶ B)), IsAbelianScheme C ∧
      SmoothOfRelativeDimension (Module.finrank O X * g) C.hom ∧
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) → ∃! c : T ⟶ C, ∀ x, c ≫ u x = f x := by
  haveI := hB.comm
  obtain ⟨u, h1, h2, h3, h4⟩ := tensorObj_dual_represents B a X
  exact ⟨_, inferInstance, u, (isTensor (Module.Dual O X) a).isAbelianScheme hB,
    GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul S B O a X g hg, h1, h2, h3, h4⟩

end GlobalTheory.HomScheme
end
end
end
