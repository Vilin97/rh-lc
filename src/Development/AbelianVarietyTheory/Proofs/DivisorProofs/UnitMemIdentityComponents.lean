module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupSchemeStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IdentityComponentOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Published

def IdentityComponentOpen : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧
      ∀ x : G.left, x ∈ Set.range j.left ↔
        x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

end GlobalTheory.Published
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenSubgroup

theorem exists_open_subgroup : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  intro S G _ Z hZ h1 hmul hinv
  let U : G.left.Opens := ⟨Z, hZ⟩
  let G₀ : Over S := Over.mk (U.ι ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk U.ι rfl
  have hjo : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range j.left = Z := U.range_ι
  have : Mono j := Over.mono_of_mono_left j
  have lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ := by
    intro X φ hsub
    have hsub' : Set.range φ.left ⊆ Set.range j.left := hr ▸ hsub
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩
    · rw [← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')
  have inZ : ∀ x : G₀.left, j.left x ∈ Z := fun x => hr ▸ Set.mem_range_self x
  obtain ⟨e, he⟩ := lift (𝟙_ _) η[G] (by
    rintro _ ⟨s, rfl⟩
    exact h1 s)
  obtain ⟨m, hm⟩ := lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    apply hmul
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _)
  obtain ⟨i, hi⟩ := lift G₀ (j ≫ ι[G]) (by
    rintro _ ⟨x, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinv _ (inZ x))
  obtain ⟨Gs, hG⟩ := exists_grpObj_of_mono_of_fac j e m i he hm hi
  exact ⟨G₀, Gs, j, hG, hjo, hr⟩

end GlobalTheory.OpenSubgroup
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStableStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  first | exact @GlobalTheory.OpenSubgroup.exists_open_subgroup | exact GlobalTheory.OpenSubgroup.exists_open_subgroup | (intros; apply GlobalTheory.OpenSubgroup.exists_open_subgroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
end
end
