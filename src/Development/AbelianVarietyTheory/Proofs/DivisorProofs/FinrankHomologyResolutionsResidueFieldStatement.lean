module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalent

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem resolution_lift_of_exact {O : Type} [CommRing O] {P A B C : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P]
    [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    {u : A →ₗ[O] B} {v : B →ₗ[O] C} (huv : Function.Exact u v) (w : P →ₗ[O] B)
    (hw : v ∘ₗ w = 0) : ∃ l : P →ₗ[O] A, u ∘ₗ l = w := by
  have hr : ∀ x, w x ∈ LinearMap.range u := fun x => by
    rw [← LinearMap.exact_iff.mp huv, LinearMap.mem_ker]
    exact LinearMap.congr_fun hw x
  obtain ⟨l, hl⟩ := Module.projective_lifting_property u.rangeRestrict (w.codRestrict _ hr)
    u.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext x
  have := congrArg Subtype.val (LinearMap.congr_fun hl x)
  simpa using this

theorem resolutions_homotopy_equivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  intro O _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _ G₂ _ _ _ _
    ε d₁ d₂ d₃ ν e₁ e₂ hε hd1 hd2 hd3 hν he1 he2
  obtain ⟨a₀, ha₀⟩ := Module.projective_lifting_property ν ε hν
  obtain ⟨b₀, hb₀⟩ := Module.projective_lifting_property ε ν hε
  have ha₀' : ∀ x, ν (a₀ x) = ε x := fun x => LinearMap.congr_fun ha₀ x
  have hb₀' : ∀ x, ε (b₀ x) = ν x := fun x => LinearMap.congr_fun hb₀ x
  obtain ⟨a₁, ha₁⟩ := resolution_lift_of_exact he1 (a₀ ∘ₗ d₁) (by
    ext x; simp [ha₀', Function.Exact.apply_apply_eq_zero hd1])
  have ha₁' : ∀ x, e₁ (a₁ x) = a₀ (d₁ x) := fun x => LinearMap.congr_fun ha₁ x
  obtain ⟨a₂, ha₂⟩ := resolution_lift_of_exact he2 (a₁ ∘ₗ d₂) (by
    ext x; simp [ha₁', Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨b₁, hb₁⟩ := resolution_lift_of_exact hd1 (b₀ ∘ₗ e₁) (by
    ext x; simp [hb₀', Function.Exact.apply_apply_eq_zero he1])
  have hb₁' : ∀ x, d₁ (b₁ x) = b₀ (e₁ x) := fun x => LinearMap.congr_fun hb₁ x
  obtain ⟨b₂, hb₂⟩ := resolution_lift_of_exact hd2 (b₁ ∘ₗ e₂) (by
    ext x; simp [hb₁', Function.Exact.apply_apply_eq_zero he2])
  obtain ⟨h₀, hh₀⟩ := resolution_lift_of_exact hd1 (LinearMap.id - b₀ ∘ₗ a₀) (by
    ext x; simp [hb₀', ha₀'])
  have hh₀' : ∀ x, d₁ (h₀ x) = x - b₀ (a₀ x) := fun x => by
    simpa using LinearMap.congr_fun hh₀ x
  obtain ⟨h₁, hh₁⟩ := resolution_lift_of_exact hd2 (LinearMap.id - b₁ ∘ₗ a₁ - h₀ ∘ₗ d₁) (by
    ext x; simp [hb₁', ha₁', hh₀'])
  have hh₁' : ∀ x, d₂ (h₁ x) = x - b₁ (a₁ x) - h₀ (d₁ x) := fun x => by
    simpa using LinearMap.congr_fun hh₁ x
  obtain ⟨h₂, hh₂⟩ := resolution_lift_of_exact hd3 (LinearMap.id - b₂ ∘ₗ a₂ - h₁ ∘ₗ d₂) (by
    ext x
    have e1 := LinearMap.congr_fun hb₂ (a₂ x)
    have e2 := LinearMap.congr_fun ha₂ x
    simp only [LinearMap.comp_apply] at e1 e2
    simp [hh₁', e1, e2, Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨k₀, hk₀⟩ := resolution_lift_of_exact he1 (LinearMap.id - a₀ ∘ₗ b₀) (by
    ext x; simp [hb₀', ha₀'])
  have hk₀' : ∀ x, e₁ (k₀ x) = x - a₀ (b₀ x) := fun x => by
    simpa using LinearMap.congr_fun hk₀ x
  obtain ⟨k₁, hk₁⟩ := resolution_lift_of_exact he2 (LinearMap.id - a₁ ∘ₗ b₁ - k₀ ∘ₗ e₁) (by
    ext x; simp [hb₁', ha₁', hk₀'])
  refine ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, ha₁, ha₂, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [hh₁, sub_add_cancel]
  · rw [hh₂, sub_add_cancel]
  · rw [hk₁, sub_add_cancel]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalentStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.partialFreeResolutions_homotopyEquivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  first | exact @GlobalTheory.resolutions_homotopy_equivalent | exact GlobalTheory.resolutions_homotopy_equivalent | (intros; apply GlobalTheory.resolutions_homotopy_equivalent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_add_le_of_image_mem {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (Z R : Submodule K V) (Z' R' : Submodule K W) (hR' : R' ≤ Z')
    (hZ : ∀ x ∈ Z, A x ∈ Z') (hk : ∀ x ∈ Z, A x ∈ R' → x ∈ R) :
    Module.finrank K Z + Module.finrank K R' ≤ Module.finrank K Z' + Module.finrank K R := by
  let g : (Z × R') →ₗ[K] W := LinearMap.coprod (A ∘ₗ Z.subtype) R'.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_prod] at h1
  have h2 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K Z' := by
    apply Submodule.finrank_mono
    rintro _ ⟨⟨x, r⟩, rfl⟩
    simp only [g, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Z'.add_mem (hZ x x.2) (hR' r.2)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K R := by
    let φ : LinearMap.ker g →ₗ[K] R :=
      LinearMap.codRestrict R (Z.subtype ∘ₗ LinearMap.fst K Z R' ∘ₗ (LinearMap.ker g).subtype) (by
        rintro ⟨⟨x, r⟩, hx⟩
        simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
        apply hk x x.2
        have : A x = -(r : W) := eq_neg_of_add_eq_zero_left hx
        rw [this]; exact R'.neg_mem r.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, r⟩, hx⟩ h0
    simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h0
      simpa [φ] using this
    subst hx0
    have hr : r = 0 := by
      apply Subtype.ext
      simpa using hx
    subst hr
    rfl
  omega

theorem finrank_homology_base_change_resolutions : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  intro O _ K _ _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _
    G₂ _ _ _ _ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    GlobalTheory.T.partialFreeResolutions_homotopyEquivalent O N F₀ F₁ F₂ F₃ G₀ G₁ G₂ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  have bc : ∀ {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      {f g : P →ₗ[O] Q}, f = g → ∀ x, f.baseChange K x = g.baseChange K x := by
    intro P Q _ _ _ _ f g h x; rw [h]
  have z12 : ∀ x, d₁.baseChange K (d₂.baseChange K x) = 0 := by
    intro x; have := bc hd₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have ze12 : ∀ x, e₁.baseChange K (e₂.baseChange K x) = 0 := by
    intro x; have := bc he₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have q1 : ∀ x, e₁.baseChange K (a₁.baseChange K x) = a₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c1 x; simpa [LinearMap.baseChange_comp] using this
  have q2 : ∀ x, e₂.baseChange K (a₂.baseChange K x) = a₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c2 x; simpa [LinearMap.baseChange_comp] using this
  have q3 : ∀ x, d₁.baseChange K (b₁.baseChange K x) = b₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c3 x; simpa [LinearMap.baseChange_comp] using this
  have q4 : ∀ x, d₂.baseChange K (b₂.baseChange K x) = b₁.baseChange K (e₂.baseChange K x) := by
    intro x; have := bc c4 x; simpa [LinearMap.baseChange_comp] using this
  have q5 : ∀ x, x - b₁.baseChange K (a₁.baseChange K x) =
      d₂.baseChange K (h₁.baseChange K x) + h₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c5 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q6 : ∀ x, x - b₂.baseChange K (a₂.baseChange K x) =
      d₃.baseChange K (h₂.baseChange K x) + h₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c6 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q7 : ∀ x, x - a₁.baseChange K (b₁.baseChange K x) =
      e₂.baseChange K (k₁.baseChange K x) + k₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c7 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine finrank_add_le_of_image_mem (a₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact ze12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q1, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨b₂.baseChange K y + h₁.baseChange K x, ?_⟩
      have := q5 x
      rw [hx, map_zero, add_zero, ← hy, ← q4] at this
      rw [map_add (f := _), ← this]; abel
  · refine finrank_add_le_of_image_mem (b₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact z12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q3, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨a₂.baseChange K y + k₁.baseChange K x, ?_⟩
      have := q7 x
      rw [hx, map_zero, add_zero, ← hy, ← q2] at this
      rw [map_add (f := _), ← this]; abel
  · have := finrank_add_le_of_image_mem (a₂.baseChange K) (LinearMap.ker (d₂.baseChange K))
      (LinearMap.range (d₃.baseChange K)) ⊤ ⊥ bot_le (fun _ _ => Submodule.mem_top) (by
        intro x hx h0
        rw [LinearMap.mem_ker] at hx
        rw [Submodule.mem_bot] at h0
        refine ⟨h₂.baseChange K x, ?_⟩
        have := q6 x
        rw [hx, h0, map_zero, map_zero, add_zero, sub_zero] at this
        exact this.symm)
    simp only [finrank_top, finrank_bot, add_zero] at this
    omega

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finrank_homology_resolutions_residueField : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  first | exact @GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | exact GlobalTheory.AbCoh.finrank_homology_base_change_resolutions | (intros; apply GlobalTheory.AbCoh.finrank_homology_base_change_resolutions <;> assumption)
end
end
