module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpensStatement
import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEqStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProper

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AffInj

theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

end GlobalTheory.AffInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProperStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom := by
  first | exact @GlobalTheory.AffInj.app_injective_of_isPullback | exact GlobalTheory.AffInj.app_injective_of_isPullback | (intros; apply GlobalTheory.AffInj.app_injective_of_isPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem appTop_injective_of_surjective_toSpec_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  intro R _ _ S π hπ hS
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : π ⁻¹ᵁ (Sp R).basicOpen r = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hr, Scheme.basicOpen_zero]
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ.surj x
  have hy : y ∈ π ⁻¹ᵁ (Sp R).basicOpen r := hx
  rw [h1] at hy
  exact hy.elim

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  first | exact @GlobalTheory.appTop_injective_of_surjective_toSpec_domain | exact GlobalTheory.appTop_injective_of_surjective_toSpec_domain | (intros; apply GlobalTheory.appTop_injective_of_surjective_toSpec_domain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | exact GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | (intros; apply GlobalTheory.Mum.AffDesc.mem_range_app_of_flat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_fibreSquare_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y := by
  intro R _ S Y Z π y p q H r h1 h2
  have A : IsPullback (pullback.fst p p ≫ q) (pullback.snd p p) π (p ≫ y) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback p p) H.flip
  have X : IsPullback r (pullback.snd p p) (pullback.snd π π) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst π π) ?_ h2 (IsPullback.of_hasPullback π π)
    rw [h1, ← H.w]; exact A
  have := IsPullback.paste_vert X H.flip
  rwa [pullback.condition (f := p), pullback.condition (f := π)]

theorem descend_of_equalised_fibreSquare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ _ _ _ S Y Z π y p q hπ hs hS hy H
  have hinj := GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain R S π hs hS
  have heq := GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq R S π hπ hS hinj
  let r : pullback p p ⟶ pullback π π := pullback.map p p π π q q y H.w H.w
  have h1 : r ≫ pullback.fst π π = pullback.fst p p ≫ q := pullback.lift_fst _ _ _
  have h2 : r ≫ pullback.snd π π = pullback.snd p p ≫ q := pullback.lift_snd _ _ _
  have hP := isPullback_fibreSquare_baseChange R S Y Z π y p q H r h1 h2
  exact GlobalTheory.T.app_injective_descent_of_affineOpens Y Z p fun V hV => ⟨GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper R S Y Z π y p q hπ hy H hinj V hV,
    GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised R S Y Z π y p q hπ hy H r h1 h2 hP heq V hV⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.flat_descent_sections_injective_equalizer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.descend_of_equalised_fibreSquare | exact GlobalTheory.descend_of_equalised_fibreSquare | (intros; apply GlobalTheory.descend_of_equalised_fibreSquare <;> assumption)
end
end
