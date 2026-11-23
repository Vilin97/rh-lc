module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommute

section

@[expose] public section

namespace GlobalTheory

theorem trace_eq_add_of_shortExact (K : Type) [Field K]
    (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hb : b ∘ₗ i = i ∘ₗ a) (hc : p ∘ₗ b = c ∘ₗ p) :
    LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have hr' : ∀ u, r₀ (i u) = u := fun u => LinearMap.congr_fun hr₀ u
  have hpi : ∀ u, p (i u) = 0 := fun u => by
    have : i u ∈ LinearMap.ker p := hex ▸ LinearMap.mem_range_self i u
    exact this
  have hb' : ∀ u, b (i u) = i (a u) := fun u => LinearMap.congr_fun hb u
  have hc' : ∀ v, p (b v) = c (p v) := fun v => LinearMap.congr_fun hc v
  let r : V →ₗ[K] U := r₀ ∘ₗ (LinearMap.id - s ∘ₗ p)
  have hri : ∀ u, r (i u) = u := fun u => by
    simp [r, hpi, hr']
  have hir : ∀ v, i (r v) = v - s (p v) := fun v => by
    have : v - s (p v) ∈ LinearMap.range i := by
      rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
    obtain ⟨u, hu⟩ := this
    have h2 : r v = u := by
      show r₀ (v - s (p v)) = u
      rw [← hu, hr']
    rw [h2, hu]
  have hdec : b = (b ∘ₗ i) ∘ₗ r + (b ∘ₗ s) ∘ₗ p := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hir, map_sub, sub_add_cancel]
  have h1 : r ∘ₗ (b ∘ₗ i) = a := by
    ext u
    simp only [LinearMap.comp_apply, hb', hri]
  have h2 : p ∘ₗ (b ∘ₗ s) = c := by
    ext w
    simp only [LinearMap.comp_apply, hc', hs']
  calc LinearMap.trace K V b
      = LinearMap.trace K V ((b ∘ₗ i) ∘ₗ r) + LinearMap.trace K V ((b ∘ₗ s) ∘ₗ p) := by
        rw [← map_add (f := _), ← hdec]
    _ = LinearMap.trace K U a + LinearMap.trace K W c := by
        rw [LinearMap.trace_comp_comm' r (b ∘ₗ i), LinearMap.trace_comp_comm' p (b ∘ₗ s), h1, h2]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommuteStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.linear_map_short_exact_commute : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  first | exact @GlobalTheory.trace_eq_add_of_shortExact | exact GlobalTheory.trace_eq_add_of_shortExact | (intros; apply GlobalTheory.trace_eq_add_of_shortExact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwining

section

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_injective : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  intro K L _ _ _ G _ V _ _ _ W _ _ _ ρ σ f hf
  have hcomm : ∀ g, ρ g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ σ g := fun g =>
    (f.isIntertwining' g).symm
  have hle : ∀ g, LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨σ g w, (LinearMap.congr_fun (hcomm g) w).symm⟩
  refine ⟨fun g => algebraMap K L ((ρ.quotient _ hle).character g),
    (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ (ρ.quotient _ hle)).1, fun g => ?_⟩
  rw [← map_add (f := _)]
  congr 1
  refine GlobalTheory.T.linear_map_short_exact_commute K W V _ f.toLinearMap (LinearMap.range f.toLinearMap).mkQ (σ g) (ρ g)
    (ρ.quotient _ hle g) hf (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm (hcomm g) ?_
  ext v
  rfl
end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwiningStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_character_quotient_of_injective_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_injective | exact GlobalTheory.BI.exists_isChar_eq_add_of_injective | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_injective <;> assumption)
end
end
