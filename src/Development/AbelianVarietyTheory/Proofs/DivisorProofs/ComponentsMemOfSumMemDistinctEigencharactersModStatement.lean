module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSumMem

section

@[expose] public section

namespace GlobalTheory.MembershipOfSum

theorem mem_of_sum_mem {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ (c : O), ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ (i j : Fin a), i ≠ j → ∃ (c : O), χ i c ≠ χ j c) (S : Finset (Fin a))
    (u : Fin a → H) (hu : ∀ i ∈ S, ∀ (c : O), ρ c (u i) - χ i c • u i ∈ F)
    (hs : ∑ i ∈ S, u i ∈ F) : ∀ i ∈ S, u i ∈ F := by
  induction S using Finset.induction_on generalizing u with
  | empty => intro i hi; simp at hi
  | insert j S hj ih =>
    have key : ∀ i ∈ S, u i ∈ F := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨c, hc⟩ := hχ i j hij
      have h1 : ∑ l ∈ insert j S, (χ l c - χ j c) • u l ∈ F := by
        have e : ∑ l ∈ insert j S, (χ l c - χ j c) • u l =
            ρ c (∑ l ∈ insert j S, u l) - χ j c • ∑ l ∈ insert j S, u l
              - ∑ l ∈ insert j S, (ρ c (u l) - χ l c • u l) := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sub_smul]; abel
        rw [e]
        exact F.sub_mem (F.sub_mem (hF c _ hs) (F.smul_mem _ hs))
          (F.sum_mem fun l hl => hu l hl c)
      rw [Finset.sum_insert hj, sub_self, zero_smul, zero_add] at h1
      have h2 := ih (fun l => (χ l c - χ j c) • u l) (by
        intro l hl d
        have := F.smul_mem (χ l c - χ j c) (hu l (Finset.mem_insert_of_mem hl) d)
        rw [smul_sub, smul_comm] at this
        rw [map_smul]
        exact this) h1 i hi
      exact (F.smul_mem_iff (sub_ne_zero.mpr hc)).mp h2
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_insert hj] at hs
      have := F.sub_mem hs (F.sum_mem key)
      simpa using this
    · exact key i hi

end GlobalTheory.MembershipOfSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsMemOfSumMemDistinctEigencharactersMod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory

theorem eigen_components_mod_stable {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ c, ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) (S : Finset (Fin a)) :
    ∀ u : Fin a → H, (∀ i ∈ S, ∀ c, ρ c (u i) - χ i c • u i ∈ F) →
      ∑ i ∈ S, u i ∈ F → ∀ i ∈ S, u i ∈ F := by
  first
  | exact @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | (apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem ..)

theorem eigen_mod_stable : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  intro k _ H _ _ O _ ρ F hF a χ hχ u hu hs i
  exact eigen_components_mod_stable ρ F hF χ hχ Finset.univ u (fun i _ c => hu i c) hs i (Finset.mem_univ i)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsMemOfSumMemDistinctEigencharactersModStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  first | (exact @GlobalTheory.eigen_mod_stable) | (exact GlobalTheory.eigen_mod_stable) | (intros; apply GlobalTheory.eigen_mod_stable <;> assumption)
end
end
