module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelDefs
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import GroundTheory.GlobalFields.SecondInequality.Cyclic
public import GroundTheory.TateCohomology.Herbrand
public import Mathlib.RepresentationTheory.Coinduced
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
public import GroundTheory.TateCohomology.HerbrandAbstract
public import GroundTheory.TateCohomology.TateLow
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.Tactic.TypeStar

-- Source module: GroundTheory.TateCohomology.HerbrandRep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom

theorem repSubOne_apply (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl

variable [Fintype G]

def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom

end GroundTheory.GroupCoh
end
end

-- Source module: GroundTheory.TateCohomology.HerbrandTate

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]


omit [Fintype G] in
theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelCyclic

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem natCard_tateCohomology_zero_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) 0) = finrank K L := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_zero _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).1

theorem natCard_tateCohomology_neg_one_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) (-1)) = 1 := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_neg_one _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).2

variable [IsCyclic Gal(L/K)]

theorem isZero_groupCohomology_one_ideleClassRep_of_isCyclic :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have e2 : (-1 + 2 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
  have h0 : Nat.card (groupCohomology (ideleClassRep K L) 1) =
      Nat.card (tateCohomology (ideleClassRep K L) ((1 : ℕ) : ℤ)) :=
    (Nat.card_congr
      ((TateCohomology.isoGroupCohomology 1).app (ideleClassRep K L)).toLinearEquiv.toEquiv).symm
  have h1 : Nat.card (tateCohomology (ideleClassRep K L) (-1 + 2)) =
      Nat.card (tateCohomology (ideleClassRep K L) (-1)) :=
    Nat.card_congr
      (GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ (-1)).toLinearEquiv.toEquiv
  have h : Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [h0, ← e2, h1]
    exact natCard_tateCohomology_neg_one_ideleClassRep σ hσ
  have : Subsingleton (groupCohomology (ideleClassRep K L) 1) :=
    (Nat.card_eq_one_iff_unique.1 h).1
  exact ModuleCat.isZero_of_subsingleton _

theorem natCard_groupCohomology_two_ideleClassRep_of_isCyclic :
    Nat.card (groupCohomology (ideleClassRep K L) 2) = finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (ideleClassRep K L) 2 ≅ tateCohomology (ideleClassRep K L) 0 :=
    ((TateCohomology.isoGroupCohomology 2).app (ideleClassRep K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ 0
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  exact natCard_tateCohomology_zero_ideleClassRep σ hσ

end GroundTheory.ProfCoh
end
end
