module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.EtaleCohomology.EtaleTrace.LFinCut

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LFinCut

theorem normal_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) [Smooth p] : GlobalTheory.IsNormalScheme X := by
  rw [GlobalTheory.isNormalScheme_iff]
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p fun y => ?_
  have hf : IsField ((S k).presheaf.stalk y) := isField_stalk_of_closure_mem_irreducibleComponents (S k) y (by
    have : closure ({y} : Set (S k)) = Set.univ := Set.eq_univ_of_forall fun z => subset_closure (Subsingleton.elim z y)
    rw [this, irreducibleComponents_eq_singleton]; rfl)
  let := hf.toField
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.LFinCut

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCompSum

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.compSum_of :
    CompSum := by
  intro k _ X p hs hpr
  haveI := hs
  haveI := hpr
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : GlobalTheory.IsNormalScheme X := LateralTheory.EtaleTrace.LFinCut.normal_of_smooth p
  haveI : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := {}
  haveI : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  have hopen : ∀ Z : irreducibleComponents X, IsOpen (Z : Set X) :=
    fun Z => (GlobalTheory.IsNormalScheme.component Z).isOpen
  refine ⟨Nat.card (irreducibleComponents X), fun s => (GlobalTheory.IsNormalScheme.component (e.symm s) : Scheme),
    fun s => (GlobalTheory.IsNormalScheme.component (e.symm s)).ι, ⟨fun s => inferInstance, ?_, ?_⟩, ?_⟩
  · intro x
    refine ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι, Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  · intro s s' hss'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have hne : e.symm s ≠ e.symm s' := fun h => hss' (e.symm.injective h)
    show Disjoint ((e.symm s : Set X)) ((e.symm s' : Set X))
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hne
    have h12 : ((e.symm s : Set X)) ⊆ (e.symm s' : Set X) :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen (e.symm s).2.1.isPreirreducible
        (hopen (e.symm s')) hn).trans
        (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents _ (e.symm s').2))
    exact Subtype.ext (le_antisymm h12 ((e.symm s).2.2 (e.symm s').2.1 h12))
  · intro s
    haveI : IsReduced X := by
      haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
        obtain ⟨hd, -⟩ := ‹GlobalTheory.IsNormalScheme X›
        haveI := hd x
        infer_instance
      exact isReduced_of_isReduced_stalk X
    haveI : IrreducibleSpace ((GlobalTheory.IsNormalScheme.component (e.symm s) : X.Opens) : Set X) :=
      Subtype.irreducibleSpace (e.symm s).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
end
end
