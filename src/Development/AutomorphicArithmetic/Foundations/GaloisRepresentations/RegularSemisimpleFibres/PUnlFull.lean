module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubquotientOfProductOfSupport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfExtTensor

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

section Tensor

variable {G H V V' U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup U] [Module ℂ U]

end Tensor

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnlFull

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unlFull :
    UnlFull := by
  intro k _ _ _ _ _ N V _ _ π s x hd hs hu
  have hmem : ∀ a, x a ∈ Finset.univ.val.map x := fun a =>
    Multiset.mem_map_of_mem x (Finset.mem_univ_val a)
  have hx : ∀ a, (x a).IsCusp := fun a => hs.isCusp (hmem a)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k s N (fun a => Segment.single (x a) (hx a)) x hd
      (fun a b => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx a) (hx b) (hu _ (hmem b) _ (hmem a))
        (hu _ (hmem a) _ (hmem b)))
      (fun a => (single_spec (hx a)).2.1)
  have h1 := GlobalTheory.LocGL.SupportPerm.isSubquotient_prodIrr_of_hasSupport
    UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N s ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ x hd hs
  haveI := GlobalTheory.ReducedFactor.nontrivial_of_irr hs.isIrreducible
  have equiv_of_sub {G A B : Type} [Group G] [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] {σ : Representation ℂ G B}
      {ρ : Representation ℂ G A} (h : IsSubquotient σ ρ) [Nontrivial B]
      (hirr : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : B)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_of_sub h1 hP
  exact ⟨E.symm⟩
end
end
