module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
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
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly

-- Source module: Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion

section

@[expose] public section

open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_of_integral_version : ∀ (k : Type) [Field k] (N e d : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f : MvPolynomial (Fin (e + 1) × Fin N) k), GlobalTheory.ChowHt.IsChowFormInt I e d f → GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  intro k _ N e d I f h
  refine ⟨h.ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · exact h.dvd_of_forall_aeval_eq_zero fun u hu => hg u ((h.zero_iff u).1 hu)
  · rintro ⟨a, rfl⟩ u hu
    rw [map_mul, (h.zero_iff u).2 hu, zero_mul]

end ChowFormCompatibility
end
end

-- Source module: Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormUniqueUpToConstant

section

@[expose] public section

open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_unique_up_to_constant : ∀ (k : Type) [Field k] (N B : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f g : MvPolynomial (Fin B × Fin N) k), GroundTheory.Heights₂.Heights.IsChowForm I B f → GroundTheory.Heights₂.Heights.IsChowForm I B g → ∃ c : k, c ≠ 0 ∧ g = C c * f := by
  intro k _ N B I f g hf hg
  have hfg : f ∣ g := (hf.2 g).1 ((hg.2 g).2 dvd_rfl)
  have hgf : g ∣ f := (hg.2 f).1 ((hf.2 f).2 dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hfg hgf
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end ChowFormCompatibility
end
end

-- Source module: Development.WeilBound.CoreStatements.NefModelVolumes.HyperplaneSectionDivCycle

section

@[expose] public section

open MvPolynomial

namespace ChowFormCompatibility

theorem projCycle_eq_fundCycle {k : Type} [Field k] {N : ℕ} (J : Ideal (MvPolynomial (Fin N) k)) :
    GlobalTheory.ChowHt.projCycle J = GroundTheory.Heights₂.Heights.fundCycle J := by
  ext Q
  rw [GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]
  by_cases hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J
  · haveI hp : Q.IsPrime := hQ.1.1.1
    have h1 := GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ
    rw [if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dite_eq_left hp]
    have h2 := congrArg ENat.toNat h1
    rw [ENat.toNat_coe] at h2
    exact h2
  · rw [if_neg hQ]
    exact GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ

theorem hyperplane_section_divCycle : ∀ (k : Type) [Field k] (N B : ℕ) (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k), GlobalTheory.ChowHt.hyperplaneSection P u = GroundTheory.Heights₂.Heights.divCycle P u ∧ GlobalTheory.ChowHt.fixFirstBlock u f = GroundTheory.Heights₂.Heights.specFirst f u := by
  intro k _ N B P u f
  refine ⟨projCycle_eq_fundCycle _, ?_⟩
  have h : (fun p : Fin (B + 1) × Fin N =>
      (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
        Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) =
      GroundTheory.Heights₂.Heights.specFirstVar u := by
    funext ⟨b, j⟩
    induction b using Fin.cases with
    | zero => rfl
    | succ b => rfl
  rw [GlobalTheory.ChowHt.fixFirstBlock, h]
  rfl

end ChowFormCompatibility
end
end

-- Source module: Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormHyperplaneSection

section

@[expose] public section

open MvPolynomial

namespace ChowFormCompatibility

attribute [local instance] MvPolynomial.gradedAlgebra

theorem chow_form_hyperplane_section : GlobalTheory.Published.ChowFormHyperplaneSection := by
  unfold GlobalTheory.Published.ChowFormHyperplaneSection
  intro k _ _ N e P hP hprime _ u hu dl f hf d g hg
  have hrel : GroundTheory.Heights₂.Heights.IsRelevant P := by
    by_contra h
    simp only [GroundTheory.Heights₂.Heights.IsRelevant, not_exists, not_not] at h
    exact hu (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  have hproj : GroundTheory.Heights₂.Heights.IsProjPrime P :=
    ⟨hprime, (GroundTheory.Heights₂.Heights.isHomogIdeal_iff P).2 hP, hrel⟩
  have hf' := chow_form_of_integral_version k N (e + 1) dl P f hf
  obtain ⟨c, hc, g', hg', heq⟩ :=
    GroundTheory.Heights₂.Heights.ChowFormSection.full k N (e + 1) P f u hproj hf' hu
  obtain ⟨hsec, hfix⟩ := hyperplane_section_divCycle k N (e + 1) P u f
  have key : ∀ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support,
      ∃ a : k, a ≠ 0 ∧ g' Q = C a * g Q := by
    intro Q hQ
    have hQ' : Q ∈ (GlobalTheory.ChowHt.hyperplaneSection P u).support := by
      rw [hsec]
      exact hQ
    exact chow_form_unique_up_to_constant k N (e + 1) Q (g Q) (g' Q) (chow_form_of_integral_version k N e (d Q) Q (g Q) (hg Q hQ')) (hg' Q hQ)
  choose! a ha hga using key
  refine ⟨c * ∏ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support, a Q ^ (GroundTheory.Heights₂.Heights.divCycle P u) Q, ?_, ?_⟩
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (ha Q hQ))
  · rw [hfix, heq, hsec, Finsupp.prod, map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hga Q hQ, mul_pow, map_pow]

end ChowFormCompatibility
end
end
