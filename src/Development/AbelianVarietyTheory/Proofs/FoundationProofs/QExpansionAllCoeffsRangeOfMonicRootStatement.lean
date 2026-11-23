module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSumStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansionsStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbit

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add (f := _), map_natCast, map_add (f := _), map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbitStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit : ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  first | exact @GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | exact GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | (intros; apply GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRootStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 → ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  first | exact @GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | exact GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | (intros; apply GlobalTheory.PsRoot.coeff_mem_range_of_isRoot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRoot

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem qAll_isBoundedAtImInfty {p : ℂ → Prop} {N : ℕ} {f : ℍ → ℂ} (hN : 0 < N) (h : QAll p N f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨a, ha, -⟩ := h
  exact (GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).2

theorem isBoundedAtImInfty_of_monic_root {n : ℕ} {h : ℍ → ℂ} {s : Fin n → ℍ → ℂ}
    (hs : ∀ j, UpperHalfPlane.IsBoundedAtImInfty (s j))
    (hrel : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) : UpperHalfPlane.IsBoundedAtImInfty h := by
  have hb : ∀ τ, ‖h τ‖ ≤ 1 + ∑ j, ‖s j τ‖ := fun τ => GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hrel τ)
  have hsum : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
    refine Asymptotics.IsBigO.add (Asymptotics.isBigO_refl _ _) ?_
    convert Asymptotics.IsBigO.sum (A := fun j τ => ‖s j τ‖) (s := Finset.univ) (fun j _ => (hs j).norm_left) using 1
    ext τ; simp [Finset.sum_apply]
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun τ => ?_) hsum
  refine (hb τ).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.FN

namespace GlobalTheory.FN

theorem qAll_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  intro Ω _ _ ε N n h s hN hh hper hs hrel
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hh hper
    (isBoundedAtImInfty_of_monic_root (fun j => qAll_isBoundedAtImInfty hN (hs j)) hrel)
  choose a ha hain using hs
  let p : ℕ → ℍ → ℂ := fun i => if hi : i < n then s ⟨i, hi⟩ else fun _ => 1
  let c : ℕ → ℕ → ℂ := fun i => if hi : i < n then a ⟨i, hi⟩ else fun k => if k = 0 then 1 else 0
  have hp : ∀ i, HasQ N (p i) (c i) := by
    intro i
    by_cases hi : i < n
    · simpa [p, c, hi] using ha ⟨i, hi⟩
    · simpa [p, c, hi] using HasQ.const N 1
  have hrel' : ∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * h τ ^ i = 0 := by
    intro τ
    rw [Finset.sum_range_succ, Finset.sum_range, add_comm, ← hrel τ]
    simp [p]
  have hQ := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n h b p c hN hb hp hrel'
  set Q := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i)) with hQdef
  have hcoeff : ∀ i, Q.coeff i = if i < n + 1 then PowerSeries.mk (c i) else 0 := by
    intro i
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun j => PowerSeries.mk (c j))]
    simp
  have hcn : PowerSeries.mk (c n) = 1 := by
    ext k
    simp [c, PowerSeries.coeff_one]
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hcoeff n
    rw [h0, if_pos (Nat.lt_succ_self n), hcn] at this
    simp at this
  have hcr : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range := by
    intro i k
    rw [hcoeff i]
    split_ifs with hi
    · rw [PowerSeries.coeff_mk]
      by_cases hin : i < n
      · simpa [c, hin] using hain ⟨i, hin⟩ k
      · simp only [c, hin, dite_false]
        split_ifs
        · exact ⟨1, map_one ε⟩
        · exact ⟨0, map_zero ε⟩
    · simp only [map_zero]
      exact ⟨0, map_zero ε⟩
  have key := GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range Ω ε (PowerSeries.mk b) Q hQ0 hcr hQ
  exact ⟨b, hb, fun k => by simpa using key k⟩

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRootStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  first | exact @GlobalTheory.FN.qAll_range_of_monic_root | exact GlobalTheory.FN.qAll_range_of_monic_root | (intros; apply GlobalTheory.FN.qAll_range_of_monic_root <;> assumption)
end
end
