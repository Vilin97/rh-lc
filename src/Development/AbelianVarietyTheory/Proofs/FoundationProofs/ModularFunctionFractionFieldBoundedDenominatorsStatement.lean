module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMemStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGeneratedStatement
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMemStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominator

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem finite_subring_common_denominator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω),
      ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω),
        ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  intro Ω _ _ _ S
  have hZQ : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hZ : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) S
  set D : ℕ := y.natAbs with hDdef
  refine ⟨D, Int.natAbs_pos.mpr hy0, ?_⟩
  have hDint : ∀ j : ℕ, IsIntegral ℤ ((D : Ω) ^ j) := by
    intro j
    have h : ((D : Ω) ^ j) = algebraMap ℤ Ω ((D : ℤ) ^ j) := by simp
    rw [h]
    exact isIntegral_algebraMap
  let T : Subring Ω :=
    { carrier := {x | ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x)}
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a * b) = ((D : Ω) ^ i * a) * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact hi.mul hj
      one_mem' := ⟨0, by simpa using (isIntegral_one : IsIntegral ℤ (1 : Ω))⟩
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a + b) =
            (D : Ω) ^ j * ((D : Ω) ^ i * a) + (D : Ω) ^ i * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact ((hDint j).mul hi).add ((hDint i).mul hj)
      zero_mem' := ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩
      neg_mem' := by
        rintro a ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have : (D : Ω) ^ i * -a = -((D : Ω) ^ i * a) := by ring
        rw [this]; exact hi.neg }
  have hST : (S : Set Ω) ⊆ T := by
    intro x hx
    refine ⟨1, ?_⟩
    have hx' := hy x hx
    rw [pow_one]
    rcases Int.natAbs_eq y with h | h
    · have e : y • x = (D : Ω) * x := by
        rw [zsmul_eq_mul]; congr 1; rw [h]; simp [hDdef]
      rw [← e]; exact hx'
    · have e : y • x = -((D : Ω) * x) := by
        rw [zsmul_eq_mul, h]; simp [hDdef]
      have := hx'.neg
      rw [e, neg_neg] at this
      exact this
  intro x hx
  exact (Subring.closure_le.mpr hST) hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominatorStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.algebraic_subring_closure_common_denominator : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω), ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω), ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  first | exact @GlobalTheory.finite_subring_common_denominator | exact GlobalTheory.finite_subring_common_denominator | (intros; apply GlobalTheory.finite_subring_common_denominator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubring

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem coeff_fg : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω),
    InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε f h hf hh
  obtain ⟨N, w, hN, hLv⟩ := hf
  obtain ⟨b, hb, hbE⟩ := hLv.2 1
  have hb' : HasQ N (fun τ => DD τ ^ w * f τ) b := by
    simpa only [one_smul] using hb
  choose a ha using fun n => (hbE n : b n ∈ ε.range)
  have hb'' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) := by
    have : (fun n => ε (a n)) = b := funext ha
    rw [this]; exact hb'
  obtain ⟨S, hS⟩ := GlobalTheory.T.qExpansion_coeffs_mem_finitelyGenerated Ω ε N w f a hN hLv hb''
  obtain ⟨H, hH, hHa, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N (fun τ => DD τ ^ w * f τ) a hN hb''
  obtain ⟨hD, hDe, hD0, hDl, hDz⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨hmul, hinv⟩ := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω (Subring.closure (S : Set Ω))
  set A := Subring.closure (S : Set Ω)

  have hpow : ∀ k : ℕ, IsExp ε (fun τ => DD τ ^ k) (hD ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hC 1
      simpa [map_one] using this
    | succ k ih =>
      have e : (fun τ => DD τ ^ (k + 1)) = (fun τ => DD τ ^ k) * DD := by
        funext τ; simp [pow_succ]
      rw [e, pow_succ]
      exact (hops _ _ _ _ ih hDe).2.2
  have hprod : IsExp ε (fun τ => DD τ ^ w * f τ) (hD ^ w * h) := (hops _ _ _ _ (hpow w) hh).2.2
  have hEq : hD ^ w * h = H := huniq _ _ _ hprod hH
  have hDw0 : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hEq' : h = H * (hD⁻¹) ^ w := by
    rw [← hEq, inv_pow, mul_comm (hD ^ w) h, mul_assoc, mul_inv_cancel₀ hDw0, mul_one]

  have hHA : ∀ r, H.coeff r ∈ A := by
    intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hHa k]; exact hS k
    · push_neg at hr
      rw [hH0 r hr]; exact A.zero_mem
  have hDA : ∀ r, hD.coeff r ∈ A := by
    intro r
    obtain ⟨n, hn⟩ := hDz r
    rw [hn]; exact intCast_mem A n
  have hDiA : ∀ r, (hD⁻¹).coeff r ∈ A := hinv hD hDA (by rw [hDl, inv_one]; exact A.one_mem)
  have hpA : ∀ k : ℕ, ∀ r, ((hD⁻¹) ^ k).coeff r ∈ A := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [pow_zero]
      by_cases hr : r = 0
      · subst hr; simpa using A.one_mem
      · simpa [hr] using A.zero_mem
    | succ k ih =>
      intro r
      rw [pow_succ]
      exact hmul _ _ ih hDiA r
  refine ⟨S, fun r => ?_⟩
  rw [hEq']
  exact hmul _ _ hHA (hpA w) r

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubringStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  first | exact @GlobalTheory.FN.coeff_fg | exact GlobalTheory.FN.coeff_fg | (intros; apply GlobalTheory.FN.coeff_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2
    exact GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominatorsStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_bounded_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  first | exact @GlobalTheory.FN.frac_bdd_den | exact GlobalTheory.FN.frac_bdd_den | (intros; apply GlobalTheory.FN.frac_bdd_den <;> assumption)
end
end
