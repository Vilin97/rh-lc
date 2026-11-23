module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolyInRootOfInertiaCyclotomicFixedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuation

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaFieldUnram

theorem valuation_eq_zpow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k :=
  GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed

end GlobalTheory.InertiaFieldUnram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | exact GlobalTheory.InertiaFieldUnram.valuation_eq_zpow | (intros; apply GlobalTheory.InertiaFieldUnram.valuation_eq_zpow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotient

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem valuation_primitiveRoot_sub_one_pow_totient :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ),
      1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
        A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  intro l hl Ω _ _ A m hm ζ hζ
  have hpos : 0 < l ^ m := pow_pos hl.out.pos m

  have memA : ∀ x : Ω, x ^ (l ^ m) = 1 → x ∈ A := by
    intro x hx
    rcases A.mem_or_inv_mem x with h | h
    · exact h
    · have h1 : x * x ^ (l ^ m - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]; exact hx
      have h2 : x⁻¹ = x ^ (l ^ m - 1) := inv_eq_of_mul_eq_one_right h1
      have h3 : x = (x⁻¹) ^ (l ^ m - 1) := by
        rw [inv_pow, ← h2, inv_inv]
      rw [h3]; exact A.pow_mem h _
  have key : ∀ x : Ω, x ∈ A → ∀ a : ℕ, A.valuation (x ^ a - 1) ≤ A.valuation (x - 1) := by
    intro x hx a
    rw [← geom_sum_mul, map_mul]
    have hs : A.valuation (∑ i ∈ Finset.range a, x ^ i) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (sum_mem fun i _ => A.pow_mem hx i)
    calc _ ≤ 1 * A.valuation (x - 1) := by gcongr
      _ = _ := one_mul _
  have eqv : ∀ η ∈ primitiveRoots (l ^ m) Ω, A.valuation (1 - η) = A.valuation (ζ - 1) := by
    intro η hη
    have hη' : IsPrimitiveRoot η (l ^ m) := (mem_primitiveRoots hpos).1 hη
    rw [Valuation.map_sub_swap]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hη'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hη'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← ha]; exact key ζ (memA ζ hζ.pow_eq_one) a
    · rw [← hb]; exact key η (memA η hη'.pow_eq_one) b
  have hprod : (l : Ω) = ∏ η ∈ primitiveRoots (l ^ m) Ω, (1 - η) := by
    have e1 := Polynomial.eval_one_cyclotomic_prime_pow (R := Ω) (p := l) (m - 1)
    rw [Nat.sub_add_cancel hm, cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at e1
    simpa using e1.symm
  rw [hprod, map_prod, Finset.prod_congr rfl eqv, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotientStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | exact GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CycIne

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  intro l _ Ω _ _ _ A hA m ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Polynomial.C u, ?_, by simp⟩
    intro x hx
    have hxu : x = u := by
      obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
      rw [Polynomial.mem_support_iff, Polynomial.coeff_C] at hn
      rw [Polynomial.coeff_C]
      split_ifs at hn ⊢ with h
      · rfl
      · exact absurd rfl hn
    subst hxu
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩
  · obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix
    have hl : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hlv⟩ := hA
      have := (hv (l : 𝓞 ℚ)).2 hlv
      simpa using this
    let K : Subfield Ω := (IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield
    have hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F := ℚ) A, s x = x := fun x =>
      IntermediateField.mem_fixedField_iff _ x
    obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified l Ω A hl K
      (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero l Ω A m hm ζ hζ) u hu ⟨Q, fun x hx => (hK x).2 (hQ x hx), hQe⟩
    exact ⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩

end GlobalTheory.CycIne
end
end
