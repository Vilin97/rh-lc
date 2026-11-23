module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamifiedStatement
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolyInRootOfInertiaCyclotomicFixed

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaCycFixed

theorem cycMod_eq_one_of_fix (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hs : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := m)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
  have hs' : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ = ζ := hs
  rw [hs'] at hspec
  set x : ZMod (l ^ m) := ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow m)
    with hx
  have hmod : x.val ≡ 1 [MOD l ^ m] := by
    have hne : l ^ m ≠ 0 := pow_ne_zero m (Fact.out : l.Prime).ne_zero
    have hz : IsPrimitiveRoot (hζ.isUnit hne).unit (l ^ m) := IsPrimitiveRoot.isUnit_unit hne hζ
    have key := (pow_eq_pow_iff_modEq (x := (hζ.isUnit hne).unit) (n := x.val) (m := 1)).1 (by
      ext
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_one]
      exact hspec.symm)
    rwa [← hz.eq_orderOf] at key
  have h1 : ((x.val : ℕ) : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  apply Units.ext
  simpa [cycMod, cycZ, hx] using h1

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u : Ω, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A m ζ hζ u hu
  have : IsGalois ℚ Ω := {}
  have hint : Algebra.IsIntegral ℚ Ω := Algebra.IsAlgebraic.isIntegral
  set I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A with hI
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField I with hK
  have : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set L : IntermediateField ℚ Ω := (IntermediateField.adjoin K {ζ}).restrictScalars ℚ with hL
  have hKL : K ≤ L := fun x hx => by
    show x ∈ IntermediateField.adjoin K {ζ}
    exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨x, hx⟩
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self K ζ

  have hfix : ∀ s ∈ L.fixingSubgroup, s u = u := by
    intro s hs

    let C : ClosedSubgroup (G ℚ Ω) := ⟨I.topologicalClosure, I.isClosed_topologicalClosure⟩
    have hsC : s ∈ I.topologicalClosure := by
      have hle : IntermediateField.fixedField C.toSubgroup ≤ K := by
        intro x hx
        rw [IntermediateField.mem_fixedField_iff] at hx ⊢
        intro f hf
        exact hx f (I.le_topologicalClosure hf)
      have h1 : s ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hKL hs
      have h2 := IntermediateField.fixingSubgroup_antitone hle h1
      rwa [InfiniteGalois.fixingSubgroup_fixedField C] at h2

    set E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {u, ζ} with hE
    have : FiniteDimensional ℚ E := by
      rw [hE]
      refine IntermediateField.finiteDimensional_adjoin ?_
      intro x _
      exact Algebra.IsIntegral.isIntegral x
    have hopen : IsOpen ((E.fixingSubgroup : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := E.fixingSubgroup_isOpen
    have hopen' : IsOpen {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} :=
      hopen.preimage (continuous_const.mul continuous_id)
    have hsmem : s ∈ {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact one_mem _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hsC
    obtain ⟨i, hi1, hi2⟩ := mem_closure_iff.1 hsC _ hopen' hsmem
    simp only [Set.mem_ofPred_eq] at hi1
    have hu' : (s⁻¹ * i) u = u :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 u (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hζ' : (s⁻¹ * i) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 ζ (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hsζ : s ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζL
    have hiζ : i ζ = ζ := by
      have : i = s * (s⁻¹ * i) := by group
      rw [this, AlgEquiv.mul_apply, hζ', hsζ]
    have hiu : i u = u := hu i hi2 (cycMod_eq_one_of_fix l Ω m ζ hζ i hiζ)
    have : i = s * (s⁻¹ * i) := by group
    rw [this, AlgEquiv.mul_apply, hu'] at hiu
    exact hiu
  have huL : u ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    exact hfix
  have huK : u ∈ IntermediateField.adjoin K {ζ} := huL
  have hζint : IsIntegral K ζ := (Algebra.IsIntegral.isIntegral (R := ℚ) ζ).tower_top
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at huK
  obtain ⟨P, hP⟩ := huK
  refine ⟨P.map (algebraMap K Ω), ?_, ?_⟩
  · intro x hx s hs
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [Polynomial.coeff_map]
    exact ((IntermediateField.mem_fixedField_iff _ _).1 (P.coeff n).2) s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hP

end GlobalTheory.InertiaCycFixed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolyInRootOfInertiaCyclotomicFixedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u : Ω, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.InertiaCycFixed.exists_poly_of_fixed | exact GlobalTheory.InertiaCycFixed.exists_poly_of_fixed | (intros; apply GlobalTheory.InertiaCycFixed.exists_poly_of_fixed <;> assumption)
end
end

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
