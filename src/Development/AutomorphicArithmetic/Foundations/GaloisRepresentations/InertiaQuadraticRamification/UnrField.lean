module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AsmUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.CharOrd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecPow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.GroupStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormalOfComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.OrdPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharPP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.KumMove

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.kumMove :
    MoveRoot → NormVal → KumMove := by
  intro hMR hNV Ω _ _ _ U hU ℓ q hℓ hq
  obtain ⟨b, σ0, hσ0U, hσ0⟩ := hMR Ω U hU ℓ hℓ
  obtain ⟨D, hDpos, hD⟩ := hNV Ω U hU q hq
  obtain ⟨e, D', hD'ℓ, hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'
  refine ⟨b + e, fun k hk ζ y hζ hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  have hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a := by
    intro τ a ha ω hω
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hω
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
  have comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y) := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := hpow σ
    obtain ⟨c, hc⟩ := hpow τ
    have h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
        AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]
    have h2 := hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1
    rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply] at h2
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hy
    exact hq0 hy.symm
  obtain ⟨a0, ha0⟩ := hpow σ0
  obtain ⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a :=
    ⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one],
      by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩
  have hjk : ℓ ^ (b + e) ∣ ℓ ^ k := pow_dvd_pow ℓ hk
  have hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a := by
    intro τ hτ
    have hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e)) := by
      rw [← map_pow, hy, map_natCast]
    obtain ⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ := ⟨τ y / y, by field_simp⟩
    have hχj : χ ^ ℓ ^ (b + e) = 1 := by
      rw [hτy', mul_pow] at hτy
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)
    have hχ1 : χ ^ (ℓ ^ k) = 1 := by
      obtain ⟨m, hm⟩ := hjk
      rw [hm, pow_mul, hχj, one_pow]
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hχ1
      exact zero_ne_one hχ1
    rw [map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hχ0)
  have hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1 := by
    have hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q := by rw [← map_pow, hy, map_natCast]
    rw [div_pow, hσy, ← pow_mul', pow_mul, hy]
    have hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel ha1]
    rw [hqa]
    field_simp
  have hdiv := hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq
  have hb : ℓ ^ b ∣ a - 1 := by
    rw [pow_add, hDe] at hdiv
    have h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e := by
      have : (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e := by ring
      rwa [this] at hdiv
    have h'' := Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'
    exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''
  obtain ⟨t, ht⟩ := hb
  have hbk : b ≤ k := by omega
  have hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b) := by
    have := hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero)
      (pow_dvd_pow ℓ (Nat.sub_le k b))
    rwa [Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk] at this
  apply hσ0 _ hξ
  rw [map_pow, ha, ← pow_mul]
  have h1 : a = 1 + ℓ ^ b * t := by rw [← ht]; omega
  have h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t := by
    rw [h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hbk, mul_comm t]
  rw [h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.MoveRoot

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.moveRoot :
    MoveRoot := by
  intro Ω _ _ _ U hU ℓ hℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 (hU.mem_nhds U.one_mem)
  haveI := hEfin
  set b := Module.finrank ℚ E + 2 with hb
  have hn : 0 < ℓ ^ b := pow_pos hℓ.pos b
  haveI : NeZero ((ℓ ^ b : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ0, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ b) Ω)
    (Polynomial.degree_cyclotomic_pos _ Ω hn).ne'
  have hprim : IsPrimitiveRoot ζ0 (ℓ ^ b) := Polynomial.isRoot_cyclotomic_iff.1 hζ0
  have hnot : ζ0 ∉ E := by
    intro hmem
    have h0 := minpoly.natDegree_le (A := ℚ) (⟨ζ0, hmem⟩ : E)
    have h0' := IntermediateField.minpoly_eq (K := ℚ) (S := E) ⟨ζ0, hmem⟩
    have h1 : (minpoly ℚ ζ0).natDegree ≤ Module.finrank ℚ E := h0' ▸ h0
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hℓ (by omega)] at h1
    have h2 : b - 1 < ℓ ^ (b - 1) := Nat.lt_pow_self hℓ.one_lt
    have h3 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    have h4 : ℓ ^ (b - 1) ≤ Module.finrank ℚ E :=
      (Nat.le_mul_of_pos_right _ h3).trans h1
    generalize ℓ ^ (b - 1) = N at h2 h4
    omega
  have hex : ∃ σ ∈ E.fixingSubgroup, σ ζ0 ≠ ζ0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact hcon
  obtain ⟨σ, hσE, hσ⟩ := hex
  refine ⟨b, σ, hEsub hσE, fun ζ hζ hfix => hσ ?_⟩
  haveI : NeZero (ℓ ^ b) := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  rw [← hm, map_pow, hfix]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormVal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.padicValNat_def, Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.MainUnr

section

@[expose] public section

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem unrSplit_holds : UnrSplit :=
  unrSplit_of groupStep (unrCharPP (ordPrime (kumMove moveRoot normVal)) charOrd decPow) (freshSplit freshChar_holds) exFld
    layerOf_holds degOf splitIff

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrField

section

@[expose] public section

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrField_holds : UpperTheory.Gal.NearKilling.UnrField := UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrSplit_holds
end
end
