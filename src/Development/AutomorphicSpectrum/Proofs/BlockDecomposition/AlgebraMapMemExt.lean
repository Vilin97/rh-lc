module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansion

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.QPd

theorem exists_sub_one_pow {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] (x : B) :
    ∃ z : B, (x - 1) ^ (p - 1) = (∑ i ∈ Finset.range p, x ^ i) - (p : B) * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : ((X - 1 : (ZMod p)[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
    have h1 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
      simpa using sub_pow_char (X : (ZMod p)[X]) 1
    have h2 : (X - 1 : (ZMod p)[X]) * ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i = X ^ p - 1 :=
      mul_geom_sum _ _
    have h3 : (X - 1 : (ZMod p)[X]) ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    have h4 : (X - 1 : (ZMod p)[X]) * ((X - 1) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
      rw [mul_sub, h2, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left h3
  have hdvd : C (p : ℤ) ∣ ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i) := by
    have hmap : ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map
        (Int.castRingHom (ZMod p)) = 0 := by

      simpa [Polynomial.map_sum] using hmod
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have h5 := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) hmap
    simp only [coeff_map, coeff_zero] at h5
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using h5)
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨-aeval x g, ?_⟩
  have := congrArg (aeval x) hg

  simp only [map_sub, map_pow, aeval_X, map_one, map_sum, map_mul, aeval_C] at this
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at this
  linear_combination this

theorem not_dvd_choose {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ (a * p + c).choose c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a * p + c) (k := c)
  have h1 : (a * p + c) % p = c := by
    rw [Nat.mul_add_mod_of_lt hc] <;> simp
  have h2 : c % p = c := Nat.mod_eq_of_lt hc
  have h3 : c / p = 0 := Nat.div_eq_of_lt hc
  rw [h1, h2, h3] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans h
  have := (Nat.modEq_iff_dvd.1 h0)
  simp at this
  have h5 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h5)

theorem not_dvd_uniformBell {p : ℕ} (hp : p.Prime) (a : ℕ) : ¬ p ∣ Nat.uniformBell a p := by
  induction a with
  | zero => simpa [Nat.uniformBell_zero_left] using hp.one_lt.ne'
  | succ a ih =>
    rw [Nat.uniformBell_succ_left]
    intro h
    rcases (hp.dvd_mul).1 h with h | h
    · refine not_dvd_choose hp a (p - 1) (Nat.sub_lt hp.pos one_pos) ?_
      have h6 : a * p + (p - 1) = a * p + p - 1 := by have := hp.pos; omega
      rwa [h6]
    · exact ih h

theorem exists_inv {B : Type} [CommRing B] {p N : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B))
    (h : ¬ p ∣ N) : ∃ v : B, v * N = 1 := by
  obtain ⟨e, he⟩ := hnil
  have hc : IsCoprime (N : ℤ) ((p : ℤ) ^ e) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨s, t, hst⟩ := hc
  refine ⟨s, ?_⟩
  have := congrArg (Int.cast : ℤ → B) hst
  push_cast at this
  rw [he] at this
  simpa using this

theorem pow_dvd_factorial {p : ℕ} (hp : p.Prime) (e : ℕ) : p ^ e ∣ (p * e).factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_pow_eq_zero {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ}
    (hp : p.Prime) (hnil : IsNilpotent (p : B)) : ∃ n : ℕ, ∀ y ∈ J, y ^ n = 0 := by
  obtain ⟨e, he⟩ := hnil
  refine ⟨p * e, fun y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := pow_dvd_factorial hp e
  rw [← δ.factorial_mul_dpow_eq_pow hy, hk]
  push_cast
  rw [he]
  simp

theorem not_dvd_coeff {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial := by
  rw [Nat.choose_symm_add]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact not_dvd_uniformBell hp a h
    · exact not_dvd_choose hp a c hc h
  · exact absurd ((hp.dvd_factorial).1 h) (not_le.2 hc)

section
variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem coeff_mul_dpow {p : ℕ} (hp : p.Prime) {μ w : B} (hμ : μ ∈ J) (hw : w ∈ J)
    (h : δ.dpow p μ = μ * w) (a c : ℕ) :
    ((Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial : ℕ) : B) *
        δ.dpow (a * p + c) μ = μ ^ (a + c) * δ.dpow a w := by
  have h1 : (Nat.uniformBell a p : B) * δ.dpow (a * p) μ = μ ^ a * δ.dpow a w := by
    rw [← δ.dpow_comp hp.ne_zero hμ, h, δ.dpow_mul hw]
  have h2 := δ.mul_dpow (m := a * p) (n := c) hμ
  have h3 := δ.factorial_mul_dpow_eq_pow (n := c) hμ
  push_cast
  rw [pow_add]
  linear_combination (-(Nat.uniformBell a p : B) * (c.factorial : B)) * h2 +
    (c.factorial : B) * δ.dpow c μ * h1 + μ ^ a * δ.dpow a w * h3

theorem exists_dpow_prime_eq {p : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B)) (x : B)
    (hξ : (∑ i ∈ Finset.range p, x ^ i) ∈ J) :
    ∃ w ∈ GlobalTheory.Cris.ExpBij.dpFil δ (p - 1), δ.dpow p (x ^ p - 1) = (x ^ p - 1) * w := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  simp only [Nat.add_sub_cancel] at *
  set ξ := ∑ i ∈ Finset.range (q + 1), x ^ i with hξdef
  obtain ⟨z, hz⟩ := exists_sub_one_pow hp x
  simp only [Nat.add_sub_cancel, ← hξdef] at hz
  obtain ⟨u, hu⟩ := exists_inv (N := q.factorial) hp hnil
    (fun h ↦ absurd ((hp.dvd_factorial).1 h) (by omega))
  have hμ : x ^ (q + 1) - 1 = (x - 1) * ξ := (mul_geom_sum x (q + 1)).symm
  have h2 := δ.factorial_mul_dpow_eq_pow (n := q + 1) hξ
  rw [Nat.factorial_succ] at h2
  push_cast at h2 hz
  refine ⟨δ.dpow (q + 1) ξ - z * u * ξ ^ q, ?_, ?_⟩
  · refine Ideal.sub_mem _ (GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ q)
      (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hξ _)) (Ideal.mul_mem_left _ _ ?_)
    simpa using GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hξ) q
  · rw [hμ, δ.dpow_mul hξ, pow_succ]
    linear_combination (x - 1) * δ.dpow (q + 1) ξ * hz +
      (x - 1) * z * ((q : B) + 1) * δ.dpow (q + 1) ξ * hu - (x - 1) * z * u * h2

end

theorem dpow_pow_sub_one : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  intro B _ J δ p hp hnil x hξ
  have hμJ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hξ
  obtain ⟨n, hn⟩ := exists_pow_eq_zero δ hp hnil
  obtain ⟨w, hwf, hw⟩ := exists_dpow_prime_eq δ hp hnil x hξ
  have hp2 := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hwJ : w ∈ J := GlobalTheory.Cris.ExpBij.dpFil_le δ hp1 hwf
  generalize x ^ p - 1 = μ at hμJ hw ⊢
  have key : ∀ m, ∃ b : B, (m = 1 → b = 1) ∧
      (1 ≤ m → δ.dpow m μ = μ * b ∧ b ∈ GlobalTheory.Cris.ExpBij.dpFil δ (m - 1)) ∧
      (p * (n + 2) ≤ m → b = 0) := by
    intro m
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact ⟨0, by simp, by simp, fun _ ↦ rfl⟩
      · refine ⟨1, fun _ ↦ rfl, fun _ ↦ ⟨by rw [δ.dpow_one hμJ, mul_one],
          GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ 1⟩, fun h ↦ ?_⟩
        nlinarith
    · obtain ⟨a, c, hc, rfl⟩ : ∃ a c, c < p ∧ a * p + c = m :=
        ⟨m / p, m % p, Nat.mod_lt _ hp.pos, Nat.div_add_mod' m p⟩
      obtain ⟨v, hv⟩ := exists_inv hp hnil (not_dvd_coeff hp a c hc)
      have hco := coeff_mul_dpow δ hp hμJ hwJ hw a c
      obtain ⟨k, hk⟩ : ∃ k, a + c = k + 1 := by
        refine ⟨a + c - 1, ?_⟩
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [zero_mul, zero_add] at h ⊢
          omega
        · omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      refine ⟨v * (μ ^ k * δ.dpow a w), fun h1 ↦ by omega, fun _ ↦ ⟨?_, ?_⟩, fun hM ↦ ?_⟩
      · calc δ.dpow (a * (q + 1) + c) μ
            = (v * ((Nat.uniformBell a (q + 1) * (a * (q + 1) + c).choose (a * (q + 1)) *
                c.factorial : ℕ) : B)) * δ.dpow (a * (q + 1) + c) μ := by rw [hv, one_mul]
          _ = v * (μ ^ (a + c) * δ.dpow a w) := by rw [mul_assoc, hco]
          _ = μ * (v * (μ ^ k * δ.dpow a w)) := by rw [hk, pow_succ]; ring
      · have h5 := GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ
          (GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hμJ) k)
          (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hp1 hwf a)
        have e : a * (q + 1) + c - 1 = k * 1 + a * (q + 1 - 1) := by
          rw [Nat.add_sub_cancel, Nat.mul_succ]
          omega
        rw [e]
        exact Ideal.mul_mem_left _ _ h5
      · have h6 : n + 2 ≤ a := by
          by_contra hlt
          have h7 : a + 1 ≤ n + 2 := by omega
          have h8 := Nat.mul_le_mul_left (q + 1) h7
          nlinarith
        have h9 : μ ^ k = 0 := pow_eq_zero_of_le (by omega : n ≤ k) (hn μ hμJ)
        simp [h9]
  choose ν h1 h2 h3 using key
  refine ⟨⟨n, hn _ hμJ⟩, ν, h1 1 rfl, fun m ↦ (h2 (m + 1) (by omega)).1, fun m ↦ ?_, fun m hm ↦ ?_,
    p * (n + 2), fun m hm ↦ h3 m hm⟩
  · have h := (h2 (m + 1) (by omega)).2
    rw [Nat.add_sub_cancel] at h
    exact h
  · exact ⟨n, hn _ (GlobalTheory.Cris.ExpBij.dpFil_le δ (show 1 ≤ m - 1 by omega) (h2 m (by omega)).2)⟩

end GlobalTheory.CompanionTheory.QPd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansionStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.cyclotomic_divided_power_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | exact GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | (intros; apply GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapMemExt

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDAcyc

variable {B : Type} [CommRing B] {J : Ideal B}

theorem le_fil_one (δ : DividedPowers J) : J ≤ fil δ 1 := by
  intro j hj
  refine Ideal.subset_span ⟨[(1, j)], by simpa using hj, by simp, by simp [δ.dpow_one hj]⟩

theorem algebraMap_mem_ext (Q : PDPoly B) {j : B} (hj : j ∈ J) :
    algebraMap B Q.P j ∈ Q.ext J :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj)

theorem e_one_mem_ext (Q : PDPoly B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem map_e {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {μ q : B} (hμ : μ ∈ J) (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P μ + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) = ∑ j ∈ Finset.range (k + 1), (δ.dpow j μ * q ^ (k - j)) • Q.e (k - j) := by
  have he1 : Q.e 1 ∈ Q.ext J := e_one_mem_ext Q
  have hm : algebraMap B Q.P μ ∈ Q.ext J := algebraMap_mem_ext Q hμ
  have hq : algebraMap B Q.P q * Q.e 1 ∈ Q.ext J := Ideal.mul_mem_left _ _ he1
  have h0 : g (Q.e k) = η.dpow k (g (Q.e 1)) := by
    rw [hgd.dpow_comp _ he1, hS.var]
  rw [h0, h1, η.dpow_add hm hq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ η.dpow a (algebraMap B Q.P μ) * η.dpow b (algebraMap B Q.P q * Q.e 1))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [η.dpow_mul he1, hS.var, hS.dp.dpow_comp _ hμ, Algebra.smul_def, map_mul, map_pow]
  ring

noncomputable def qDer (Q : PDPoly B) (q : B) (ν : ℕ → B) : Q.P →ₗ[B] Q.P :=
  Q.e.constr B fun k ↦ (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
    ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1))

theorem qDer_e (Q : PDPoly B) (q : B) (ν : ℕ → B) (k : ℕ) :
    qDer Q q ν (Q.e k) = (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1)) := by
  simp only [qDer, Module.Basis.constr_basis]

theorem map_e_sub {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) - Q.e k = (q - 1) • qDer Q q ν (Q.e k) := by
  rw [map_e hS hμ g hgd h1, qDer_e, Finset.sum_range_succ', δ.dpow_zero hμ, smul_add,
    smul_smul, mul_geom_sum, Finset.smul_sum]
  simp only [hν, smul_smul, mul_assoc, Nat.sub_zero, one_mul, sub_smul, one_smul]
  abel

theorem map_sub_self {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgB : g.comp (algebraMap B Q.P) = algebraMap B Q.P)
    (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (z : Q.P) :
    g z - z = (q - 1) • qDer Q q ν z := by
  have hsm : ∀ (b : B) (w : Q.P), g (b • w) = b • g w := fun b w ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * g w) (RingHom.congr_fun hgB b)
  let gl : Q.P →ₗ[B] Q.P :=
    { toFun := g, map_add' := map_add g, map_smul' := fun b w ↦ by simpa using hsm b w }
  have key : gl - LinearMap.id = (q - 1) • qDer Q q ν :=
    Q.e.ext fun k ↦ by simpa [gl] using map_e_sub hS hμ hν g hgd h1 k
  simpa [gl] using LinearMap.congr_fun key z

theorem main : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B)
    (η : DividedPowers (Q.ext J)), Q.IsStd δ η → ∀ (p : ℕ), p.Prime → IsNilpotent (p : B) →
    ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → ∀ g : Q.P →+* Q.P,
    g.comp (algebraMap B Q.P) = algebraMap B Q.P → IsDPMorphism η η g →
    g (1 + Q.e 1) = algebraMap B Q.P (x ^ p) * (1 + Q.e 1) →
    Function.Injective (algebraMap B Q.P) ∧
    (∀ r, ∀ z ∈ fil η r, g z = z → ∃ m ∈ fil δ (r + 1),
      algebraMap B Q.P m = algebraMap B Q.P (x ^ p - 1) * z) ∧
    ∀ r, ∀ z ∈ fil η r, ∃ y ∈ fil η (r + 1), g y - y = algebraMap B Q.P (x ^ p - 1) * z := by
  intro B _ J δ Q η hS p hp hpn x hx g hgB hgd hg1
  have hrepr : ∀ b : B, Q.e.repr (algebraMap B Q.P b) 0 = b := fun b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, ← Q.e_zero, map_smul]
    simp
  have hμ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hx
  obtain ⟨hqn, ν, hν1, hνd, hνf, hνn, hνz⟩ := GlobalTheory.T.cyclotomic_divided_power_expansion δ p hp hpn x hx
  obtain ⟨hfm, hfa, -, hfr⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ Q η hS
  have h1 : g (Q.e 1) = algebraMap B Q.P (x ^ p - 1) + algebraMap B Q.P (x ^ p) * Q.e 1 := by
    have := hg1
    rw [map_add (f := _), map_one, mul_add, mul_one, add_comm (1 : Q.P)] at this
    rw [_root_.map_sub, map_one (algebraMap B Q.P)]
    linear_combination this
  have hg := map_sub_self hS hμ hνd g hgB hgd h1
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.connection_on_divided_power_basis Q.e (fil δ) p (x ^ p) ν (qDer Q (x ^ p) ν) hp.ne_zero hpn
    hqn hfm hfa hν1 hνf hνn hνz (qDer_e Q (x ^ p) ν)
  refine ⟨fun a b hab ↦ by rw [← hrepr a, hab, hrepr], ?_, ?_⟩
  · intro r z hz hgz
    have hD : qDer Q (x ^ p) ν ((x ^ p - 1) • z) = 0 := by
      rw [map_smul, ← hg, hgz, sub_self]
    obtain ⟨c, hc⟩ := hker _ hD
    have hc' : algebraMap B Q.P c = algebraMap B Q.P (x ^ p - 1) * z := by
      rw [← Algebra.smul_def, hc, Q.e_zero, Algebra.algebraMap_eq_smul_one]
    refine ⟨c, ?_, hc'⟩
    have hc0 : c = (x ^ p - 1) * Q.e.repr z 0 := by
      have := hrepr c
      rw [hc', ← Algebra.smul_def, map_smul] at this
      simpa using this.symm
    rw [hc0, add_comm]
    have hz0 : Q.e.repr z 0 ∈ fil δ r := by simpa using (hfr r z).1 hz 0
    exact hfm 1 r (Ideal.mul_mem_mul (le_fil_one δ hμ) hz0)
  · intro r z hz
    obtain ⟨y, hy, hDy⟩ := hsurj r z ((hfr r z).1 hz)
    refine ⟨y, (hfr (r + 1) y).2 hy, ?_⟩
    rw [hg, hDy, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDAcyc
end
end
