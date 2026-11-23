module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDenominatorOfLattice
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
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
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormDenEqOneOnLattice
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsLatticeLiftCongrModCoprime
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPrimeToPMultipleInRangeOfBilinForm
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.FiniteFreeOfBoundedDenominatorsLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.LatticeSaturatedAtPAndPrimeToP
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDivOfREqSmulCompletedLattice

section

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_div_of_r_eq_smul_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (w : VQ D) (n : ℕ) (e : AfP p ⊗[ℚ] VQ D), w ∈ X.lat → 0 < n → n.Coprime p → e ∈ LaHat D → X.r w = n • e → ∃ u ∈ X.lat, w = n • u := by
  intro p _ D X w n e hw hn hc he hr
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hwu : w = n • ((n : ℚ)⁻¹ • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hru : X.r ((n : ℚ)⁻¹ • w) = e := by
    rw [map_smul, hr, ← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨(n : ℚ)⁻¹ • w, ⟨(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 n _ hc ?_, ?_⟩, hwu⟩
  · rw [← hwu]; exact hw.1
  · rw [hru]; exact he
end
end

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsIntBilinFormOfScaledForm

section

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_int_bilinForm_of_scaled_form :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D),
      ∃ E : LinearMap.BilinForm ℤ X.lat,
        ∀ u w : X.lat, (E u w : ℚ) = X.s * X.B (u : VQ D) (w : VQ D) := by
  intro p _ D X
  have h : ∀ u w : X.lat, ((X.s * X.B (u : VQ D) (w : VQ D)).num : ℚ)
      = X.s * X.B (u : VQ D) (w : VQ D) := fun u w =>
    Rat.intCast_num_of_den_eq_one (UpperTheory.scaled_form_den_eq_one_on_lattice p D X u w u.2 w.2)
  refine ⟨LinearMap.mk₂ ℤ (fun u w : X.lat => (X.s * X.B (u : VQ D) (w : VQ D)).num)
    ?_ ?_ ?_ ?_, ?_⟩
  · intro u u' w
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add X.B, LinearMap.add_apply, mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower X.B, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  · intro u w w'
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add (X.B (u : VQ D)), mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower (X.B (u : VQ D)), zsmul_eq_mul]
    ring
  · intro u w
    rw [LinearMap.mk₂_apply]
    exact h u w
end
end

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.IntegralUnitCongrCoprimeIntMod

section

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.integral_unit_congr_coprime_int_mod :
    ∀ (p : ℕ) [Fact p.Prime] (ε : (AfP p)ˣ), IsIntAf (ε : AfP p) → IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p) → ∀ n : ℕ, 0 < n → n.Coprime p → ∃ (ν : ℤ) (b : AfP p), IsIntAf b ∧ (ε : AfP p) = (ν : AfP p) + (n : AfP p) * b ∧ IsCoprime ν (n : ℤ) := by
  intro p _ ε hε hε' n hn hnp
  obtain ⟨ν, b, hb, hνb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε
  obtain ⟨μ, b', hb', hμb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε'
  refine ⟨ν, b, hb, hνb, ?_⟩
  have hint : IsIntAf ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    intro v
    simp only [map_add (f := _), map_mul, map_intCast, map_natCast]
    exact add_mem (add_mem (mul_mem (intCast_mem _ ν) (hb' v)) (mul_mem (intCast_mem _ μ) (hb v)))
      (mul_mem (mul_mem (natCast_mem _ n) (hb v)) (hb' v))
  have hprod : (1 : AfP p) = (ν : AfP p) * μ +
      n * ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    have : (ε : AfP p) * ((ε⁻¹ : (AfP p)ˣ) : AfP p) = 1 := Units.mul_inv ε
    rw [← this, hνb, hμb]
    ring
  have hdvd : (n : ℤ) ∣ 1 - ν * μ := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ _ hint
    rw [map_intCast, Int.cast_sub, Int.cast_one, Int.cast_mul]
    linear_combination hprod
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨μ, k, by linear_combination -hk⟩
end
end

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormCongrModNOfUnitCongr

section

@[expose] public section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.scaled_form_congr_mod_n_of_unit_congr :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ) (ν : ℤ) (b : AfP p) (u u' : VQ D) (a a' : D.La) (e e' : AfP p ⊗[ℚ] VQ D), 0 < n → n.Coprime p → IsIntAf b → (X.ε : AfP p) = (ν : AfP p) + (n : AfP p) * b → u ∈ X.lat → u' ∈ X.lat → e ∈ LaHat D → e' ∈ LaHat D → X.r u = inAf D a + n • e → X.r u' = inAf D a' + n • e' → ∃ z : ℤ, X.s * X.B u u' = (ν : ℚ) * (D.EF a a' : ℤ) + (n : ℚ) * z := by
  intro p _ D X n ν b u u' a a' e e' hn hc hb hε hu hu' he he' hr hr'
  have hden := UpperTheory.scaled_form_den_eq_one_on_lattice p D X u u' hu hu'
  have hform : algebraMap ℚ (AfP p) (X.s * X.B u u') =
      (X.ε : AfP p) * MultScale.EFA D (X.r u) (X.r u') := X.form u u'
  generalize X.s * X.B u u' = q at hden hform ⊢
  have hqz : ((q.num : ℤ) : ℚ) = q := Rat.coe_int_num_of_den_eq_one hden
  have ha := MultScale.inAf_mem D a
  have ha' := MultScale.inAf_mem D a'
  obtain ⟨y, hy, hexp⟩ : ∃ y : AfP p, IsIntAf y ∧
      MultScale.EFA D (inAf D a + n • e) (inAf D a' + n • e') =
        ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y := by
    refine ⟨MultScale.EFA D (inAf D a) e' + MultScale.EFA D e (inAf D a') +
      (n : AfP p) * MultScale.EFA D e e', ?_, ?_⟩
    · exact MultScale.isIntAf_add (MultScale.isIntAf_add (MultScale.isIntAf_EFA D ha he')
        (MultScale.isIntAf_EFA D he ha')) (MultScale.isIntAf_mul
          (by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)) (MultScale.isIntAf_EFA D he he'))
    · simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
        MultScale.EFA_inAf]
      ring
  rw [hr, hr', hexp, hε] at hform
  have hE := MultScale.isIntAf_intCast (p := p) (D.EF a a')
  have hN : IsIntAf (n : AfP p) := by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)
  have hy' : IsIntAf ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) :=
    MultScale.isIntAf_add (MultScale.isIntAf_mul (MultScale.isIntAf_intCast ν) hy)
      (MultScale.isIntAf_mul hb (MultScale.isIntAf_add hE (MultScale.isIntAf_mul hN hy)))
  have hc' : algebraMap ℚ (AfP p) (((q.num - ν * (D.EF a a' : ℤ) : ℤ)) : ℚ) =
      (n : AfP p) * ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) := by
    have h1 : algebraMap ℚ (AfP p) ((q.num : ℤ) : ℚ) = algebraMap ℚ (AfP p) q := by rw [hqz]
    rw [map_intCast] at h1 ⊢
    push_cast
    rw [h1, hform]
    ring
  obtain ⟨k, hk⟩ := IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _ _ hy' hc'
  refine ⟨k, ?_⟩
  have hk' : ((q.num : ℤ) : ℚ) - (ν : ℚ) * (D.EF a a' : ℤ) = (n : ℚ) * k := by exact_mod_cast hk
  rw [← hqz]
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitMain

section

@[expose] public section

noncomputable section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Wit.Sys

variable {p : ℕ} [Fact p.Prime] {D : Datum p} (X : Sys D)

theorem r_nsmul (n : ℕ) (w : VQ D) :
    X.r (n • w) = n • (X.r w : AfP p ⊗[ℚ] VQ D) := map_nsmul X.r n w

theorem eq_add {n : ℕ} (hn : 0 < n) (hnp : n.Coprime p) (u v : X.lat) {e : AfP p ⊗[ℚ] VQ D} (he : e ∈ LaHat D)
    (h : X.r (u : VQ D) = X.r (v : VQ D) + n • e) : ∃ e' : X.lat, u = v + n • e' := by
  have hw : (u : VQ D) - v ∈ X.lat := sub_mem u.2 v.2
  have hr : X.r ((u : VQ D) - v) = n • e := by rw [map_sub, h]; abel
  obtain ⟨y, hy, ey⟩ := UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X _ n e hw hn hnp he hr
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  show (u : VQ D) = v + n • y
  rw [← ey]; abel

def plat (hfin : Module.Finite ℤ X.lat) (hfree : Module.Free ℤ X.lat) (E : LinearMap.BilinForm ℤ X.lat)
    (hE : ∀ u w : X.lat, ((E u w : ℤ) : ℚ) = X.s * X.B (u : VQ D) (w : VQ D)) : PLat D.O D.inv where
  La := X.lat
  fin := hfin
  free := hfree
  EF := (2 : ℤ) • E
  alt x := by
    have h : ((E x x : ℤ) : ℚ) = 0 := by rw [hE, X.alt, mul_zero]
    have h' : E x x = 0 := by exact_mod_cast h
    simp [h']
  nondeg x h := by
    have hs : X.s ≠ 0 := X.s_pos.ne'
    have hB : ∀ w, X.B (x : VQ D) w = 0 := by
      intro w
      obtain ⟨m, hm, hw⟩ := (UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X).2.2 w
      have h1 := h ⟨m • w, hw⟩
      have h2 : E x ⟨m • w, hw⟩ = 0 := by
        simpa using h1
      have h3 := hE x ⟨m • w, hw⟩
      rw [h2, map_nsmul] at h3
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
      simp only [Int.cast_zero, nsmul_eq_mul] at h3
      have := mul_eq_zero.1 h3.symm
      rcases this with h4 | h4
      · exact absurd h4 hs
      · exact (mul_eq_zero.1 h4).resolve_left hm'
    exact Subtype.ext (X.nondeg _ hB)
  adj a x y := by
    have h : ((E (a • x) y : ℤ) : ℚ) = ((E x (D.inv a • y) : ℤ) : ℚ) := by
      rw [hE, hE, coe_smul, coe_smul, X.adj]
    have h' : E (a • x) y = E x (D.inv a • y) := by exact_mod_cast h
    simp [h']

theorem main (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (j : D'.La →+ VQ D), D.Cls N D' t ∧ Function.Injective j ∧
      (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) ∧ (∀ w, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u) ∧
      (∀ u u', (D'.EF u u' : ℚ) = (2 * X.s) * X.B (j u) (j u')) ∧
      (∀ w, (∃ (r : ℕ) (u : D'.La), p ^ r • w = j u) ↔ X.r w ∈ LaHat D) ∧
      (∀ a, ∃ w ∈ LaHat D, X.r (j (t a)) = inAf D a + N • w) ∧
      (∀ w, (∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u) ↔ w ∈ X.M) := by
  obtain ⟨hfin, hfree⟩ := UpperTheory.finite_free_of_bounded_denominators_lattice p D X (UpperTheory.exists_denominator_of_lattice p D X)
  obtain ⟨E, hE⟩ := UpperTheory.exists_int_bilinForm_of_scaled_form p D X
  obtain ⟨f, hf⟩ := UpperTheory.exists_lattice_lift_congr_mod_coprime p D X
  have hν := UpperTheory.integral_unit_congr_coprime_int_mod p X.ε X.ε_int X.ε_inv
  choose! ν b hν using hν
  obtain ⟨hp1, hp2, hp3⟩ := UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X
  have hEint : ∀ (n : ℕ), 0 < n → n.Coprime p → ∀ a a', ∃ z : ℤ,
      E (f n a) (f n a') = ν n * D.EF a a' + n * z := by
    intro n hn hnp a a'
    obtain ⟨e, he, re⟩ := hf n hn hnp a
    obtain ⟨e', he', re'⟩ := hf n hn hnp a'
    obtain ⟨hb, hεb, -⟩ := hν n hn hnp
    obtain ⟨z, hz⟩ := UpperTheory.scaled_form_congr_mod_n_of_unit_congr p D X n (ν n) (b n) _ _ a a' e e' hn hnp hb hεb (f n a).2 (f n a').2 he he' re re'
    refine ⟨z, ?_⟩
    have := (hE (f n a) (f n a')).trans hz
    exact_mod_cast this
  have c1 : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧
      ∀ a : D.La, ∃ e : X.lat, f (n * m) a = f n a + n • e := by
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnm
    have hnmp : 0 < n * m := Nat.mul_pos hn hm
    refine ⟨?_, fun a => ?_⟩
    · obtain ⟨hb, hεb, -⟩ := hν n hn hnp
      obtain ⟨hb', hεb', -⟩ := hν (n * m) hnmp hnm
      refine GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ (b n - m * b (n * m)) ?_ ?_
      · intro v
        rw [map_sub, map_mul, map_natCast]
        exact sub_mem (hb v) (mul_mem (natCast_mem _ m) (hb' v))
      · have e1 := hεb.symm.trans hεb'
        push_cast at e1 ⊢
        simp only [map_sub, map_intCast]
        linear_combination -e1
    · obtain ⟨e₁, he₁, r₁⟩ := hf (n * m) hnmp hnm a
      obtain ⟨e₂, he₂, r₂⟩ := hf n hn hnp a
      refine eq_add X hn hnp _ _ (e := m • e₁ - e₂) (sub_mem (nsmul_mem he₁ m) he₂) ?_
      rw [r₁, r₂, smul_sub, smul_smul]
      abel
  have c2 : ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧
      (∀ (c : D.O) (a : D.La), ∃ e : X.lat, f n (c • a) = c • f n a + n • e) ∧
      (∀ a : D.La, (∃ e : X.lat, f n a = n • e) ↔ ∃ e : D.La, a = n • e) ∧
      (∀ a' : X.lat, ∃ (a : D.La) (e : X.lat), a' = f n a + n • e) ∧
      ∀ a a' : D.La, (n : ℤ) ∣ ((2 : ℤ) • E) (f n a) (f n a') - ν n * ((2 : ℤ) • D.EF) a a' := by
    intro n hn hnp
    obtain ⟨hb, hεb, hcop⟩ := hν n hn hnp
    refine ⟨hcop, fun c a => ?_, fun a => ⟨?_, ?_⟩, fun a' => ?_, fun a a' => ?_⟩
    · obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp (c • a)
      obtain ⟨e₂, he₂, r₂⟩ := hf n hn hnp a
      refine eq_add X hn hnp (f n (c • a)) (c • f n a)
        (e := e₁ - (actQ D c).baseChange (AfP p) e₂) (sub_mem he₁ (GlobalTheory.AdelicSim.bc_mem D c he₂)) ?_
      rw [r₁, coe_smul, r_act, r₂, map_add (f := _), map_nsmul, GlobalTheory.AdelicSim.bc_inAf, smul_sub]
      abel
    · rintro ⟨e, he⟩
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp a
      have h1 : X.r (f n a : VQ D) = n • X.r (e : VQ D) := by
        rw [he, AddSubgroup.coe_nsmul, r_nsmul]
      refine GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf p D n hn hnp
        (GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp) a
        ⟨X.r (e : VQ D) - e₁, sub_mem e.2.2 he₁, ?_⟩
      rw [smul_sub, ← h1, r₁]; abel
    · rintro ⟨e, rfl⟩
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp (n • e)
      have h2 : inAf D (n • e) = n • inAf D e := GlobalTheory.AdelicSim.inAf_nsmul D n e
      obtain ⟨y, hy, ey⟩ := UpperTheory.exists_div_of_r_eq_smul_completedLattice p D X (f n (n • e) : VQ D) n (inAf D e + e₁) (f n (n • e)).2 hn hnp
        (add_mem (GlobalTheory.AdelicSim.inAf_mem D e) he₁) (by rw [r₁, h2, smul_add])
      exact ⟨⟨y, hy⟩, Subtype.ext ey⟩
    · obtain ⟨a, w, hw, ew⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ a'.2.2
      obtain ⟨e₁, he₁, r₁⟩ := hf n hn hnp a
      obtain ⟨e', he'⟩ := eq_add X hn hnp a' (f n a) (e := w - e₁) (sub_mem hw he₁) (by
        rw [ew, r₁, smul_sub]; abel)
      exact ⟨a, e', he'⟩
    · obtain ⟨z, hz⟩ := hEint n hn hnp a a'
      refine ⟨2 * z, ?_⟩
      simp only [LinearMap.smul_apply, hz, smul_eq_mul]
      ring
  let D' := X.plat hfin hfree E hE
  have hG : Genus p N D.plat D' (fun a => f N a) := ⟨f, ν, rfl, c1, c2⟩
  have hH : HalfPerf p D' := by
    obtain ⟨e, he, h⟩ := UpperTheory.exists_prime_to_p_multiple_in_range_of_bilinForm p D X E hE
    exact ⟨E, rfl, e, he, h⟩
  refine ⟨D', fun a => f N a, X.lat.subtype, ⟨hG, hH⟩, Subtype.val_injective, fun c u => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨m, hm, hw⟩ := hp3 w
    exact ⟨m, ⟨m • w, hw⟩, hm, rfl⟩
  · have h : ∀ u u' : X.lat, ((((2 : ℤ) • E) u u' : ℤ) : ℚ) = (2 * X.s) * X.B (u : VQ D) (u' : VQ D) := by
      intro u u'
      simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, hE]
      push_cast; ring
    exact h
  · intro w
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨r, u, hu⟩
      have h1 : p ^ r • X.r w ∈ LaHat D := by
        rw [← r_nsmul, hu]; exact Subtype.property (p := (· ∈ X.lat)) u |>.2
      have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ r)) := fun v => by
        rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv v) r
      have hm := DenEnd.smul_mem D hint h1
      have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      convert hm using 1
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [← mul_pow, inv_mul_cancel₀ hp, one_pow, one_smul]
    · obtain ⟨k, hk⟩ := hp1 w h
      exact ⟨k, ⟨p ^ k • w, hk⟩, rfl⟩
  · intro a
    obtain ⟨e, he, re⟩ := hf N hN hNp a
    exact ⟨e, he, re⟩
  · intro w
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨m, u, hm, hu⟩
      exact (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 m w hm (by rw [hu]; exact (Subtype.property (p := (· ∈ X.lat)) u).1)
    · obtain ⟨m, -, hm, hw⟩ := hp2 w h
      exact ⟨m, ⟨m • w, hw⟩, hm, rfl⟩

end UpperTheory.Gal.W2.Wit.Sys
end
end
end
