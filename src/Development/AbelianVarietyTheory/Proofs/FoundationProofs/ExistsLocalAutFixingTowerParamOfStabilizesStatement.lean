module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwise
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletedLaurentQuotPrimeEquivLaurentFp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependent
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicCompleteStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvrStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence

section

@[expose] public section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem aeval_qq_pow_sub_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) → v (p : Ωl) < 1 → ∀ (T : Tower p Ωl) (n : ℕ) (f : (O0 p)[X]), f.natDegree < p ^ n → v (aeval (T.qq n) f ^ (p ^ n) - algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i)) < 1 := by
  intro p hp Ωl _ _ _ v hv hvp T n f hf
  classical
  have hpr : p.Prime := hp.out
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hpr.pos n) (by rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : ℕ → integralClosure (O0 p) Ωl := fun i =>
    ⟨algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i, isIntegral_algebraMap.mul (hq.pow i)⟩
  have key : ∀ s : Finset ℕ, ∃ r : integralClosure (O0 p) Ωl,
      (∑ i ∈ s, t i) ^ p ^ n = ∑ i ∈ s, t i ^ p ^ n + p * r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hpr.ne_zero)]⟩
    | insert a s ha ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hpr (t a) (∑ i ∈ s, t i) n
      exact ⟨r + t a * (∑ i ∈ s, t i) * r', by rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]; ring⟩
  obtain ⟨r, hr⟩ := key (Finset.range (p ^ n))
  have term : ∀ i, ((t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) =
      algebraMap (O0 p) Ωl (f.coeff i ^ p ^ n * qO p ^ i) := by
    intro i
    rw [SubmonoidClass.coe_pow, map_mul, map_pow, map_pow]
    show (algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i) ^ p ^ n = _
    rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, GlobalTheory.K5.Basic.qq_pow]
  have e1 : aeval (T.qq n) f = ((∑ i ∈ Finset.range (p ^ n), t i : integralClosure (O0 p) Ωl) : Ωl) := by
    rw [aeval_eq_sum_range' hf]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
  have e2 : algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) =
      ((∑ i ∈ Finset.range (p ^ n), t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) := by

    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => (term i).symm
  have e3 : aeval (T.qq n) f ^ p ^ n - algebraMap (O0 p) Ωl
      (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) = (p : Ωl) * (r : Ωl) := by
    rw [e1, e2, ← SubmonoidClass.coe_pow, hr]
    push_cast
    ring
  rw [e3, map_mul]
  have hr1 : v (r : Ωl) ≤ 1 := (hv _).2 r.2
  calc v (p : Ωl) * v (r : Ωl) ≤ v (p : Ωl) * 1 := by gcongr
    _ = v (p : Ωl) := mul_one _
    _ < 1 := hvp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant

section

@[expose] public section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem addVal_eq_zero_of_root_sub_const {k K : Type} [Field k] [Field K] (φ : k →+* K)
    (v : AddValuation K (WithTop ℤ)) (hv : ∀ a : k, a ≠ 0 → v (φ a) = 0) (f : K) (P : k[X])
    (hP : P ≠ 0) (hf : eval₂ φ f P = 0) (c : k) (h : f - φ c ≠ 0) : v (f - φ c) = 0 := by
  letI : Algebra k K := φ.toAlgebra
  have h1 : IsAlgebraic k f := ⟨P, hP, hf⟩
  have h2 : IsAlgebraic k (f - φ c) := h1.sub (isAlgebraic_algebraMap c)
  haveI : Valuation.IsTrivialOn k (AddValuation.toValuation v) := ⟨fun a ha => hv a ha⟩
  by_contra hne
  exact Valuation.transcendental_of_ne_one k (v := AddValuation.toValuation v) _ h hne h2

theorem laurentSeries_eq_C_of_root : ∀ (k : Type) [Field k] (f : LaurentSeries k),
    (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  rintro k _ f ⟨P, hP, hf⟩
  refine ⟨f.coeff 0, ?_⟩
  by_contra hne
  have h : f - HahnSeries.C (f.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have h0 := addVal_eq_zero_of_root_sub_const (K := LaurentSeries k) HahnSeries.C
    (HahnSeries.addVal ℤ k) (fun a ha => by
      rw [HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero ha), HahnSeries.order_C]; rfl)
    f P hP hf _ h
  rw [HahnSeries.addVal_apply] at h0
  have h1 := HahnSeries.coeff_orderTop_ne (g := 0) h0
  apply h1
  simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizes

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Glue.CuspUp

open GlobalTheory.K5 GlobalTheory.KZ Polynomial
open scoped NNReal

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
  {v : Valuation Ωl ℝ≥0}

theorem v_alg_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (b : O0 p) : v (algebraMap (O0 p) Ωl b) ≤ 1 :=
  (hv _).2 isIntegral_algebraMap

theorem v_alg_lt_iff (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1) (b : O0 p) :
    v (algebraMap (O0 p) Ωl b) < 1 ↔ (p : O0 p) ∣ b := by
  obtain ⟨_, hd, hirr⟩ := completed_laurent_isDVR p
  constructor
  · intro hb
    rw [← Ideal.mem_span_singleton, ← hirr.maximalIdeal_eq]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h2 : v (algebraMap (O0 p) Ωl b) * v (algebraMap (O0 p) Ωl c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le hb (v_alg_le hv c)).ne
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_mul, map_natCast]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (v_alg_le hv c)

theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ ∀ b, φ b = 0 ↔ (p : O0 p) ∣ b := by
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk _), he, fun b => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  exact e.map_eq_zero_iff

theorem isInt_qq (T : K5.Tower p Ωl) (n : ℕ) : IsIntegral (O0 p) (T.qq n) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos n) ?_
  rw [Basic.qq_pow]
  exact isIntegral_algebraMap

theorem v_aeval_le (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) :
    v (aeval (T.qq n) f) ≤ 1 :=
  (hv _).2 (IsIntegral.of_mem_of_fg _ (isInt_qq T n).fg_adjoin_singleton _
    (aeval_mem_adjoin_singleton _ _))

theorem orth (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (hlt : v (aeval (T.qq n) f) < 1) : C (p : O0 p) ∣ f := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have h3 : v (aeval (T.qq n) f ^ (p ^ n)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le hlt (pow_pos hp.out.pos n).ne'
  have h4 := v.map_sub_lt h3 h2
  rw [sub_sub_cancel, v_alg_lt_iff hv h1, ← hφ] at h4
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, hq] at h4
  have h5 := GlobalTheory.laurent_pow_indep_over_prime_pow_powers p n (fun i => φ (f.coeff i)) h4
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i < p ^ n
  · exact (hφ _).1 (h5 i hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _

theorem res (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (f : (O0 p)[X]) (hf : f.natDegree < p ^ n)
    (halg : IsAlgebraic ℤ (aeval (T.qq n) f)) : ∃ m : ℤ, v (aeval (T.qq n) f - m) < 1 := by
  obtain ⟨φ, hq, hφ⟩ := exists_red (p := p)
  have h2 := GlobalTheory.aeval_qq_pow_sub_lt_one p Ωl h v hv h1 T n f hf
  have hy := v_aeval_le hv T n f
  set y := aeval (T.qq n) f
  set b := ∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i
  have hroot : ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
    haveI : CharZero Ωl := Basic.charZero_of_isClo h
    let z := y ^ p ^ n
    obtain ⟨Q, hQ, hQz⟩ := halg.pow (p ^ n)
    let P := Q.primPart
    have hPz : aeval z P = 0 := by
      have hc : Q.content ≠ 0 := fun hc => hQ (Polynomial.content_eq_zero_iff.mp hc)
      rw [Q.eq_C_content_mul_primPart, map_mul, aeval_C] at hQz
      exact (mul_eq_zero.mp hQz).resolve_left (by simpa using hc)
    refine ⟨P, ?_, (v_alg_lt_iff hv h1 _).1 ?_⟩
    · intro hP
      have hd : ∀ i, (p : ℤ) ∣ P.coeff i := by
        intro i
        have hi := congrArg (fun R => R.coeff i) hP
        simp only [coeff_map, coeff_zero, eq_intCast] at hi
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi
      have hu := (Polynomial.isPrimitive_primPart Q) (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 hd)
      have := Int.isUnit_iff.1 hu
      have := hp.out.two_le
      omega
    · let b' := algebraMap (O0 p) Ωl b
      have hz : v z ≤ 1 := by
        dsimp [z]
        rw [map_pow]
        exact pow_le_one₀ zero_le hy
      let zi : v.integer := ⟨z, hz⟩
      let bi : v.integer := ⟨b', v_alg_le hv b⟩
      obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub zi bi (P.map (Int.castRingHom v.integer))
      have hev (w : v.integer) :
          v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval w) = aeval (w : Ωl) P := by
        rw [Polynomial.eval_map, aeval_def]
        have hw := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype w
        rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from
          RingHom.ext_int _ _] at hw
        exact hw
      have hd' := congrArg v.integer.subtype hd
      rw [map_sub, map_mul, map_sub, hev, hev] at hd'
      change aeval z P - aeval b' P = (z - b') * (d : Ωl) at hd'
      rw [hPz, zero_sub, neg_eq_iff_eq_neg] at hd'
      have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
        rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
        congr 1
        exact RingHom.ext_int _ _
      rw [hmap, hd', Valuation.map_neg, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 d.2
  obtain ⟨P, hP0, hP⟩ := hroot
  obtain ⟨c, hc⟩ := GlobalTheory.laurentSeries_eq_C_of_root (ZMod p) (φ b) ⟨_, hP0, by
    rw [← (hφ _).2 hP, eval₂_map, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨m, ?_⟩
  have h3 : v (algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n)) < 1 := by
    let C' : ZMod p →+* LaurentSeries (ZMod p) := HahnSeries.C
    change φ b = C' (m : ZMod p) at hc
    rw [v_alg_lt_iff hv h1, ← hφ, φ.map_sub, hc, φ.map_pow, map_intCast φ,
      ← map_intCast C', ← C'.map_pow, ZMod.pow_card_pow, sub_self]
  have hm : v (m : Ωl) ≤ 1 := (hv _).2 (Basic.isInt_intCast m)
  let y' : v.integer := ⟨y - m, v.map_sub_le hy hm⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out y' (m : v.integer) n
  have hr' := congrArg (Subtype.val) hr
  simp only [y'] at hr'
  push_cast at hr'
  have h4 : v ((p : Ωl) * (y - m) * m * r) < 1 := by
    rw [mul_assoc, mul_assoc, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (y' * ((m : v.integer) * r)).2
  have h5 := v.map_sub_lt (v.map_add_lt h2 h3) h4
  have h6 : y ^ p ^ n - algebraMap (O0 p) Ωl b + algebraMap (O0 p) Ωl (b - (m : O0 p) ^ p ^ n) -
      (p : Ωl) * (y - m) * m * r = (y - m) ^ p ^ n := by
    rw [map_sub, map_pow, map_intCast]
    rw [sub_add_cancel] at hr'
    linear_combination hr'
  rw [h6, map_pow] at h5
  exact lt_of_pow_lt_pow_left₀ (p ^ n) zero_le_one (by rwa [one_pow])

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem approx (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (N : ℕ) : ∀ (f : (O0 p)[X]) (a : Ω), f.natDegree < p ^ n → aeval (T.qq n) f = j a →
      v (j (s a - a)) ≤ v (p : Ωl) ^ N := by
  haveI := Basic.charZero_of_isClo h
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction N with
  | zero =>
    intro f a _ ha
    have h2 := v_aeval_le hv T n f
    rw [ha] at h2
    rw [map_sub, pow_zero]
    exact v.map_sub_le (hs a h2) h2
  | succ N ih =>
    intro f a hf ha
    have halg : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm⟩ := res h hv h1 T n f hf (ha ▸ halg.algHom j.toIntAlgHom)
    have hf' : (f - C (m : O0 p)).natDegree < p ^ n := by rwa [natDegree_sub_C]
    obtain ⟨g, hg⟩ := orth h hv h1 T n _ hf' (by simpa using hm)
    have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpl : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpO : (p : O0 p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := ih g ((a - m) / p) (by rwa [hg, natDegree_C_mul hpO] at hf') (by
      have := congrArg (aeval (T.qq n)) hg
      simp only [map_sub, map_mul, aeval_C, map_intCast, map_natCast, ha] at this
      rw [map_div₀, map_sub, map_intCast, map_natCast, this, mul_div_cancel_left₀ _ hpl])
    have h4 : s a - a = p * (s ((a - m) / p) - (a - m) / p) := by
      rw [map_div₀, map_sub, map_intCast, map_natCast]; field_simp; ring
    rw [h4, map_mul, map_mul, map_natCast, pow_succ']
    exact mul_le_mul_right h3 _

theorem fixed (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1)
    (f : (O0 p)[X]) (d : O0 p) (hd : d ≠ 0) (a : Ω)
    (ha : aeval (T.qq n) f = algebraMap (O0 p) Ωl d * j a) : s a = a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨_, hdv, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hirr
  have hpos := pow_pos hp.out.pos n
  have hmon : (X ^ (p ^ n) - C (qO p)).Monic := monic_X_pow_sub_C _ hpos.ne'
  have hdeg : ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))).natDegree < p ^ n := by
    have := natDegree_modByMonic_lt (C (↑u⁻¹ : O0 p) * f) hmon (fun h0 => by
      have := congrArg natDegree h0
      rw [natDegree_X_pow_sub_C _, natDegree_one] at this
      omega)
    rwa [natDegree_X_pow_sub_C _] at this
  have hev : aeval (T.qq n) ((C (↑u⁻¹ : O0 p) * f) %ₘ (X ^ (p ^ n) - C (qO p))) = j ((p : Ω) ^ m * a) := by
    rw [aeval_modByMonic_eq_self_of_root (by simp [Basic.qq_pow]), map_mul, aeval_C, ha, ← mul_assoc,
      ← map_mul, Units.inv_mul_cancel_left]
    simp
  have h0 : v (j (s ((p : Ω) ^ m * a) - (p : Ω) ^ m * a)) = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.2 hne) h1
    exact absurd (approx h hv h1 T n j s hs N _ _ hdeg hev) (not_le.2 hN)
  rw [v.zero_iff, map_eq_zero, sub_eq_zero, map_mul, map_pow, map_natCast] at h0
  exact mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero)) h0

theorem up (h : IsClo p Ωl) (hv : ∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) (h1 : v (p : Ωl) < 1)
    (T : K5.Tower p Ωl) (n : ℕ) (j : Ω →+* Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x, v (j x) ≤ 1 → v (j (s x)) ≤ 1) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  haveI := h.clo
  haveI := h.alg
  haveI := Basic.charZero_of_isClo h
  haveI : FaithfulSMul (O0 p) Ωl := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
  letI : Algebra (FractionRing (O0 p)) Ωl := FractionRing.liftAlgebra (O0 p) Ωl
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ωl := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ωl :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O0 p) (K := FractionRing (O0 p))).1 h.alg
  let K := IntermediateField.adjoin (FractionRing (O0 p)) {T.qq n}
  have hfix : ∀ a : Ω, j a ∈ Set.range (algebraMap K Ωl) → s a = a := by
    rintro a ⟨⟨y, hy⟩, rfl : y = j a⟩
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, hf⟩ := hy
    obtain ⟨d, hd, hdf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (O0 p)) f
    refine fixed h hv h1 T n j s hs
      (IsLocalization.integerNormalization (nonZeroDivisors (O0 p)) f) d (nonZeroDivisors.ne_zero hd) a ?_
    rw [← aeval_map_algebraMap (FractionRing (O0 p)), hdf, ← Algebra.smul_def, ← hf,
      ← algebraMap_smul (FractionRing (O0 p)) d f, map_smul, algebraMap_smul]
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.exists_algEquiv_inducing_of_forall_conj Ω Ωl K j s (GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base Ω Ωl K j s hfix)
  refine ⟨(g.restrictScalars (FractionRing (O0 p))).restrictScalars (O0 p), ?_, hg⟩
  exact g.commutes ⟨T.qq n, IntermediateField.mem_adjoin_simple_self _ _⟩

end Local

theorem exists_gal_fix_qq_of_stab {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (h : IsClo p Ωl) (j : Ω →+* Ωl)
    (hA : ∀ x, x ∈ A ↔ IsInt (p := p) (j x)) (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (hs : Stab A s) :
    ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hirr.maximalIdeal_eq]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  haveI := h.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ωl h.inj
  have h1 : v (p : Ωl) < 1 := by
    haveI := Basic.charZero_of_isClo h
    have hle : v (p : Ωl) ≤ 1 := by
      rw [← map_natCast (algebraMap (O0 p) Ωl)]
      exact (hv _).2 isIntegral_algebraMap
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact Basic.not_cong_one_zero h 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  exact up h hv h1 T n j s fun x hx => (hv _).2 ((hA _).1 ((hs x).2 ((hA _).2 ((hv _).1 hx))))

end GlobalTheory.Glue.CuspUp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizesStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ GlobalTheory.K5.IsInt (p := p) (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | exact GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | (intros; apply GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab <;> assumption)
end
end
