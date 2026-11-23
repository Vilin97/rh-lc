module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPow

section

@[expose] public section

theorem GlobalTheory.cauchy_product_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  intro R _ x α β A B hA hB r
  obtain ⟨NA, hNA⟩ := hA r
  obtain ⟨NB, hNB⟩ := hB r
  have hα : ∀ p ≥ NA, x ^ r ∣ α p := by
    intro p hp
    have h1 := hNA p hp
    have h2 := hNA (p + 1) (by omega)
    have e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]; exact dvd_sub h1 h2
  refine ⟨NA + NB, fun n hn => ?_⟩
  have key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q := by
    rw [Finset.sum_range_diag_flip n (fun p q => α p * β q)]
    simp only [Finset.mul_sum]
  have hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = (A - ∑ p ∈ Finset.range n, α p) * B
        + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q) := by
    rw [key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)
  by_cases hp' : NA ≤ p
  · exact dvd_mul_of_dvd_left (hα p hp') _
  · exact dvd_mul_of_dvd_right (hNB _ (by omega)) _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPowStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.cauchy_product_partial_sums_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  first | exact @GlobalTheory.cauchy_product_dvd_pow | exact GlobalTheory.cauchy_product_dvd_pow | (intros; apply GlobalTheory.cauchy_product_dvd_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPow

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative (R := K) (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add (f := _), hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι), C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  first | exact @GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | exact GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | (intros; apply GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivativeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧),
      descN (K := K) p f = X ^ p * (⇑(derivative (R := K)))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative, ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge h), Nat.cast_zero, zero_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibnizStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  intro O K _ _ _ _ _ l e a ι _ _ P C k f v
  let D (p : ℕ) (τ : ZMod a) := (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)
  have h (n : ℕ) : (C.nabla ^ n) (f • v) = ∑ p ∈ Finset.range (n + 1),
      n.choose p • (D p • (C.nabla ^ (n - p)) v) := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [Finset.sum_choose_succ_nsmul (fun i j => D i • (C.nabla ^ j) v) n,
        pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      rw [map_nsmul, C.leibniz, smul_add, add_comm]
      congr 2
      · rw [show n + 1 - p = n - p + 1 by omega, pow_succ', mul_apply_eq_comp]
      · congr 1
        funext τ
        exact (Function.iterate_succ_apply' _ _ _).symm
  rw [h k]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTaylorFormulaBreuilKisinLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TaylorBasis

theorem cauchy_dvd {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R)
    (hA : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p)
    (hB : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) :=
  GlobalTheory.T.cauchy_product_partial_sums_dvd_pow x α β A B hA hB r

theorem desc_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (v : Vec K a ι) : C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v :=
  GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' C k v

theorem nabla_pow_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) :=
  GlobalTheory.T.nabla_pow_apply_smul_leibniz C k f v

theorem descN_eq (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) :
    descN K p f = X ^ p * (⇑(derivative (R := K)))^[p] f :=
  GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' K p f

theorem muDiv_mul_choose {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {k p : ℕ} (h : p ≤ k) :
    ϖ.muDiv a O g k * (k.choose p : OCr l O) = ϖ.muDiv a O g p * ϖ.muDiv a O g (k - p) := by
  have hx := ϖ.theta_mu (ϖ.gal_pi a g)
  have key : dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) = dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p) := by
    apply sub_eq_zero.1
    refine acris_nat_cancel (Nat.factorial_ne_zero k) ?_
    have hf : (k.factorial : Per.Acris l) = (k.choose p : Per.Acris l) * p.factorial * (k - p).factorial := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
    rw [show (k.factorial : Per.Acris l) * (dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) -
        dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p)) = (k.choose p : Per.Acris l) * ((k.factorial : Per.Acris l) *
        dpow (ϖ.mu g) hx k) - (k.choose p : Per.Acris l) * (((p.factorial : Per.Acris l) * dpow (ϖ.mu g) hx p) *
        (((k - p).factorial : Per.Acris l) * dpow (ϖ.mu g) hx (k - p))) by
      linear_combination (-(dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p))) * hf]
    rw [factorial_mul_dpow, factorial_mul_dpow, factorial_mul_dpow, ← pow_add, Nat.add_sub_cancel' h, sub_self]
  have hm : ∀ n, ϖ.muDiv a O g n =
      (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) (dpow (ϖ.mu g) hx n) := fun n => rfl
  rw [hm, hm, hm, ← map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O), ← map_mul,
    ← map_mul, key]

theorem galOCr_iC_taylor {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) (c : ZMod a → S O K e) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ galOCr O (g : GQ l) (ϖ.iC t K c) -
      ∑ p ∈ Finset.range n, ϖ.muDiv a O g p * ϖ.iC t K (fun τ => ⟨descN K p (c τ), descN_mem_S e p (c τ).2⟩) := by
  choose N hN using fun τ : ZMod a => ϖ.taylor_S a O K g (c τ) r
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun τ => hN τ n ((Finset.le_sup (Finset.mem_univ τ)).trans hn)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩

  simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem coord_desc {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (m : Vec K a ι) (k : ℕ) (τ : ZMod a) (i : ι) :
    (P.mxInv τ *ᵥ C.desc k m τ) i = ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) *
      (descN K p ((P.mxInv τ *ᵥ m τ) j) * (X ^ (k - p) * (P.mxInv τ *ᵥ (C.nabla ^ (k - p)) (P.phi (bas j)) τ) i)) := by
  have hΦ : ∀ (f : ZMod a → K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (f • w) τ) i = f τ * (P.mxInv τ *ᵥ w τ) i := fun f w => by
    rw [Pi.smul_apply', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦs : ∀ (s : K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (s • w) τ) i = s * (P.mxInv τ *ᵥ w τ) i := fun s w => by
    rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦsum : ∀ {J : Type} (s : Finset J) (w : J → Vec K a ι),
      (P.mxInv τ *ᵥ (∑ x ∈ s, w x) τ) i = ∑ x ∈ s, (P.mxInv τ *ᵥ w x τ) i := fun s w => by
    rw [Finset.sum_apply, Matrix.mulVec_sum, Finset.sum_apply]
  conv_lhs => rw [desc_eq, P.eq_sum_phi_bas m]

  rw [hΦs, map_sum, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla_pow_smul, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [hΦs, hΦ, descN_eq]
  have hX : (X : K⟦X⟧) ^ k = X ^ p * X ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
  rw [hX]
  ring

theorem taylor_of_basis {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}
    [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (C : Conn P)
    (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι),
      (X : K⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S O K e)
    (hΓ : ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (l : OCr l O) ^ r ∣ toOCr l O (Γ i j) -
        ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ j k i⟩)) :
    I.Taylor C := by
  intro g
  obtain ⟨Γ, hΓL, hconv⟩ := hΓ g
  refine ⟨Γ, hΓL, fun m r => ?_⟩
  let c : ι → ZMod a → ↥(S O K e) := coordL P (S O K e) m
  have hcj : ∀ j τ, (c j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m : Vec K a ι) τ) j := fun j τ => rfl
  have hcm : ∀ j, toCris t ϖ P m j = ϖ.iC t K (c j) := fun j => rfl
  have F3 : ∀ k i, toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩ i =
      ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : OCr l O) *
        (ϖ.iC t K (fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) *
          ϖ.iC t K (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
    intro k i
    have h1 : coordL P (S O K e) ⟨C.desc k m, C.desc_mem k m.2⟩ i =
        ∑ j, ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ZMod a → ↥(S O K e)) *
          ((fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) * (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
      funext τ
      apply Subtype.ext
      refine (coord_desc C m k τ i).trans ?_
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, AddSubmonoidClass.coe_finsetSum,
        MulMemClass.coe_mul, SubringClass.coe_natCast, hcj]
    rw [toCris_apply, h1]

    simp only [map_sum, map_mul, map_natCast]
  have key : ∀ p : ι × ι, ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      galOCr O (g : GQ l) (ϖ.iC t K (c p.2)) * toOCr l O (Γ p.1 p.2) -
        ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c p.2 τ), descN_mem_S e q (c p.2 τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 (k - q) p.1⟩)) :=
    fun p => cauchy_dvd _ _ (fun k => ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 k p.1⟩)) _ _
      (fun r => galOCr_iC_taylor t ϖ g (c p.2) r) (fun r => hconv p.1 p.2 r) r
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun p : ι × ι => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
  refine ⟨fun i => ∑ j, z (i, j), funext fun i => ?_⟩
  have e1 : (Γ.map (toOCr l O) *ᵥ fun j => galOCr O (g : GQ l) (toCris t ϖ P m j)) i =
      ∑ j, galOCr O (g : GQ l) (ϖ.iC t K (c j)) * toOCr l O (Γ i j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hcm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (∑ k ∈ Finset.range n, ϖ.muDiv a O g k • toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩) i =
      ∑ j, ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c j τ), descN_mem_S e q (c j τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ j (k - q) i⟩)) := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, F3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, muDiv_mul_choose a O ϖ g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
    ring
  rw [Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => hz (i, j)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C :=
  fun _ _ _ _ _ _ ϖ LL _ _ _ _ _ _ _ _ I C hS hΓ => taylor_of_basis (thetaW _ LL) ϖ I C hS hΓ

end GlobalTheory.TaylorBasis
end
end
