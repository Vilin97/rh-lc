module

public import Formalism.PeriodIntegrals.Minkowski
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.CharpolyDvdOfPowEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Trace

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.Assemble

section

@[expose] public section

namespace PI.Mk

open Finset

theorem term_eq (N p i : ℕ) : N / (p ^ i * (p - 1)) = (N / (p - 1)) / p ^ i := by
  rw [mul_comm, Nat.div_div_eq_div_mul]

theorem padicValNat_pow_mul_factorial (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValNat ℓ (ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial) = PI.minkowskiExp N ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set m := N / (ℓ - 1) with hm
  have hmN : m ≤ N := Nat.div_le_self _ _
  have hlog : Nat.log ℓ m < N + 1 := lt_of_le_of_lt (Nat.log_le_self _ _) (Nat.lt_succ_of_le hmN)
  rw [Nat.padicValNat_def,
    Nat.multiplicity_mul (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _),
    Nat.multiplicity_prime_pow, _root_.multiplicity_factorial hlog]
  unfold PI.minkowskiExp
  simp_rw [term_eq, ← hm]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp

theorem minkowskiExp_eq_zero (N p : ℕ) (hp : N + 2 ≤ p) : PI.minkowskiExp N p = 0 := by
  unfold PI.minkowskiExp
  apply Finset.sum_eq_zero
  intro i _
  have h0 : N / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [term_eq, h0, Nat.zero_div]

theorem pow_minkowskiExp_dvd (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℓ ^ PI.minkowskiExp N ℓ ∣ PI.minkowskiM N := by
  by_cases h : ℓ < N + 2
  · unfold PI.minkowskiM
    exact Finset.dvd_prod_of_mem (fun p => p ^ PI.minkowskiExp N p)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hℓ⟩)
  · rw [minkowskiExp_eq_zero N ℓ (by omega), pow_zero]
    exact one_dvd _

theorem minkowskiBound_of (h : PGroupStep) : PI.MinkowskiBound := by
  intro N G hG
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ k hℓ hk
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime ℓ hk
  have hinj : Function.Injective G.subtype := G.subtype_injective
  have hcard : Nat.card (K.map G.subtype) = ℓ ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hK]
  have hfin : Finite (K.map G.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hp : IsPGroup ℓ (K.map G.subtype) := IsPGroup.of_card hcard
  have hdvd := h N ℓ hℓ (K.map G.subtype) hfin hp
  rw [hcard] at hdvd
  have hne : ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _)
  have hle : k ≤ PI.minkowskiExp N ℓ := by
    rw [← padicValNat_pow_mul_factorial N ℓ hℓ]
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne).1 hdvd
  exact (pow_dvd_pow ℓ hle).trans (pow_minkowskiExp_dvd N ℓ hℓ)

end PI.Mk
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps

section

@[expose] public section

namespace PI.Mk

open Finset Polynomial

noncomputable def schurPoly (N ℓ m : ℕ) : ℤ[X] :=
  ∏ y ∈ range m, (X - C ((N : ℤ) - (ℓ : ℤ) * ((y + 1 : ℕ) : ℤ)))

theorem schurPoly_eval_top (N ℓ m : ℕ) :
    (schurPoly N ℓ m).eval (N : ℤ) = ((ℓ ^ m * m.factorial : ℕ) : ℤ) := by
  unfold schurPoly
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_sub_cancel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]
  push_cast
  ring

theorem schurPoly_eval_zero (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by
  unfold schurPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))
  have : y - 1 + 1 = y := by omega
  simp [this]

theorem dvd_sum_eval (hb : PowerSumStep) (N : ℕ)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (f : ℤ[X]) :
    (Fintype.card P : ℤ) ∣ ∑ g : P, f.eval (Matrix.trace
      ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ)) := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro k _
  rw [← Finset.mul_sum]
  exact Dvd.dvd.mul_left (hb N P k) _

theorem pGroupStep_of (ha : TraceStep) (hb : PowerSumStep) : PGroupStep := by
  intro N ℓ hℓ P hfin hP
  have : Fintype P := Fintype.ofFinite P
  set m := N / (ℓ - 1) with hm
  have hdvd := dvd_sum_eval hb N P (schurPoly N ℓ m)
  rw [Finset.sum_eq_single (1 : P)] at hdvd
  · have h1 : Matrix.trace (((1 : P) : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ) = (N : ℤ) := by
      simp
    rw [h1, schurPoly_eval_top, Int.natCast_dvd_natCast, ← Nat.card_eq_fintype_card] at hdvd
    exact hdvd
  · intro g _ hg
    obtain ⟨a, hga⟩ := hP g
    have hmat : ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ) ^ (ℓ ^ a)
        = 1 := by
      have := congrArg (fun x : P => ((x : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ)) hga
      simpa using this
    obtain ⟨y, hy, htr, hy0⟩ := ha N ℓ a hℓ _ hmat
    rw [htr]
    apply schurPoly_eval_zero _ _ _ _ _ hy
    intro h0
    apply hg
    apply Subtype.ext
    apply Units.ext
    simpa using hy0 h0
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem minkowskiBound_of_steps (ha : TraceStep) (hb : PowerSumStep) : PI.MinkowskiBound :=
  minkowskiBound_of (pGroupStep_of ha hb)

end PI.Mk
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSum

section

@[expose] public section

namespace PI.Mk

open Matrix Finset

theorem trace_idem_nat {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ) (hE : E * E = E) :
    ∃ r : ℕ, E.trace = (r : ℚ) := by
  have hf : IsIdempotentElem (Matrix.toLin' E) := by
    change Matrix.toLin' E ∘ₗ Matrix.toLin' E = Matrix.toLin' E
    rw [← Matrix.toLin'_mul, hE]
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' E)), ?_⟩
  rw [← Matrix.trace_toLin'_eq]
  exact (LinearMap.IsIdempotentElem.isProj_range _ hf).trace

theorem card_dvd_sum_trace {H : Type*} [Group H] [Fintype H] {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : H → Matrix n n ℤ) (hρ : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    (Fintype.card H : ℤ) ∣ ∑ h : H, (ρ h).trace := by
  classical
  let M : H → Matrix n n ℚ := fun h => (ρ h).map (Int.castRingHom ℚ)
  have hM : ∀ a b, M (a * b) = M a * M b := fun a b => by
    simp only [M, hρ, Matrix.map_mul]
  have hc : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : ∀ a, M a * ∑ h, M h = ∑ h, M h := fun a => by
    rw [Finset.mul_sum]
    simp_rw [← hM]
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
  have hE : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) * ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) =
      (Fintype.card H : ℚ)⁻¹ • ∑ h, M h := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul]
    simp_rw [hsum]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul,
      mul_assoc, inv_mul_cancel₀ hc, mul_one]
  obtain ⟨r, hr⟩ := trace_idem_nat _ hE
  have htr : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h).trace = (Fintype.card H : ℚ)⁻¹ * ∑ h, ((ρ h).trace : ℚ) := by
    rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [M, Matrix.trace]
  rw [htr, inv_mul_eq_iff_eq_mul₀ hc] at hr
  refine ⟨(r : ℤ), ?_⟩
  have h2 : ((∑ h, (ρ h).trace : ℤ) : ℚ) = (((Fintype.card H : ℤ) * (r : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact hr
  exact_mod_cast h2

def kron {n : Type*} (k : ℕ) (M : Matrix n n ℤ) : Matrix (Fin k → n) (Fin k → n) ℤ :=
  fun i j => ∏ t, M (i t) (j t)

theorem kron_mul {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A B : Matrix n n ℤ) :
    kron k (A * B) = kron k A * kron k B := by
  ext i j
  simp only [kron, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.prod_mul_distrib]

theorem trace_kron {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A : Matrix n n ℤ) :
    (kron k A).trace = A.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, kron]
  rw [show (∑ i, A i i) ^ k = ∏ _t : Fin k, ∑ j, A j j by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem powerSumStep : PowerSumStep := by
  intro N P _ k
  have h := card_dvd_sum_trace (H := P)
    (fun g => kron k (((g : Matrix.GeneralLinearGroup (Fin N) ℤ)) : Matrix (Fin N) (Fin N) ℤ))
    (fun a b => by simp only [Subgroup.coe_mul, Units.val_mul, kron_mul])
  simpa only [trace_kron] using h

end PI.Mk
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski

section

@[expose] public section

theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
end
end
