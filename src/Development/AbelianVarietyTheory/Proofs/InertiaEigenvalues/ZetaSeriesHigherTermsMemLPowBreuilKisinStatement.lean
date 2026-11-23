module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulConnectionSeriesTermMemLatticeStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulEqPrimePowSmulPhiModule

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem PhiMod.exists_X_pow_smul_eq_l_pow_smul (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)
    (n : ℕ) : ∀ w ∈ P.MM, ∃ w' ∈ P.MM,
      (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  intro w hw
  have hl0 := l_ne_zero (K := K) l
  have hlp := (Fact.out : l.Prime).pos
  have hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e := by
    refine monomial_mem_S ?_
    rw [norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS,
      Nat.mul_div_cancel_left _ (NeZero.pos e)]
    refine (norm_factorial_le l _).trans (le_of_eq ?_)
    rw [pow_succ, Nat.mul_div_cancel _ hlp]
  refine ⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩
  change _ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)
  rw [← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
end BK
end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulEqPrimePowSmulPhiModuleStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (n : ℕ), ∀ w ∈ P.MM, ∃ w' ∈ P.MM, (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  first | exact @GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | exact GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | (intros; apply GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTerms

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow (K := K) (a := a) (ι := ι) m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow (K := K) (a := a) (ι := ι) m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  have hext {τ : ZMod a} {v : ι → K⟦X⟧} :
      v ∈ P.extc (S O K e) τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι (S O K e) := by
    have hmem {v : ι → K⟦X⟧} : v ∈ P.extc (S O K e) τ ↔
        ∃ m ∈ vecs ι (S O K e), v = P.mx τ *ᵥ m := by
      rw [PhiMod.extc, Submodule.mem_span_range_iff_exists_fun]
      have key (c : ι → S O K e) : ∑ i, c i • (P.mx τ).col i =
          P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
        ext1 j
        simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, fun i => (c i).2, key c⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨fun i => ⟨m i, hm i⟩, key _⟩
    rw [hmem]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rwa [Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]⟩
  refine mem_tot.2 fun τ => hext.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, hext.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, hext.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTermsStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  first | exact @GlobalTheory.BK.PhiMod.mem_MM_of_series | exact GlobalTheory.BK.PhiMod.mem_MM_of_series | (intros; apply GlobalTheory.BK.PhiMod.mem_MM_of_series <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaSeriesHigherTermsMemLPowBreuilKisin

section

@[expose] public section

noncomputable section

namespace GlobalTheory

open PowerSeries GlobalTheory.BK

theorem nat_mul_add_le_pow {l : ℕ} (hl : 2 ≤ l) (n : ℕ) : n * l + l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right l ih
    have h2 := Nat.mul_le_mul_left (n * l + l) hl
    nlinarith

theorem zeta_add_lphi_conn_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hηH hHl hy₀
  set y : Vec K a ι := (X : K⟦X⟧) ^ e • y₀ with hy
  set A := l - 14 * H with hA
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hlA : (l : K) ^ A ≠ 0 := pow_ne_zero _ hl0
  set c : K := ((l : K) ^ A)⁻¹ with hc
  set w : Vec K a ι := c • (D.zeta y + D.lphi (D.conn y)) with hw
  let t : ℕ → Vec K a ι := fun n => -(c • (D.lphi ^ (n + 2)) (D.conn y))
  have hterm : ∀ n, ∃ v ∈ D.MM, t n = (l : K) ^ n • v := by
    intro n
    obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀ (n + 1)
    obtain ⟨w', hw', h₂⟩ := GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule O K l e a ι D.toPhiMod (n + 1) w₁ hw₁
    set B := H + 2 * η + (n + 1) * (η - 1) with hB
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hineq : B + A + n ≤ l ^ (n + 1) := by
      have h1 := nat_mul_add_le_pow hl2 n
      have h2 : (n + 1) * (η - 1) ≤ (n + 1) * H := Nat.mul_le_mul_left _ (by omega)
      have h3 : n * (H + 1) ≤ n * l := Nat.mul_le_mul_left _ (by omega)
      have h4 : (n + 1) * H = n * H + H := by ring
      have h5 : n * (H + 1) = n * H + n := by ring
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hineq
    rw [h₂, hd, show B + A + n + d = B + (A + (n + d)) by ring, pow_add (l : K) B, mul_smul] at h₁
    have h₃ := congrArg (fun v => ((l : K) ^ B)⁻¹ • v) h₁
    simp only [inv_smul_smul₀ (pow_ne_zero B hl0)] at h₃
    refine ⟨-((l : K) ^ d • w'), neg_mem (PhiMod.l_pow_smul_mem_MM _ d hw'), ?_⟩
    change -(c • (D.lphi ^ (n + 1 + 1)) (D.conn y)) = _
    rw [h₃, pow_add, mul_smul, hc, inv_smul_smul₀ hlA, pow_add, mul_smul, smul_neg]
  have hpart : ∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m := by
    intro m
    have key := D.zeta_add_sum_mem y (m + 1)
    rw [Finset.sum_range_succ'] at key
    have heq : w - ∑ n ∈ Finset.range m, t n = c • (D.zeta y + (∑ n ∈ Finset.range m,
        (D.lphi ^ (n + 1 + 1)) (D.conn y) + (D.lphi ^ (0 + 1)) (D.conn y))) := by
      simp only [t, hw, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add, pow_one, smul_add,
        Finset.smul_sum]
      abel
    rw [heq]
    exact Submodule.smul_of_tower_mem _ c (uPow_anti (by omega) key)
  refine ⟨w, GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms O K l e a ι D.toPhiMod w t hterm hpart, ?_⟩
  rw [hw, hc, smul_inv_smul₀ hlA]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaSeriesHigherTermsMemLPowBreuilKisinStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  first | exact @GlobalTheory.zeta_add_lphi_conn_mem | exact GlobalTheory.zeta_add_lphi_conn_mem | (intros; apply GlobalTheory.zeta_add_lphi_conn_mem <;> assumption)
end
end
