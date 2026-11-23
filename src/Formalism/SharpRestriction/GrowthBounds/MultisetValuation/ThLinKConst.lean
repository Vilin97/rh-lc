module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InClassOfExp
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntRPsubst
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
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntRPsubst
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThPosSubPosAdd

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

section CgCalc

variable {ι K : Type} [Field K] (R : Subring K) (pp : K)

def Cg (f g : MvPowerSeries ι K) : Prop := ∃ Y : MvPowerSeries ι K, IntR R Y ∧ f = g + MvPowerSeries.C pp * Y

variable {R pp}

theorem cg_refl (f : MvPowerSeries ι K) : Cg R pp f f := ⟨0, IntR_zero, by simp⟩

theorem cg_of_eq {f g : MvPowerSeries ι K} (h : f = g) : Cg R pp f g := h ▸ cg_refl f

theorem cg_trans {f g k : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_add {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f + f') (g + g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_sum {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Cg R pp (F a) (G a)) :
    Cg R pp (∑ a ∈ s, F a) (∑ a ∈ s, G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cg_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cg_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem cg_mul {f g f' g' : MvPowerSeries ι K} (hf' : IntR R f') (hg : IntR R g) (h1 : Cg R pp f g)
    (h2 : Cg R pp f' g') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  refine ⟨g * Y' + Y * f', IntR_add (IntR_mul hg hY') (IntR_mul hY hf'), ?_⟩
  rw [e]
  conv_lhs => rw [add_mul, e']
  conv_rhs => rw [e']
  ring

theorem cg_pow {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) (h : Cg R pp f g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq (by simp)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul hf (IntR_pow hg k) ih h

theorem cg_of_coeff {f g : MvPowerSeries ι K}
    (h : ∀ n, ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y) : Cg R pp f g := by
  choose y hy he using h
  let Y : MvPowerSeries ι K := fun n => y n
  have hYc : ∀ n, MvPowerSeries.coeff n Y = y n := fun _ => rfl
  refine ⟨Y, fun n => by rw [hYc]; exact hy n, ?_⟩
  ext n
  rw [map_add (f := _), MvPowerSeries.coeff_C_mul, he n, hYc]

theorem cg_coeff {f g : MvPowerSeries ι K} (h : Cg R pp f g) (n : ι →₀ ℕ) :
    ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨_, hY n, by rw [e, map_add (f := _), MvPowerSeries.coeff_C_mul]⟩

end CgCalc

section Pos

theorem th_posSub_posAdd {n' : ℕ} (s : Fin n') (d : ℕ) : posSub (posAdd s d) d = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := s.pos; omega⟩
  apply Fin.ext
  show ((s.val + d) % (m + 1) + (m + 1) * d - d) % (m + 1) = s.val
  have e : (s.val + d) % (m + 1) + (m + 1) * d - d = (s.val + d) % (m + 1) + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : s.val + d + m * d = s.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

theorem th_posAdd_posSub {n' : ℕ} (t : Fin n') (d : ℕ) : posAdd (posSub t d) d = t := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := t.pos; omega⟩
  apply Fin.ext
  show ((t.val + (m + 1) * d - d) % (m + 1) + d) % (m + 1) = t.val
  have e : t.val + (m + 1) * d - d = t.val + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : t.val + m * d + d = t.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

theorem th_odd_posAdd {n' : ℕ} (hev : Even n') (s : Fin n') (d : ℕ) :
    (posAdd s d).val % 2 = (s.val + d) % 2 := by
  show (s.val + d) % n' % 2 = _
  exact Nat.mod_mod_of_dvd _ hev.two_dvd

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThLinKConst

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

variable {p : ℕ} [hp : Fact p.Prime] {n' r0 r1 : ℕ} (K' : Type) [Field K'] [Algebra (K0 p) K']

def Aw (w : WW p) (k : ℕ) : K' := wK' p K' ((sigW p)^[k] w)

def FrobSumH (p n' r0 r1 : ℕ) (K' : Type) [Field K'] (R : Subring K') : Prop :=
  ∀ (s : Finset (Fin n')) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K'), (∀ i ∈ s, IntR R (x i)) →
    ∃ Y : MvPowerSeries (Zidx n' r0 r1) K', IntR R Y ∧
      (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y

def FrobWH (p : ℕ) [Fact p.Prime] : Prop := ∀ a : WW p, ∃ y : WW p, sigW p a = a ^ p + (p : WW p) * y

variable {K'} (vp : K')

theorem th_Aw_mem (w : WW p) (k : ℕ) : Aw K' w k ∈ Rp p K' vp := W_mem_Rp p K' vp _

theorem th_Aw_succ (hW : FrobWH p) (w : WW p) (k : ℕ) :
    ∃ y ∈ Rp p K' vp, Aw K' w (k + 1) = Aw K' w k ^ p + (p : K') * y := by
  obtain ⟨y, hy⟩ := hW ((sigW p)^[k] w)
  refine ⟨wK' p K' y, ?_, ?_⟩
  · have h1 := th_Aw_mem vp y 0
    simpa [Aw] using h1
  · simp only [Aw, wK', Function.iterate_succ_apply', hy, map_add (f := _), map_mul, map_pow, map_natCast]

theorem th_frob_lin (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (e : Fin n' → ℕ) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K') (hx : ∀ s, IntR (Rp p K' vp) (x s)) :
    Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s + 1)) * x s ^ p) := by
  have hint : ∀ s ∈ P, IntR (Rp p K' vp) (MvPowerSeries.C (Aw K' w (e s)) * x s) :=
    fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) (hx s)
  obtain ⟨Y, hY, hEq⟩ := hF P (fun s => MvPowerSeries.C (Aw K' w (e s)) * x s) hint
  have h1 : Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, (MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p) := ⟨Y, hY, hEq⟩
  refine cg_trans h1 (cg_sum _ _ _ fun s _ => ?_)
  obtain ⟨z, hz, hzeq⟩ := th_Aw_succ vp hW w (e s)
  rw [mul_pow, ← map_pow]
  refine cg_mul (IntR_pow (hx s) p) (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) ?_ (cg_refl _)
  refine cg_of_coeff fun n => ?_
  by_cases hn : n = 0
  · subst hn
    refine ⟨-z, Subring.neg_mem _ hz, ?_⟩
    rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_C, hzeq]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C, if_neg hn, if_neg hn]
    ring

def linK (K' : Type) [Field K'] [Algebra (K0 p) K'] (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1)
    (k : ℕ) : MvPowerSeries (Zidx n' r0 r1) K' :=
  ∑ s ∈ P, MvPowerSeries.C (Aw K' w (s.val + k)) * MvPowerSeries.X (s, a, b) ^ (p ^ k)

theorem th_linK_int (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ) :
    IntR (Rp p K' vp) (linK K' w P a b k) := by
  unfold linK
  exact IntR_sum _ _ fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _))
    (IntR_pow (IntR_X (R := Rp p K' vp) _) _)

theorem th_linK_const (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (linK K' w P a b 0) = 0 := by
  simp [linK]

theorem th_claimF (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (a : Fin r0) (b : Fin r1) (k : ℕ) :
    Cg (Rp p K' vp) (p : K') (linK K' w P a b 0 ^ (p ^ k)) (linK K' w P a b k) := by
  induction k with
  | zero =>
    apply cg_of_eq
    simp only [pow_zero, pow_one]
  | succ k ih =>
    have hL : IntR (Rp p K' vp) (linK K' w P a b 0) := th_linK_int vp w P a b 0
    have h1 := cg_pow (IntR_pow hL (p ^ k)) (th_linK_int vp w P a b k) ih p
    rw [← pow_mul, ← pow_succ] at h1
    refine cg_trans h1 ?_
    have h2 := th_frob_lin vp hF hW w P (fun s => s.val + k) (fun s => MvPowerSeries.X (s, a, b) ^ (p ^ k))
      (fun s => IntR_pow (IntR_X (R := Rp p K' vp) _) _)
    simp only [← pow_mul, ← pow_succ] at h2
    exact h2

theorem th_coeff_linK (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ)
    (n : Zidx n' r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (linK K' w P a b k) =
      ∑ s ∈ P, Aw K' w (s.val + k) * (if n = Finsupp.single (s, a, b) (p ^ k) then 1 else 0) := by

  simp only [linK, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]

theorem th_reindex (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) (n : Zidx n' r0 r1 →₀ ℕ) (l : ℕ) :
    (-1 : K') ^ l * ∑ s ∈ P, Aw K' w (s.val + 2 * l) *
        (if n = Finsupp.single (s, a, b) (p ^ (2 * l)) then 1 else 0) =
      ∑ t ∈ P, Aw K' w t.val *
        (if n = Finsupp.single (posSub t (2 * l), a, b) (p ^ (2 * l)) then (-1 : K') ^ l else 0) := by
  have hAw : ∀ s : Fin n', Aw K' w (posAdd s (2 * l)).val = Aw K' w (s.val + 2 * l) := by
    intro s
    simp only [Aw, posAdd]
    rw [Function.IsPeriodicPt.iterate_mod_apply hper]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun t => posSub t (2 * l)) (fun s => posAdd s (2 * l)) (fun t ht => hPs t ht l)
    (fun s hs => hPa s hs l) (fun t _ => th_posAdd_posSub t _) (fun s _ => th_posSub_posAdd s _) (fun t _ => ?_)
  have h1 : Aw K' w t.val = Aw K' w ((posSub t (2 * l)).val + 2 * l) := by
    rw [← hAw, th_posAdd_posSub]
  rw [h1]
  split_ifs <;> ring

theorem th_claimM (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (μ : PowerSeries K')
    (hT1 : ∀ n, ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y)
    (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) :
    Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) := by
  have hL0 := th_linK_const (K' := K') w P a b
  have hsL : PowerSeries.HasSubst (linK K' w P a b 0) := PowerSeries.HasSubst.of_constantCoeff_zero hL0

  have h1 : Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (PowerSeries.subst (linK K' w P a b 0) (altF K' p)) := by
    choose y hy he using hT1
    have e : μ = altF K' p + PowerSeries.C (p : K') * PowerSeries.mk y := by
      ext n
      rw [map_add (f := _), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← he n]
      ring
    refine ⟨PowerSeries.subst (linK K' w P a b 0) (PowerSeries.mk y),
      IntR_psubst hL0 (th_linK_int vp w P a b 0) (fun n => by rw [PowerSeries.coeff_mk]; exact hy n), ?_⟩
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hsL, PowerSeries.subst_mul hsL, PowerSeries.subst_C]
  refine cg_trans h1 (cg_of_coeff fun n => ?_)
  rw [Formalism.InvariantFactorPaths.G7.TwoS.coeff_subst_altF hp.out.two_le hL0 n]
  choose y hy he using fun l => cg_coeff (th_claimF vp hF hW w P a b (2 * l)) n
  refine ⟨∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * y l,
    Subring.sum_mem _ fun l _ => (Rp p K' vp).mul_mem ((Rp p K' vp).pow_mem ((Rp p K' vp).neg_mem
      (Rp p K' vp).one_mem) l) (hy l), ?_⟩
  have e2 : MvPowerSeries.coeff n (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) =
      ∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * MvPowerSeries.coeff n (linK K' w P a b (2 * l)) := by

    rw [map_sum]
    simp only [MvPowerSeries.coeff_C_mul, th_coeff_linK, th_reindex w hper P hPa hPs a b n]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    rfl
  rw [e2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← pow_mul, he l]
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end
