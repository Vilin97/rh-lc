module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisSeriesTermsMemPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoSidedShiftSeriesHasSum

section

@[expose] public section

open Polynomial

namespace GlobalTheory.TwoSidedShift

theorem mem_pow_span_iff (l : ℕ) (A : Type) [CommRing A] (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
  simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_sum_shift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A),
    (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) →
    ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) →
      HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  intro l _ A _ _ φ h c hc hsh
  set ψ : A →+* A := φ ^ h with hψdef
  have hψ : ∀ x, φ^[h] x = ψ x := fun x => by rw [hψdef, RingHom.coe_pow]
  have hsh' : ∀ n : ℤ, ψ (c n) = (l : A) * c (n + 1) := fun n => by rw [← hψ]; exact hsh n
  set T : ℕ → A := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n with hT
  have hIcc : ∀ N : ℕ, Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
      = insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
    intro N; ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  have hstep : ∀ N : ℕ, T (N + 1) = T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) := by
    intro N
    simp only [hT]
    rw [hIcc N, Finset.sum_insert, Finset.sum_insert]
    · ring
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
  have hdstep : ∀ N : ℕ, (l : A) ^ (N + 1) ∣ T (N + 1) - T N := by
    intro N
    rw [hstep N, show T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) - T N
      = c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) by ring]
    refine dvd_add ?_ ?_
    · have := hc ((N + 1 : ℕ) : ℤ)
      rwa [show (((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
    · have := hc (-((N + 1 : ℕ) : ℤ))
      rwa [show (-((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
  have hcauchy : ∀ m n : ℕ, m ≤ n → (l : A) ^ m ∣ T n - T m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [show T (n + 1) - T m = (T (n + 1) - T n) + (T n - T m) by ring]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hdstep n)) ih
  obtain ⟨w, hw⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance (f := T)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_span_iff]
      rw [← dvd_neg, neg_sub]; exact hcauchy m n hmn)
  have hwT : ∀ N : ℕ, (l : A) ^ N ∣ w - T N := by
    intro N
    have := hw N
    rw [SModEq.sub_mem, mem_pow_span_iff] at this
    rw [← dvd_neg, neg_sub]; exact this

  have hE : ∀ N : ℕ, ψ (T N) - (l : A) * T N = (l : A) * (c ((N : ℤ) + 1) - c (-(N : ℤ))) := by
    intro N
    induction N with
    | zero => simp [hT, hsh']; ring
    | succ N ih =>
      rw [hstep N, map_add (f := _), map_add (f := _), hsh', hsh']
      have e1 : (-((N + 1 : ℕ) : ℤ) + 1) = -(N : ℤ) := by push_cast; ring
      have e2 : (((N + 1 : ℕ) : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) + 1 := rfl
      rw [e1]
      push_cast at ih ⊢
      linear_combination ih
  have hEd : ∀ N : ℕ, (l : A) ^ N ∣ ψ (T N) - (l : A) * T N := by
    intro N
    rw [hE N]
    have h1 : (l : A) ^ (N + 1) ∣ c ((N : ℤ) + 1) := by
      have := hc ((N : ℤ) + 1)
      rwa [show ((N : ℤ) + 1).natAbs = N + 1 by omega] at this
    have h2 : (l : A) ^ N ∣ c (-(N : ℤ)) := by simpa using hc (-(N : ℤ))
    exact dvd_mul_of_dvd_right (dvd_sub ((pow_dvd_pow _ (by omega)).trans h1) h2) _
  refine ⟨w, ?_, ?_⟩
  · rw [hψ, ← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, mem_pow_span_iff]
    rw [show ψ w - (l : A) * w = ψ (w - T N) + (ψ (T N) - (l : A) * T N) - (l : A) * (w - T N) by
      rw [map_sub]; ring]
    refine dvd_sub (dvd_add ?_ (hEd N)) (dvd_mul_of_dvd_right (hwT N) _)
    have := map_dvd ψ (hwT N)
    simpa [map_pow, map_natCast] using this
  · intro Θ hΘ
    set r : ℝ := ‖(l : ℂ_[l])‖ with hr
    have hr1 : r < 1 := by
      have h := PadicComplex.norm_extends' l (l : ℚ_[l])
      have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
      rw [← h] at h2
      simpa using h2
    have hr0 : 0 ≤ r := norm_nonneg _
    have hbound : ∀ (n : ℕ) (a : A), (l : A) ^ n ∣ a → ‖Θ a‖ ≤ r ^ n := by
      intro n a ⟨b, hb⟩
      rw [hb, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hr0 _) (hΘ b)
    change Filter.Tendsto (fun s : Finset ℤ => ∑ b ∈ s, Θ (c b)) Filter.atTop (nhds (Θ w))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr1
    refine ⟨Finset.Icc (-(N : ℤ)) N, fun s hs => ?_⟩
    rw [dist_eq_norm, ← Finset.sum_sdiff hs]
    have hrest : ‖∑ n ∈ s \ Finset.Icc (-(N : ℤ)) N, Θ (c n)‖ ≤ r ^ N := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
      have hn' : n ∉ Finset.Icc (-(N : ℤ)) N := (Finset.mem_sdiff.1 hn).2
      rw [Finset.mem_Icc] at hn'
      refine (hbound _ _ (hc n)).trans (pow_le_pow_of_le_one hr0 hr1.le (by omega))
    have hhead : ‖∑ n ∈ Finset.Icc (-(N : ℤ)) N, Θ (c n) - Θ w‖ ≤ r ^ N := by

      rw [← map_sum, ← map_sub]
      refine hbound N _ ?_
      rw [← dvd_neg, neg_sub]; exact hwT N
    rw [add_sub_assoc]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hrest hhead)) hN

end GlobalTheory.TwoSidedShift

theorem GlobalTheory.twoSided_shift_series : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) :=
  GlobalTheory.TwoSidedShift.exists_sum_shift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoSidedShiftSeriesHasSumStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.twoSided_shift_series_hasSum : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  first | exact @GlobalTheory.twoSided_shift_series | exact GlobalTheory.twoSided_shift_series | (intros; apply GlobalTheory.twoSided_shift_series <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntilt

section

@[expose] public section

noncomputable section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem iter_tm {l : ℕ} [Fact l.Prime] (j : ℕ) (z : Fl l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[j] (algebraMap (Ainf l) (Acris l) (tm z)) =
      algebraMap (Ainf l) (Acris l) (tm (z ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    refine (GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_
    rw [← pow_mul, ← pow_succ]

theorem acris_cancel {l : ℕ} [Fact l.Prime] (k : ℕ) (u v : Acris l)
    (e : (l : Acris l) ^ k * u = (l : Acris l) ^ k * v) : u = v := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply (GlobalTheory.MemLoc.acris_basic l).2.1
    linear_combination e

theorem series_acris : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  intro l _ h x h2 hx
  obtain ⟨-, -, -, hpw_comp, hpw_nat, -, -⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨c, hdvd, hc⟩ := GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  have hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) =
      (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a := by
    intro j k a
    rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
  have hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x := by
    intro n j
    rw [← hpw_nat, ← hpw_comp, add_comm]
  have shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1) := by
    intro n
    apply acris_cancel (n.toNat + (n+1).toNat)
    have e1 := congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)
    rw [hφl, hφl, iter_tm, hpwj] at e1
    have e2 := hc (n + 1)
    have hh : (n + 1) * (h : ℤ) = n * h + h := by ring
    rw [hh] at e2
    calc (l : Acris l) ^ (n.toNat + (n+1).toNat) * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)
        = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ n.toNat * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)) := by ring
      _ = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ (-n).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by rw [e1]
      _ = (l : Acris l) ^ (n.toNat + 1) * ((l : Acris l) ^ (-(n+1)).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
      _ = _ := by rw [← e2]; ring
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.T.twoSided_shift_series_hasSum l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift
  refine ⟨w, hw, fun Θ hΘ hΘt j => ?_⟩
  have hs := hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)
  have hl : (l : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) =
      (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
    intro n
    have e := congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul,
      map_mul, map_pow, map_pow, map_natCast, hΘt] at e
    rw [RingHom.comp_apply, RingHom.coe_pow]
    have hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ) := by omega
    have ha : (l : ℂ_[l]) ^ n.toNat ≠ 0 := pow_ne_zero _ hl
    rw [hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
    calc Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))
        = ((l : ℂ_[l]) ^ n.toNat)⁻¹ * ((l : ℂ_[l]) ^ n.toNat * Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))) := by
          rw [inv_mul_cancel_left₀ ha]
      _ = _ := by rw [e]; ring
  have hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x))
      ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w) := by
    simpa only [hterm] using hs
  rw [lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]

end GlobalTheory.PSer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntiltStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusSeries_acris_untilt : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  first | exact @GlobalTheory.PSer.series_acris | exact GlobalTheory.PSer.series_acris | (intros; apply GlobalTheory.PSer.series_acris <;> assumption)
end
end
