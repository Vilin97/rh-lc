module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
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
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.Interval.Finset.Box
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLe

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_ext_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F)
    (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  intro l _ F _ ι tsh hn hι hsurj α s z R hR hz
  classical
  obtain ⟨-, -, -, -, -, hon, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := GlobalTheory.PSer.Laws.norm_l
  have hlpos : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hlpos
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; exact inv_pos.2 (by linarith)
  obtain ⟨w, hw⟩ := hon (l : ℂ_[l]) hl1.le
  have hnw : ‖ι w‖ = ‖(l : ℂ_[l])‖ := by rw [← hn, hι, hw]

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖ι w‖ ^ N * R ≤ 1 := by
    rcases le_or_gt R 1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0:ℝ) < R)) (hnw ▸ hl1)
      refine ⟨N, ?_⟩
      have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℝ) < R)
      rw [inv_mul_cancel₀ (by linarith)] at this
      exact this.le
  set c : F := ι w ^ N with hc
  have hcn : ‖c‖ = ‖ι w‖ ^ N := by rw [hc, norm_pow]
  have hcpos : 0 < ‖c‖ := by rw [hcn, hnw]; exact pow_pos hl0 N
  have hx : ∀ a, ∃ x : Fl l, ι x = if a ∈ s then c * z a else 0 := by
    intro a
    split_ifs with ha
    · refine hsurj _ ?_
      rw [norm_mul, hcn]
      calc ‖ι w‖ ^ N * ‖z a‖ ≤ ‖ι w‖ ^ N * R :=
            mul_le_mul_of_nonneg_left (hz a ha) (pow_nonneg (norm_nonneg _) _)
        _ ≤ 1 := hN
    · exact ⟨0, map_zero ι⟩
  choose x hxe using hx
  have hxa : ∀ a ∈ s, ι (x a) = c * z a := fun a ha => by rw [hxe, if_pos ha]
  have hsa : ∀ a ∈ s, sh (x a) = tsh c * tsh (z a) := fun a ha => by
    rw [← hι, hxa a ha, map_mul]
  have hss : sh (∑ a ∈ s, x a) = tsh c * tsh (∑ a ∈ s, z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hι, map_sum, Finset.sum_congr rfl hxa, ← Finset.mul_sum, map_mul]
  have hbd : ∀ a ∈ s, ‖sh (x a)‖ ≤ ‖c‖ * R := fun a ha => by
    rw [hsa a ha, norm_mul, hn, hn]
    exact mul_le_mul_of_nonneg_left (hz a ha) (norm_nonneg _)
  have key := (untilt_sum_sub_le l α s (‖c‖ * R) x (mul_nonneg (norm_nonneg _) hR) hbd).1
  rw [hss, Finset.sum_congr rfl hsa, ← Finset.mul_sum, ← mul_sub, norm_mul, hn] at key
  have : ‖c‖ * ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖c‖ * (‖(l : ℂ_[l])‖ * R) := by
    linarith [key]
  exact le_of_mul_le_mul_left this hcpos

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLeStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  first | exact @GlobalTheory.untilt_ext_sum_sub_le | exact GlobalTheory.untilt_ext_sum_sub_le | (intros; apply GlobalTheory.untilt_ext_sum_sub_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPower

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPowerStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l), ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  first | exact @GlobalTheory.PSer.map_pw_eq_pw | exact GlobalTheory.PSer.map_pw_eq_pw | (intros; apply GlobalTheory.PSer.map_pw_eq_pw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRow

section

@[expose] public section

noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRowStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  first | exact @GlobalTheory.PSer.row_lam_sub_untilt_rowT | exact GlobalTheory.PSer.row_lam_sub_untilt_rowT | (intros; apply GlobalTheory.PSer.row_lam_sub_untilt_rowT <;> assumption)
end
end
