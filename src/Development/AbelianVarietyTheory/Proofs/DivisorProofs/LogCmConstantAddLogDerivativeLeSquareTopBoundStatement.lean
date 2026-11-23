module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Mathlib.Algebra.Ring.IsFormallyReal

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstants

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.NormConst

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  show 0 < 2 * (D.host.rdE / 2)
  unfold Formalism.BasicNotions.Host.rdE
  have h0 : (0:ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h0 (1 / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem abs_discr_F (D : D7) : |(NumberField.discr D.host.F : ℝ)| = (2 * D.host.v) ^ D.R.f := by
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  rw [h2v]
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hn := GlobalTheory.RealPlaces.finrank_E D
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  have key : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
    rw [← hn]
    unfold Formalism.BasicNotions.Host.rdE
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
    have h3 : |(NumberField.discr D.host.E : ℝ)| = (NumberField.discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
    rw [h3, sq_abs]
  have hr0 : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [mul_comm, pow_mul] at key
  exact ((pow_left_inj₀ (pow_nonneg hr0 _) (abs_nonneg _) two_ne_zero).1 key).symm

theorem card_infinitePlace_E (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem sum_range_closed (k : ℕ) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (4 * ((i : ℝ) + 1) + 2 * k)) =
      2 * (n : ℝ) * (n + 1) * (2 * n + 1) / 3 + k * n * (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_closed k n]
    push_cast; ring

theorem sum_exponents (r k : ℕ) :
    (∑ a : Fin r, (((r - (a : ℕ)) * (4 * (r - (a : ℕ)) + 2 * k) : ℕ) : ℝ)) =
      2 * (r : ℝ) * (r + 1) * (2 * r + 1) / 3 + k * r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (((r - i) * (4 * (r - i) + 2 * k) : ℕ) : ℝ)) r,
    ← Finset.sum_range_reflect, ← sum_range_closed k r]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have e : r - (r - 1 - j) = j + 1 := by omega
  rw [e]; push_cast; ring

end GlobalTheory.CovDom.NormConst

namespace GlobalTheory.CovDom

theorem normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D
  have hv := NormConst.two_v_pos D
  refine ⟨fun a => pow_pos hv _, ?_⟩
  rw [NormConst.card_infinitePlace_E, D.what₂.card_Tau, NormConst.abs_discr_F]
  have hprod : ∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k) =
      (2 * D.host.v) ^ (∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) * (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) := by
    unfold sc
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul]
  rw [hprod, ← pow_mul, ← Real.rpow_natCast (2 * D.host.v) D.R.f,
    ← Real.rpow_mul hv.le, ← Real.rpow_natCast (2 * D.host.v) (_ * D.R.f), ← Real.rpow_add hv]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sum, NormConst.sum_exponents]
  ring

end GlobalTheory.CovDom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBound

section

@[expose] public section

open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField

theorem log_gamma_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log (Real.Gamma n) ≤ n * Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have hf : (m.factorial : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
    have h1 : m.factorial ≤ (m + 1) ^ (m + 1) :=
      (Nat.factorial_le_pow m).trans ((Nat.pow_le_pow_left (Nat.le_succ m) m).trans
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.le_succ m)))
    exact_mod_cast h1
  rw [hg, ← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos m) hf

theorem log_cmConst_le {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (hdF : 0 < dF) (hd : 1 ≤ d)
    (hk : 1 ≤ k) :
    Real.log (Formalism.PairingDivisionLocalBalance.cmConst dF d k κ) ≤ (((k : ℝ) - 1) / 2) * Real.log dF +
      ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ)) + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) * 8 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hG : ∀ τ, 0 < Real.Gamma ((k : ℝ) + κ τ) := fun τ =>
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ κ τ := Nat.cast_nonneg _; linarith)
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hq : 0 < 2 * Real.pi / Real.sqrt d := div_pos (by positivity) (by linarith)
  unfold Formalism.PairingDivisionLocalBalance.cmConst
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'))
      (pow_ne_zero _ hq.ne'),
    Real.log_mul (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'),
    Real.log_rpow hdF, Real.log_prod (fun τ _ => (hG τ).ne'), Real.log_pow]
  have h1 : Real.log (2 * Real.pi / Real.sqrt d) ≤ 8 := by
    have h3 := Real.log_le_sub_one_of_pos hq
    have h2 : 2 * Real.pi / Real.sqrt d ≤ 2 * Real.pi := div_le_self (by positivity) hsd
    linarith [Real.pi_le_four]
  have h0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK κ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

end GlobalTheory.SizesArch

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField GlobalTheory.ChiGrid

theorem sizes : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x →
    Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
      Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
        (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤
        bTH D Cx large₂.sc.x large₂.sc.b := by
  intro ε
  refine ⟨200, 0, fun D large₂ _ _ hR i j s hs1 hs2 => ?_⟩
  obtain ⟨-, -, hm4, hm, -, hmfNd, -, -, -, hrd1, hrd2, -, -, -⟩ := hR.size
  obtain ⟨hgb, hb675⟩ := GlobalTheory.BigTop.Fun.gap_le_b hR.size
  have hbL : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL1 : 1 ≤ large₂.sc.L := by
    rw [← hbL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx1 : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hlogx : 0 ≤ Real.log large₂.sc.x := Real.log_nonneg hx1.le
  have hcard : Fintype.card D.what₂.Tau = D.R.f := Formalism.MainNotions.Lnk.card_Tau D
  have hf1n : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1n

  have hsb : (s : ℝ) ≤ large₂.sc.b := by
    have h1 := GlobalTheory.BigTop.Fun.rankV_lt_gap (D := D) i.2 j.2
    have e := (ranks_exact D i j).2.2
    have h3 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have : s ≤ gap D 1 := by omega
    exact (by exact_mod_cast this : (s : ℝ) ≤ gap D 1).trans hgb

  have hκ : ∀ τ, (kap D 1 i j s τ : ℝ) ≤ 5 * large₂.sc.b := by
    intro τ
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hR.size τ j.2
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hR.size τ (i := D.R.m - i) (by omega) (by omega)
    have h : (kap D 1 i j s τ : ℤ) ≤ (num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) := by
      unfold kap; omega
    have h' : ((kap D 1 i j s τ : ℤ) : ℝ) ≤ ((num D 1 τ).e (j + 1) : ℝ) + (cen D 1 τ (D.R.m - i) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have hd1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hdb : (D.host.d : ℝ) ≤ large₂.sc.b := by
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by omega)
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm1 hf1) (one_le_pow₀ hN)
    exact (le_mul_of_one_le_left (by linarith) h1).trans hmfNd
  have hlogd : Real.log D.host.d ≤ large₂.sc.L := hbL ▸ Real.log_le_log (by linarith) hdb
  have hlogd0 : 0 ≤ Real.log D.host.d := Real.log_nonneg hd1
  have hdl : |large₂.logDerivativeAtOne| ≤ large₂.sc.L := hR.dlog

  have hdF : |(discr (maximalRealSubfield D.host.E) : ℝ)| = (2 * D.host.v) ^ D.R.f := by
    rw [← hR.hF]; exact GlobalTheory.CovDom.NormConst.abs_discr_F D
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  have hdF0 : 0 < |(discr (maximalRealSubfield D.host.E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hlogdF : Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ (D.R.f : ℝ) * large₂.sc.L := by
    rw [hdF, Real.log_pow, h2v]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

  have hC := log_cmConst_le |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) hdF0 hd1
    (by omega)
  have hC0 : C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) =
      Formalism.PairingDivisionLocalBalance.cmConst |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) := rfl
  rw [hC0]
  set b := large₂.sc.b
  set L := large₂.sc.L
  set F : ℝ := (D.R.f : ℝ) with hF
  have hb0 : 0 ≤ b := by linarith
  have hk : ((2 * s : ℕ) : ℝ) ≤ 2 * b := by push_cast; linarith
  have hk1 : (1 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s by omega)

  have T1 : (((2 * s : ℕ) : ℝ) - 1) / 2 * Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ 2 * (F * b * L) := by
    have a1 : 0 ≤ (((2 * s : ℕ) : ℝ) - 1) / 2 := by linarith
    have a2 := mul_le_mul_of_nonneg_left hlogdF a1
    have a3 : (((2 * s : ℕ) : ℝ) - 1) / 2 ≤ b := by linarith
    have a4 : 0 ≤ F * L := by positivity
    have a5 := mul_le_mul_of_nonneg_right a3 a4
    nlinarith

  have T2 : ∑ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (F * b * L) := by
    have each : ∀ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (b * L) := by
      intro τ
      have e : ((2 * s : ℕ) : ℝ) + kap D 1 i j s τ = ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have hn1 : 1 ≤ 2 * s + kap D 1 i j s τ := by omega
      refine (log_gamma_nat_le _ hn1).trans ?_
      have hn : ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * b := by push_cast; linarith [hκ τ]
      have hn0 : (1 : ℝ) ≤ ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by exact_mod_cast hn1
      have hl0 : 0 ≤ Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := Real.log_nonneg hn0
      have hl : Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * L := by
        have l1 := Real.log_le_log (by linarith) hn
        rw [Real.log_mul (by norm_num) (by linarith), hbL] at l1
        have l2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
        linarith
      have := mul_le_mul hn hl hl0 (by linarith)
      linarith
    refine (Finset.sum_le_sum fun τ _ => each τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith

  have hsumκ : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) ≤ 5 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.absK
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hκ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith
  have hsumκ0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) := Nat.cast_nonneg _
  have T3 : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) * 8 ≤ 40 * (F * b * L) := by
    have : F * b ≤ F * b * L := le_mul_of_one_le_right (by positivity) hL1
    linarith

  have hM : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) ≤ 12 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.wtM
    push_cast
    rw [hcard]
    have : (2 * (s : ℝ)) * F ≤ 2 * b * F := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    push_cast at hsumκ
    linarith
  have T4 : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ 12 * (F * b * L) := by
    have a1 : (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 ≤ L := by linarith
    have a2 : 0 ≤ (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 := by positivity
    have := mul_le_mul hM a1 a2 (by positivity)
    linarith
  have hfin : 0 ≤ F * b * Real.log large₂.sc.x := by positivity
  unfold bTH
  rw [hbL]
  have e : 200 * (D.R.f : ℝ) * b * (L + Real.log large₂.sc.x) = 200 * (F * b * L) + 200 * (F * b * Real.log large₂.sc.x) := by
    rw [hF]; ring
  rw [e]
  have hP : 0 ≤ F * b * L := by positivity
  linarith

end GlobalTheory.SizesArch
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBoundStatement

section

@[expose] public section

open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.log_cmConstant_add_logDerivative_le_squareTopBound : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x → Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ bTH D Cx large₂.sc.x large₂.sc.b := by
  first | exact @GlobalTheory.SizesArch.sizes | exact GlobalTheory.SizesArch.sizes | (intros; apply GlobalTheory.SizesArch.sizes <;> assumption)
end
end
