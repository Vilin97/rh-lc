module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LenEqLenI
public import Formalism.HermitianCurvature.StatementFr
public import Mathlib.Analysis.Complex.Exponential
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddPowLeExp

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

section real

theorem pratio (s : Finset ℕ) (lam : ℕ → ℝ) (α β y : ℝ) (hI : 3 ≤ β - α)
    (hroot : ∀ t ∈ s, -lam t < α ∨ β < -lam t) (hy1 : α + (β - α) / 3 ≤ y) (hy2 : y + 1 ≤ β - (β - α) / 3) :
    |∏ t ∈ s, (y + lam t)| ≤ (1 + 3 / (β - α)) ^ s.card * |∏ t ∈ s, (y + 1 + lam t)| := by
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t ht => ?_
  have hI0 : 0 < β - α := by linarith
  have h3 : 0 ≤ 3 / (β - α) := by positivity
  rcases hroot t ht with h | h
  · have a1 : 0 < y + lam t := by linarith
    rw [abs_of_pos a1, abs_of_pos (by linarith : 0 < y + 1 + lam t)]
    nlinarith
  · have a2 : y + 1 + lam t < 0 := by linarith
    rw [abs_of_neg (by linarith : y + lam t < 0), abs_of_neg a2]
    have : 1 ≤ 3 / (β - α) * -(y + 1 + lam t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI0]; linarith
    nlinarith

theorem long_bound (k r N Cc I : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hN : 20 ≤ N) (hCc : 1 ≤ Cc)
    (h : Cc * (k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ I) : 6 * (k + 2 * r + 1) ≤ I := by
  have hb : 0 ≤ k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 := by positivity
  have h1 : k * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3 ≤ I := by nlinarith
  have h2 : 6 * k ≤ k * N * (r + 1) ^ 2 := by
    have : 20 ≤ N * (r + 1) ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * (2 * r + 1) ≤ N ^ 2 * (r + 1) ^ 2 := by
    have : 400 ≤ N ^ 2 := by nlinarith
    nlinarith
  have h4 : 0 ≤ N ^ 3 := by positivity
  linarith

theorem three_le_len (N I : ℝ) (hN : 20 ≤ N) (h : 6 * N ^ 3 + 6 * N ≤ I) : 3 ≤ I := by
  have : 0 ≤ 6 * N ^ 3 := by positivity
  linarith

theorem two_N_bound (N : ℝ) (hN : 20 ≤ N) : 0 < N ^ 2 - 1 ∧ ((2 : ℕ) : ℝ) * (N / (N ^ 2 - 1)) ≤ 1 / 2 := by
  have hpos : 0 < N ^ 2 - 1 := by nlinarith
  refine ⟨hpos, ?_⟩
  rw [Nat.cast_ofNat, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem final_cmp (Pa x0 F q TT sA E1 qw : ℝ) (hPa : 0 ≤ Pa) (hx0 : 0 < x0) (hF0 : 0 < F) (hq : 0 < q) (hTT : 0 < TT)
    (hsA : 0 ≤ sA) (hE1 : 0 < E1) (hE1sq : E1 ^ 2 = Real.exp 1) (hP2 : Pa ^ 2 ≤ E1 * (sA ^ 2 * q))
    (hx : x0 ^ 2 ≤ q / TT) (hF : F ^ 2 ≤ E1) (hqw : E1⁻¹ * q ≤ qw) :
    Pa ≤ Real.exp 1 * sA * (√TT)⁻¹ * (qw / (x0 * F)) := by
  have hsq : (√TT)⁻¹ ^ 2 = TT⁻¹ := by rw [inv_pow, Real.sq_sqrt hTT.le]
  have hsq0 : 0 < (√TT)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hTT)
  have hmain : Pa * (x0 * F) ≤ E1 * sA * (√TT)⁻¹ * q := by
    have hl0 : 0 ≤ Pa * (x0 * F) := mul_nonneg hPa (mul_pos hx0 hF0).le
    have hr0 : 0 ≤ E1 * sA * (√TT)⁻¹ * q := mul_nonneg (mul_nonneg (mul_nonneg hE1.le hsA) hsq0.le) hq.le
    rw [← pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero]
    have eL : (Pa * (x0 * F)) ^ 2 = Pa ^ 2 * x0 ^ 2 * F ^ 2 := by ring
    have eR : (E1 * sA * (√TT)⁻¹ * q) ^ 2 = E1 * (sA ^ 2 * q) * (q / TT) * E1 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]; field_simp
    rw [eL, eR]
    calc Pa ^ 2 * x0 ^ 2 * F ^ 2 ≤ E1 * (sA ^ 2 * q) * x0 ^ 2 * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * F ^ 2 := by gcongr
      _ ≤ E1 * (sA ^ 2 * q) * (q / TT) * E1 := by gcongr
  have hC : Real.exp 1 * sA * (√TT)⁻¹ * (E1⁻¹ * q) = E1 * sA * (√TT)⁻¹ * q := by
    rw [← hE1sq]; field_simp
  have hfin : Pa * (x0 * F) ≤ Real.exp 1 * sA * (√TT)⁻¹ * qw := by
    rw [← hC] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left hqw ?_)
    positivity
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hx0 hF0)]
  exact hfin

theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

end real

section xs

theorem xs_eq_prod {S : Type} [Fintype S] [DecidableEq S] (x0 : ℂ → ℂ) :
    ∀ (L : List (Wd.Letter ℂ S)) (e : Wd.Ix S) (Y : ℂ),
      Fr.xs x0 L e Y = x0 Y * (L.map fun l => if e l.intersection_update_fsHerm_neg_one = 0 then Fr.phiL l Y else 1).prod
  | [], _, _ => by simp [Fr.xs]
  | l :: L, e, Y => by
    simp only [Fr.xs, List.map_cons, List.prod_cons]
    rw [xs_eq_prod x0 L e Y]
    ring

theorem phiL_bound (b : Bool) (pt y D : ℝ) (hD : 2 ≤ D) (hd : D + 2 ≤ |y - pt|) :
    0 < (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ∧
      (if b then (y + 1 - pt) / (y - pt) else (pt - y - 1) / (pt - y - 2)) ≤ 1 + 1 / D := by
  have hD0 : 0 < D := by linarith
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : pt - y - 2 < 0 := by linarith
      have h2 : pt - y - 1 < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h1
      · rw [div_le_iff_of_neg h1]
        have : 0 < 1 / D := by positivity
        nlinarith
    · rw [abs_of_neg h] at hd
      have h1 : 0 < pt - y - 2 := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (pt - y - 2) = pt - y - 2 + (pt - y - 2) / D := by ring
        rw [e1]
        have : 1 ≤ (pt - y - 2) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
  · simp only [if_true]
    rcases le_or_gt 0 (y - pt) with h | h
    · rw [abs_of_nonneg h] at hd
      have h1 : 0 < y - pt := by linarith
      constructor
      · exact div_pos (by linarith) h1
      · rw [div_le_iff₀ h1]
        have e1 : (1 + 1 / D) * (y - pt) = y - pt + (y - pt) / D := by ring
        rw [e1]
        have : 1 ≤ (y - pt) / D := by rw [le_div_iff₀ hD0]; linarith
        linarith
    · rw [abs_of_neg h] at hd
      have h2 : y + 1 - pt < 0 := by linarith
      constructor
      · exact div_pos_of_neg_of_neg h2 h
      · rw [div_le_iff_of_neg h]
        have : 0 < 1 / D := by positivity
        nlinarith

end xs

end

end Formalism.FourierDecayAlt.P.PBL
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

open Classical

theorem topRatio : TopRatio := by
  intro Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB hC v w y hcut hgr hlen hfar e ρ
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, hOkp, hw, hw', hl1, hlk, hne, hGo, -, hLC, hCA, -, hv⟩ := hB'
  have hOK : (D.parOf S v).OK := (p v).hP.1
  have hN20 : (20 : ℝ) ≤ S.Ntop := PBD.ntop_ge S
  set N : ℝ := (S.Ntop : ℝ) with hNdef
  set α := S.cutLo v with hα
  set β := S.cutHi v with hβ

  have hycut : I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) y := PBF.cutWord_mem (D.parOf S v) hcut (List.mem_cons_self)
  obtain ⟨m, hm⟩ := hgr
  obtain ⟨hlenI, hpos, -, -, -, hlast⟩ := hGo v
  obtain ⟨hm1, hmN, hgl, hgu⟩ := hpos m y hm
  obtain ⟨hyI, hy1I, hPy, hPy1⟩ := hlast y (Or.inl ⟨m, hm⟩)
  have hI0 : 0 < β - α := by
    have : (0 : ℝ) < 6 * N ^ 3 + 6 * N := by positivity
    linarith
  have hmid1 : α + (β - α) / 3 ≤ y := by
    unfold C.gridL at hgl
    have : 0 ≤ (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) := by
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact mul_nonneg (by linarith) (by positivity)
    linarith
  have hmid2 : y + 1 ≤ β - (β - α) / 3 := by
    unfold C.gridL at hgu
    have hmN' : (m : ℝ) ≤ S.Ntop := by exact_mod_cast hmN
    have hN0 : (0 : ℝ) < S.Ntop := by linarith
    have h6 : (2 * (m : ℝ) - 2) * ((β - α) / (6 * S.Ntop)) + (β - α) / (6 * S.Ntop) ≤ (β - α) / 3 := by
      have hX : 0 ≤ (β - α) / (6 * S.Ntop) := by positivity
      have e2 : (2 * (S.Ntop : ℝ)) * ((β - α) / (6 * S.Ntop)) = (β - α) / 3 := by field_simp; ring
      have := mul_le_mul_of_nonneg_right (show 2 * (m : ℝ) - 1 ≤ 2 * S.Ntop by linarith) hX
      nlinarith
    linarith

  have hyIcc : y ∈ Set.Icc α β := by rw [hα, hβ, ← cutI_eq]; exact hyI
  have hqy : 0 < (M.qC (D.parOf S v) (y : ℂ)).re := q_pos_cut hB v y hyIcc
  set q' : ℝ → ℝ := fun t => (M.qC (D.parOf S v) (t : ℂ)).re with hq'
  set wr : List (Wd.Letter ℝ (Fin w.length)) :=
    (D.positionted w).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin w.length)) with hwr
  have hQ : Wd.qw (M.qC (D.parOf S v)) (D.positionted w) (y : ℂ) = ((Wd.qw q' wr y : ℝ) : ℂ) :=
    weighted_quadratic_of_real (Fin w.length) (M.qC (D.parOf S v)) (D.positionted w) y
      (by rw [PBF.qC_ofReal, Complex.ofReal_im])
      (by intro l hl; unfold D.positionted at hl; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl; simp)
  have hLQ : Real.exp (-(1 / 2)) ≤ Wd.qw q' wr y / q' y := by
    have h4 : 4 ≤ S.Ntop := by exact_mod_cast (by linarith : (4 : ℝ) ≤ S.Ntop)
    have hlen' : wr.length ≤ S.Ntop := by simp [hwr, D.positionted]; omega
    refine (lemma_Q_estimate (Fin w.length) q' wr S.Ntop ((S.Ntop : ℝ) ^ 2 + 1) y h4 hlen' le_rfl ?_ hqy.ne').1
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    unfold D.positionted at hl0
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl0
    have hz := hfar (w.get j) (List.get_mem _ _)
    simp only [Complex.ofReal_re]
    by_cases h1 : (w.get j).1 = true
    · rw [if_pos h1]; exact hz.1
    · rw [if_neg h1]; exact ⟨hz.1, hz.2 (by simpa using h1)⟩
  have hqw : 0 < Wd.qw q' wr y := by
    have := (le_div_iff₀ hqy).1 hLQ
    have : 0 < Real.exp (-(1 / 2)) * q' y := mul_pos (Real.exp_pos _) hqy
    linarith

  set rf : Fin w.length → ℝ := fun j => if e j = 0 then
      (if (w.get j).1 then (y + 1 - (w.get j).2) / (y - (w.get j).2)
        else ((w.get j).2 - y - 1) / ((w.get j).2 - y - 2)) else 1 with hrf
  have hxs : Fr.xs (fun Y => M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ Y) (D.positionted w) e ((y : ℂ) + 1) =
      (M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1)) * ((∏ j, rf j : ℝ) : ℂ) := by
    rw [xs_eq_prod]
    congr 1
    unfold D.positionted
    rw [List.map_ofFn, List.prod_ofFn]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      unfold Fr.phiL
      by_cases hb : (w.get j).1 = true
      · simp only [hb, if_true]; push_cast; ring
      · simp only [hb, Bool.false_eq_true, if_false]; push_cast; ring
    · simp only [he, if_false, Complex.ofReal_one]
  set x0r : ℝ := (-1 : ℝ) ^ (S.G.k - (S.l + 1)) * I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) with hx0r
  have hx0 : M.sgn (D.parOf S v) (S.l + 1) * M.xC (D.parOf S v) ρ ((y : ℂ) + 1) = ((x0r : ℝ) : ℂ) := by
    simp only [hx0r, M.sgn, M.xC, I.xpoly, D.parOf]
    push_cast
    rfl
  have hinter := Formalism.FourierDecayAlt.P.types_interlace (D.parOf S v) hOK ρ
  have hx0pos : 0 < x0r := Formalism.FourierDecayAlt.P.interlacing_sign S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ) (S.l + 1) y (by omega)
    (by omega) hinter hycut 1 (by simp)
  have hD2 : (2 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 - 1 := by nlinarith
  have hrf : ∀ j, 0 < rf j ∧ rf j ≤ 1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by
    intro j
    simp only [hrf]
    by_cases he : e j = 0
    · simp only [he, if_true]
      exact phiL_bound (w.get j).1 (w.get j).2 y _ hD2 (by linarith [(hfar (w.get j) (List.get_mem _ _)).1])
    · simp only [he, if_false]
      exact ⟨one_pos, by have : (0 : ℝ) ≤ 1 / ((S.Ntop : ℝ) ^ 2 - 1) := by positivity
                         linarith⟩
  have hF0 : 0 < ∏ j, rf j := Finset.prod_pos fun j _ => (hrf j).1
  have hF1 : ∏ j, rf j ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
    calc ∏ j, rf j ≤ ∏ _j : Fin w.length, (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) :=
          Finset.prod_le_prod₀ (fun j _ => (hrf j).1.le) fun j _ => (hrf j).2
      _ = (1 + 1 / ((S.Ntop : ℝ) ^ 2 - 1)) ^ w.length := by simp
      _ ≤ Real.exp (w.length * (1 / ((S.Ntop : ℝ) ^ 2 - 1))) := one_add_pow_le_exp _ (by positivity) _
      _ ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) := by
          apply Real.exp_le_exp.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right _ (by linarith)
          exact_mod_cast hlen.le

  have hR : topR (S.l + 1) w e ρ y = ((Wd.qw q' wr y / (x0r * ∏ j, rf j) : ℝ) : ℂ) := by
    unfold topR
    rw [hQ, hxs, hx0]
    push_cast
    ring
  rw [hR, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨div_pos hqw (mul_pos hx0pos hF0), rfl, ?_⟩
  set C0 := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (√(S.T * S.T'))⁻¹ with hC0
  set F := ∏ j, rf j with hFdef
  set Cf := S.G.place (S.pl v) with hCf
  have hT : 0 < S.T := hOK.T_pos
  have hT' : 0 < S.T' := hOK.T'_pos
  have hTT : 0 < S.T * S.T' := mul_pos hT hT'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hsA := supA_nonneg S hg hk v false

  have hIR := Formalism.FourierDecayAlt.P.interlacing_ratio S.G.k (D.parOf S v).u (D.parOf S v).u' (M.rho (D.parOf S v) ρ)
    (S.l + 1) y (by omega) (by omega) hinter hycut
  have hul : 1 ≤ |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| := by
    rcases hycut with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; nlinarith
    · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]; nlinarith
  have hqprod : q' y = -(S.T * S.T') * ((∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) *
      ∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) := by
    simp only [hq']
    rw [PBF.qC_ofReal, Complex.ofReal_re, ← Finset.prod_mul_distrib]
  have hx0sq : x0r ^ 2 ≤ q' y / (S.T * S.T') := by
    have e1 : x0r ^ 2 = I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) ^ 2 := by
      rw [hx0r, mul_pow, ← pow_mul, mul_comm (S.G.k - (S.l + 1)) 2, pow_mul, neg_one_sq, one_pow, one_mul]
    have hq := hqy
    change 0 < q' y at hq
    rw [hqprod] at hq
    rw [e1, le_div_iff₀ hTT, hqprod]
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u i)) = A at hq hIR ⊢
    generalize (∏ i ∈ Icc 1 S.G.k, (y + 1 / 2 + (D.parOf S v).u' i)) = B at hq hIR ⊢
    generalize I.xpoly S.G.k (M.rho (D.parOf S v) ρ) (y + 1) = X at hIR ⊢
    generalize |y + 1 / 2 + (D.parOf S v).u (S.l + 1)| * |y + 1 / 2 + (D.parOf S v).u' (S.l + 1)| = U at hIR hul
    have hAB : A * B < 0 := by
      by_contra h
      push_neg at h
      have h3 := mul_nonneg hTT.le h
      have h4 : -(S.T * S.T') * (A * B) = -(S.T * S.T' * (A * B)) := by ring
      linarith
    rw [abs_of_neg hAB] at hIR
    have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
    have h1 : X ^ 2 ≤ -(A * B) :=
      calc X ^ 2 = X ^ 2 * 1 := (mul_one _).symm
        _ ≤ X ^ 2 * U := mul_le_mul_of_nonneg_left hul hX2
        _ ≤ -(A * B) := hIR
    have h5 := mul_le_mul_of_nonneg_left h1 hTT.le
    have h6 : -(S.T * S.T') * (A * B) = S.T * S.T' * -(A * B) := by ring
    rw [h6, mul_comm (X ^ 2)]
    exact h5

  have hroot : ∀ t ∈ Icc 1 (Cf.k + Cf.m - 1), -Cf.lam t < α ∨ β < -Cf.lam t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hmem : -Cf.lam t ∈ Cf.cutI S.l := by rw [hCf, cutI_eq]; exact ⟨hcon.1, hcon.2⟩
    have hfac := (Formalism.FourierDecayAlt.P.betaFactorisation Cf S.de S.de' S.G.ka S.T S.T' (-Cf.lam t) S.l (hOkp v)
      hw hw' hT hT' hl1 hlk hne hmem).2.1
    apply hfac
    unfold Sz.Cfg.P
    exact Finset.prod_eq_zero ht (by ring)
  have hI3 : 3 ≤ β - α := three_le_len _ _ hN20 hlenI
  have hPr := pratio (Icc 1 (Cf.k + Cf.m - 1)) Cf.lam α β y hI3 hroot hmid1 hmid2
  have hPy : S.P v y = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + Cf.lam t) := rfl
  have hPy1 : S.P v (y + 1) = ∏ t ∈ Icc 1 (Cf.k + Cf.m - 1), (y + 1 + Cf.lam t) := rfl
  rw [← hPy, ← hPy1, Nat.card_Icc] at hPr
  have hn6 : 6 * ((Cf.k + Cf.m - 1 + 1 - 1 : ℕ) : ℝ) ≤ β - α := by
    have hLv := hLC v
    have hCc1 : 1 ≤ Cc := by linarith [Real.add_one_le_exp 1]
    have hm : Cf.m = 2 * S.G.r + 2 := rfl
    have hkk : Cf.k = S.G.k := rfl
    rw [hm, hkk]
    have hk1 : 1 ≤ S.G.k := by omega
    push_cast [show S.G.k + (2 * S.G.r + 2) - 1 + 1 - 1 = S.G.k + 2 * S.G.r + 1 by omega]
    have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have hkR : (1 : ℝ) ≤ S.G.k := by exact_mod_cast hk1
    have := long_bound (S.G.k : ℝ) (S.G.r : ℝ) (S.Ntop : ℝ) Cc (β - α) hkR hr0 hN20 hCc1 hLv
    linarith

  set n := Cf.k + Cf.m - 1 + 1 - 1 with hn
  set E1 := Real.exp (1 / 2) with hE1
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE1sq : E1 ^ 2 = Real.exp 1 := by rw [hE1, ← Real.exp_nat_mul]; norm_num
  have hEinv : Real.exp (-(1 / 2)) = E1⁻¹ := by rw [hE1, Real.exp_neg]
  have hρP : (1 + 3 / (β - α)) ^ n ≤ E1 := by
    refine (one_add_pow_le_exp _ (by positivity) n).trans (Real.exp_le_exp.2 ?_)
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  have hF2 : F ^ 2 ≤ E1 := by
    have hN20' : (20 : ℝ) ≤ S.Ntop := hN20
    have h1 : F ^ 2 ≤ Real.exp ((S.Ntop : ℝ) / ((S.Ntop : ℝ) ^ 2 - 1)) ^ 2 := pow_le_pow_left₀ hF0.le hF1 2
    refine h1.trans ?_
    rw [← Real.exp_nat_mul, hE1]
    exact Real.exp_le_exp.2 (two_N_bound _ hN20').2

  have hyI' : y ∈ Cf.cutI S.l := hyI
  have hcore := core_le_supA hB v false y (by simpa using hyI')
  have hqeq : Cf.q S.de S.de' S.T S.T' y = q' y := (qC_re S v y).symm
  have hcore2 : |S.P v y * S.P v (y + 1)| = Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y := by
    unfold Sz.Cfg.core
    rw [Real.sq_sqrt (abs_nonneg _), hqeq, abs_div, abs_of_pos hqy]
    have hPP : S.P v y * S.P v (y + 1) = Cf.P y * Cf.P (y + 1) := rfl
    rw [hPP, div_mul_cancel₀ _ hqy.ne']
  have hcore0 : 0 ≤ Cf.core S.de S.de' S.T S.T' y := Real.sqrt_nonneg _
  have hP2 : S.P v y ^ 2 ≤ E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
    have h1 : S.P v y ^ 2 = |S.P v y| * |S.P v y| := by rw [sq, abs_mul_abs_self]
    have h2 : |S.P v y| * |S.P v y| ≤ |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) :=
      mul_le_mul_of_nonneg_left hPr (abs_nonneg _)
    have h3 : |S.P v y| * ((1 + 3 / (β - α)) ^ n * |S.P v (y + 1)|) =
        (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) := by
      rw [← hcore2, abs_mul]; ring
    have h4 : Cf.core S.de S.de' S.T S.T' y ^ 2 ≤ J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 :=
      pow_le_pow_left₀ hcore0 hcore 2
    have h5 : (1 + 3 / (β - α)) ^ n * (Cf.core S.de S.de' S.T S.T' y ^ 2 * q' y) ≤
        E1 * (J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) ^ 2 * q' y) := by
      exact mul_le_mul hρP (mul_le_mul_of_nonneg_right h4 hqy.le) (mul_nonneg (pow_nonneg hcore0 2) hqy.le) hE1pos.le
    calc S.P v y ^ 2 = |S.P v y| * |S.P v y| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h5
  have hqw2 : E1⁻¹ * q' y ≤ Wd.qw q' wr y := by rw [← hEinv]; exact (le_div_iff₀ hqy).1 hLQ
  exact final_cmp |S.P v y| x0r F (q' y) (S.T * S.T') _ E1 (Wd.qw q' wr y) (abs_nonneg _) hx0pos hF0 hqy hTT
    hsA hE1pos hE1sq (by rw [sq_abs]; exact hP2) hx0sq hF2 hqw2

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_ratio : Formalism.FourierDecayAlt.P.PBL.TopRatio := Formalism.FourierDecayAlt.P.PBL.topRatio
end
end
