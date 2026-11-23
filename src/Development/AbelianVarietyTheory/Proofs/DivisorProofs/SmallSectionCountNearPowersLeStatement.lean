module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Mathlib.Analysis.SpecificLimits.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfPolyAsymptotics

section

@[expose] public section

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory

theorem eventually_le_of_poly_asymptotics :
    ∀ (d b : ℕ) (f : ℝ → ℕ → ℝ) (g : ℕ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        g ((b * n + 1) * m) ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by
  intro d b f g α β _hd hb hf hg ε hε
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ d := pow_pos hbR d
  obtain ⟨η, θ, hη, hθ, key⟩ : ∃ η θ : ℝ, 0 < η ∧ 0 < θ ∧ (β * η + 2 * θ) * (b : ℝ) ^ d < ε := by
    generalize (b : ℝ) ^ d = c at hc ⊢
    have hβ1 : (0 : ℝ) < |β| + 1 := by positivity
    refine ⟨ε / (4 * c * (|β| + 1)), ε / (8 * c), div_pos hε (by positivity),
      div_pos hε (by positivity), ?_⟩
    have e1 : (|β| + 1) * (ε / (4 * c * (|β| + 1))) * c = ε / 4 := by
      field_simp
    have e2 : ε / (8 * c) * c = ε / 8 := by
      field_simp
    have h1 : β * (ε / (4 * c * (|β| + 1))) * c ≤ |β| * (ε / (4 * c * (|β| + 1))) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self β)
        (div_pos hε (by positivity)).le) hc.le
    have h2 : 0 < ε / (4 * c * (|β| + 1)) * c := mul_pos (div_pos hε (by positivity)) hc
    nlinarith
  set A : ℝ := α + β * η + θ with hAdef
  set B : ℝ := α - θ with hBdef
  have hlim : Tendsto (fun n : ℕ => A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) atTop (𝓝 (A * (b : ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul A
    simpa using this
  have hn : ∀ᶠ n : ℕ in atTop, A * ((b : ℝ) + 1 / (n : ℝ)) ^ d < B * (b : ℝ) ^ d + ε :=
    (tendsto_order.1 hlim).2 _ (by rw [hAdef, hBdef]; nlinarith)
  have hAe : ∀ᶠ j : ℕ in atTop, f η j / (j : ℝ) ^ d < A :=
    (tendsto_order.1 (hf η hη.le)).2 A (by rw [hAdef]; linarith)
  have hBe : ∀ᶠ j : ℕ in atTop, B < f 0 j / (j : ℝ) ^ d :=
    (tendsto_order.1 (hf 0 le_rfl)).1 B (by rw [hBdef, mul_zero, add_zero]; linarith)
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hk : Tendsto (fun m : ℕ => (b * n + 1) * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos _)) tendsto_id
  have hk' : Tendsto (fun m : ℕ => b * n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.mul_pos hb hn1)) tendsto_id
  filter_upwards [hk.eventually (hAe.and (hg η hη)), hk'.eventually hBe, eventually_gt_atTop 0]
    with m ⟨hA1, hG1⟩ hB1 hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (((b * n + 1) * m : ℕ) : ℝ) = ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * m) := by
    push_cast
    rw [show ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * (m : ℝ))
        = (b : ℝ) * n * m + ((n : ℝ)⁻¹ * (n : ℝ)) * m by ring, inv_mul_cancel₀ hnR.ne']
    ring
  have hj' : ((b * n * m : ℕ) : ℝ) = (b : ℝ) * ((n : ℝ) * m) := by push_cast; ring
  have hjpos : (0 : ℝ) < (((b * n + 1) * m : ℕ) : ℝ) := by
    rw [hj]; positivity
  have hj'pos : (0 : ℝ) < ((b * n * m : ℕ) : ℝ) := by
    rw [hj']; positivity
  have hnm : (0 : ℝ) < ((n : ℝ) * m) ^ d := pow_pos (mul_pos hnR hmR) d
  have hA2 := (div_lt_iff₀ (pow_pos hjpos d)).1 hA1
  have hB2 := (lt_div_iff₀ (pow_pos hj'pos d)).1 hB1
  calc g ((b * n + 1) * m) ≤ f η ((b * n + 1) * m) := hG1
    _ ≤ A * ((((b * n + 1) * m : ℕ) : ℝ)) ^ d := hA2.le
    _ = (A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) * ((n : ℝ) * m) ^ d := by rw [hj, mul_pow]; ring
    _ ≤ (B * (b : ℝ) ^ d + ε) * ((n : ℝ) * m) ^ d := mul_le_mul_of_nonneg_right hn.le hnm.le
    _ = B * (((b * n * m : ℕ) : ℝ)) ^ d + ε * ((n : ℝ) * m) ^ d := by rw [hj', mul_pow]; ring
    _ ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLe

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.smallSectionCount_nearPowers_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_two_le_lc_one_add | exact GlobalTheory.VolBr.lc_two_le_lc_one_add | (intros; apply GlobalTheory.VolBr.lc_two_le_lc_one_add <;> assumption)
end
end
