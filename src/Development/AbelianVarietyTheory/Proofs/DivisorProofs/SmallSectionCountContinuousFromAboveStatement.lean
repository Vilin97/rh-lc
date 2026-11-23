module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLeStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
    have hm := (GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  first | exact @GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | exact GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | (intros; apply GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPowStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.isNef_pow_of_isNef : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  first | exact @GlobalTheory.NefPow.isNef_pow | exact GlobalTheory.NefPow.isNef_pow | (intros; apply GlobalTheory.NefPow.isNef_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := GlobalTheory.T.isNef_pow_of_isNef hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPairStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.smallSectionCount_le_pow_goodPair : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.crude_upper_lc | exact GlobalTheory.VolBr.crude_upper_lc | (intros; apply GlobalTheory.VolBr.crude_upper_lc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAbove

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_add_le_of_mul_le (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  apply _root_.GlobalTheory.HSNef.log_add_log_le_of_mul_le_mul <;> assumption

theorem lc_add_A_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField),
    P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hD P b s t hG ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := fun a c R =>
    GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hD P b s t hG a c R hAC
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.smallSectionCount_le_pow_goodPair hHS hAC k X p D hD P b s t hG
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) 0) (fun N => P.Bl (N : ℤ) 0) (D + 1)
    (Nat.succ_pos D) (fun N => hball N 0) (fun N R => hfin N 0 R) C0 hC0 (ε / 3) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section k X p D hD P s hG.s_mem.1 hG.s_ne (δ / 2) (by positivity)
  have hdA := GlobalTheory.T.smallSectionCount_nearPowers_le hHS hAC k X p D hD P b s t hG (ε / 3) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, (2 * C + 2) / δ ≤ (n : ℝ) ∧ 1 ≤ n :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (eventually_ge_atTop 1)
  filter_upwards [hdA, hn] with n hdAn hnn
  obtain ⟨hnC, hn1⟩ := hnn
  have htend : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn1) tendsto_id
  filter_upwards [hdAn, htend.eventually hrad, eventually_ge_atTop 1] with m hdm hradm hm1
  have hnδ : 2 * C + 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1

  have hrad_le : 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)
        ≤ Real.exp 1 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hnδ (by linarith : (0 : ℝ) ≤ m)]
  have hSsub : {f | f ∈ P.H (n * m : ℕ) 0 ∧ f * s ^ m ∈ P.Bl (n * m : ℕ) m 2} ⊆
      P.Bl (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv (n * m) m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level k X p D hD P b s t hG (n * m) m (hfin _ _ _)
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  norm_cast at hlev
  have hkey := log_add_le_of_mul_le _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one) hlev
    (Set.ncard_le_ncard hSsub hEfin)
  have hX : (0 : ℝ) ≤ ((n : ℝ) * m) ^ (D + 1) := by positivity
  have hX3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 3) hX
  simp only [Pair.lc] at hdm ⊢
  push_cast at hradm hkey hdm ⊢
  linarith

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAboveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.small_section_count_continuous_from_above : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_add_A_le | exact GlobalTheory.VolBr.lc_add_A_le | (intros; apply GlobalTheory.VolBr.lc_add_A_le <;> assumption)
end
end
