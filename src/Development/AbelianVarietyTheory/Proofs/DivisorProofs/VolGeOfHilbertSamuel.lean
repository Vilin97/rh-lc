module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensorStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAboveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBallStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePairStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_good_hermitian_lineBundle_pair : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField), P.L = L ∧ P.Good D b s t := by
  first | exact @GlobalTheory.VolBr.exists_good_pair | exact GlobalTheory.VolBr.exists_good_pair | (intros; apply GlobalTheory.VolBr.exists_good_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLower

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem le_arVol_of_frequently_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  intro k _ X _ p D L a h
  have hc : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have key : ∀ δ : ℝ, 0 < δ → ((a - δ : ℝ) : EReal) ≤ arVol L D := by
    intro δ hδ
    refine Filter.le_limsup_of_frequently_le ?_
    have hε : 0 < δ / ((D + 1).factorial : ℝ) := div_pos hδ hc
    refine ((h _ hε).and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro N ⟨⟨hfin, hle⟩, hN⟩
    have h0 : 0 < (L.pow N).smallSec.ncard := (Set.ncard_pos hfin).2 ⟨_, (L.pow N).zero_mem_smallSec⟩
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hNp]
    have e : (a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * ((D + 1).factorial : ℝ) = a - δ := by
      field_simp
    calc (a - δ) * (N : ℝ) ^ (D + 1)
        = ((a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * (N : ℝ) ^ (D + 1)) * ((D + 1).factorial : ℝ) := by
          rw [← e]; ring
      _ ≤ Real.log ((L.pow N).smallSec.ncard : ℝ) * ((D + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hle hc.le
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hz (not_lt.2 le_top)
  | coe r =>
    have hr : r < a := EReal.coe_lt_coe_iff.1 hz
    have := key (a - r) (by linarith)
    rwa [sub_sub_cancel] at this

end GlobalTheory.VolBr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLowerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  first | exact @GlobalTheory.VolBr.le_arVol_of_frequently_le | exact GlobalTheory.VolBr.le_arVol_of_frequently_le | (intros; apply GlobalTheory.VolBr.le_arVol_of_frequently_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGeStatement

section

@[expose] public section

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) / (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNef

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNefStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.log_card_smallSections_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | exact GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPowStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  first | exact @GlobalTheory.SelfInterGrowth.main | exact GlobalTheory.SelfInterGrowth.main | (intros; apply GlobalTheory.SelfInterGrowth.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolGeOfHilbertSamuel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.VolBr

theorem volGe_of_hilbertSamuel :
    GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.VolGe := by
  intro hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI
  obtain ⟨P, b, s, t, hPL, hG⟩ := GlobalTheory.T.exists_good_hermitian_lineBundle_pair hAC k X p D hX L
  subst hPL
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow hAC k X p D hX P.L P.A a hSI
  obtain ⟨hRL, hRA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  apply GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower k X p D P.L a
  intro ε hε
  have hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hε3 : 0 < ε / 3 := by positivity
  have hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1) :=
    hαlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hnα, hcont⟩ := ((eventually_ge_atTop 1).and
    (hlim.and (GlobalTheory.T.small_section_count_continuous_from_above hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists
  have hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hRL
    have h2 := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ 0 1 _ P.A h1 hRA
    simpa using h2
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef
  have hstep := GlobalTheory.T.log_card_smallSections_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨m, hm, hm1, hm2⟩ := ((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists
  have hmN : N₀ ≤ m := le_of_max_le_left hm
  refine ⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩
  have hsm := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P 1 0 P.L hRL 0 (n * m)).2.1
  rw [mul_one, mul_zero] at hsm
  have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC
  have hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard := by
    rw [Set.ncard_def, Set.ncard_def, hsm]
  refine ⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩
  rw [hnc]
  change _ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1
  have hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mul_one] at hm1
  set F : ℝ := ((D + 1).factorial : ℝ)
  set x : ℝ := (n : ℝ) ^ (D + 1) with hx
  set y : ℝ := (m : ℝ) ^ (D + 1) with hy
  have hx1 : 1 ≤ x := one_le_pow₀ (by exact_mod_cast hn1)
  have hy0 : 0 ≤ y := by positivity
  have hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y := by push_cast; rw [mul_pow]
  rw [mul_pow] at hm2
  rw [hN]
  have hαx : (a - ε / 3) * x ≤ α n := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα
    linarith
  have hF0 : 0 < F := by linarith
  have e1 : (a - ε / 3) * x * y / F ≤ α n / F * y := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le
  have e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y) :=
    div_le_self (by positivity) hF1
  have e3 : ε / 3 * y ≤ ε / 3 * (x * y) := by
    have : y ≤ x * y := le_mul_of_one_le_left hy0 hx1
    exact mul_le_mul_of_nonneg_left this hε3.le
  have e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y) := by
    field_simp
    ring
  linarith [e1, e2, e3, e4, hm1, hm2]

end GlobalTheory.VolBr
end
end
end
