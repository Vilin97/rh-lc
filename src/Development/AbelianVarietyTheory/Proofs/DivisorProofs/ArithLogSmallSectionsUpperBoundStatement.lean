module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeAddMulLogSqOfLeAddMulLog

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBoundStatement

section

@[expose] public section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  first | exact @GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | exact GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | (intros; apply GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  first | exact @GlobalTheory.HSNef.smallFam_pair_tens | exact GlobalTheory.HSNef.smallFam_pair_tens | (intros; apply GlobalTheory.HSNef.smallFam_pair_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithLogSmallSectionsUpperBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := GlobalTheory.T.nef_hermitian_small_sections_key_inequality hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  exact GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithLogSmallSectionsUpperBoundStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arith_log_small_sections_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  first | exact @GlobalTheory.HSNef.lc_le_bound | exact GlobalTheory.HSNef.lc_le_bound | (intros; apply GlobalTheory.HSNef.lc_le_bound <;> assumption)
end
end
