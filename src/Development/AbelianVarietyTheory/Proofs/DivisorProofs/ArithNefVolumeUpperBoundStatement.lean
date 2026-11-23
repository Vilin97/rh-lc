module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithLogSmallSectionsUpperBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefAsymp

theorem tendsto_log_nat_div : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun m => ?_)
  simp

theorem tendsto_log_sq_div {X : ℕ → ℝ} {D : ℕ} {L : ℝ} (h1 : ∀ m, 1 ≤ X m)
    (hX : Tendsto (fun m : ℕ => X m / (m : ℝ) ^ (D + 1)) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => Real.log (X m ^ 2) / m) atTop (𝓝 0) := by
  set C : ℝ := max (L + 1) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C :=
    hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))
  have hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    have h2 := tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · refine Eventually.of_forall fun m => ?_
    exact div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    have hXle : X m ≤ C * (m : ℝ) ^ (D + 1) := by
      rw [div_lt_iff₀ hP] at hm; exact hm.le
    have hX0 : 0 < X m := lt_of_lt_of_le one_pos (h1 m)
    have hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m := by
      have := Real.log_le_log hX0 hXle
      rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at this
      push_cast at this
      linarith
    rw [Real.log_pow]
    rw [show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)
        = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]
    apply div_le_div_of_nonneg_right _ hm0.le
    push_cast
    linarith

theorem tendsto_bound_div (D q : ℕ) (hq : 3 ≤ q) {β g : ℕ → ℝ} {a γ : ℝ} (hβ0 : ∀ m, 0 ≤ β m)
    (hg0 : ∀ m, 0 ≤ g m) (hβ : Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a))
    (hg : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ)) :
    Tendsto (fun m : ℕ => bound D q (β m) (g m) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (Real.log q * (a / (((D + 1).factorial : ℝ) * Real.log ((q : ℝ) / 2))))) := by
  set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hΔ : 0 < Δ := Real.log_pos (by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hFΔ : 0 < F * Δ := mul_pos hF hΔ
  set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1
  have hc1p : 0 ≤ c1 := mul_nonneg (by positivity)
    (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))
  set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA
  set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB
  have hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2)) :=
    fun m => rfl
  have hinv := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hg.mul hinv
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ))) := by
    have := (hβ.add (hgP.const_mul c1)).div_const (F * Δ)
    rw [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)
  have hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have hA0 : ∀ m, 0 ≤ A m := fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le
  have hB0 : ∀ m, 0 ≤ B m := fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)
  have hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1 := fun m => by linarith [hA0 m, hB0 m]
  have hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1))) := by
    have := (hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hlog := tendsto_log_sq_div hX1 hXP
  have h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := ((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have := (hAP.add h2).const_mul (Real.log q)
  rw [add_zero] at this
  exact this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)

theorem eventually_le_of_bound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) →
    Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) →
    Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) →
    (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro D u β g a γ hβ0 hg0 hβ hg hu ε hε
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have ha : 0 ≤ a := ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))
  set K : ℝ := Real.log 2 * a / (F * ε) with hK
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.exp K)
  set q : ℕ := max n 3 with hqdef
  have hq3 : 3 ≤ q := le_max_right _ _
  have hqn : (n : ℝ) ≤ q := by exact_mod_cast le_max_left n 3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKΔ : K < Real.log ((q : ℝ) / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hΔ : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div hq0.ne' two_ne_zero]; ring
  have hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε := by
    have e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2)))
        = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) := by
      rw [hlogq]; field_simp
    rw [e]
    have h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε) := by
      rw [hK, div_lt_iff₀ (mul_pos hF hε)] at hKΔ; exact hKΔ
    have h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε := by
      rw [div_lt_iff₀ (mul_pos hF hΔ)]; nlinarith
    linarith
  have ht := tendsto_bound_div D q hq3 hβ0 hg0 hβ hg
  filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1
  have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm1) _
  rw [div_lt_iff₀ hP] at hm
  exact (hu m q hq3).trans hm.le

end GlobalTheory.HSNefAsymp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBoundStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.eventually_le_of_smallSectionLogCountUpperBound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) → Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) → Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) → (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNefAsymp.eventually_le_of_bound | exact GlobalTheory.HSNefAsymp.eventually_le_of_bound | (intros; apply GlobalTheory.HSNefAsymp.eventually_le_of_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmall

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef.BoxTwist

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_shift_tens (N M : HermLB p) (u : ℝ) :
    ((N.tens M).shift (fun _ => u) fun _ => rfl).Isometric (N.tens (M.shift (fun _ => u) fun _ => rfl)) :=
  HermLB.isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => (add_assoc _ _ _).symm

variable [IsIntegral X]

theorem isRatSec_const_mul {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (g : X.functionFieldˣ) :
    IsRatSec B fun i => g * r i := fun a b h => by
  beta_reduce
  rw [Units.val_mul, Units.val_mul, hr a b h]
  ring

theorem exists_pair_small (Q : Pair p) (W : HermLB p) (g : X.functionField) (hg : g ≠ 0) (u : ℝ) :
    ∃ P : Pair p, P.L = W ∧ P.A = Q.A.shift (fun _ => u) (fun _ => rfl) ∧
      ∀ f, g * f ∈ Q.Bl 0 1 (Real.exp u) → f ∈ P.Bl 0 1 1 := by
  obtain ⟨r, hr⟩ := exists_isRatSec W.isLB
  let P : Pair p := ⟨W, Q.A.shift (fun _ => u) (fun _ => rfl), r, fun j => Units.mk0 g hg * Q.r' j, hr,
    isRatSec_const_mul Q.hr' _⟩
  have e (f i i' j) : P.loc 0 1 f i j = Q.loc 0 1 (g * f) i' j := by
    simp only [Pair.loc, P, zpow_zero, zpow_one, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨P, rfl, rfl, fun f hf => ⟨fun x i j _ hj => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨i', hi'⟩ := exists_chart Q.L.isLB x
    rw [e f i i' j]
    exact hf.1 x i' j hi' hj
  · have h := hf.2 σ y
    have e' : P.nu 0 1 σ y f = Q.nu 0 1 σ y (g * f) * Real.exp (-u) := by
      rw [Pair.nu, Pair.nu, e f _ (pick (Q.L.φ σ).isLB y), mul_assoc, ← Real.exp_add]
      congr 2
      have : (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y = (Q.A.φ σ).φ (pick (Q.A.φ σ).isLB y) y + 2 * u := rfl
      rw [this]
      push_cast
      ring
    rw [e']
    calc _ ≤ Real.exp u * Real.exp (-u) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem exists_twist : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  intro hC k _ X _ p D hX N x
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair N A
  obtain ⟨c, g, -, hg, -, hgf⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P hA (-1) (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  choose v hv0 hv using fun S => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P (-1) c _ (hgf S)
  let u : ℝ := ∑ S, v S
  have hu : 0 ≤ u := Finset.sum_nonneg fun S _ => hv0 S
  have hvu (S) : v S ≤ u := Finset.single_le_sum (fun S _ => hv0 S) (Finset.mem_univ S)
  let M : HermLB p := P.L.dual.tens (P.A.pow c)
  obtain ⟨h₁, h₂, -⟩ := Pair.rep_base k X p P
  have hM : P.Rep (-1) c M := by
    simpa using Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_dual k X p P _ _ _ h₁) (Pair.rep_pow k X p P _ _ _ c h₂)
  obtain ⟨Q, -, hQ, hB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P _ _ _ _ M M hM hM
  have hi : (P.A.pow c).Isometric (P.L.tens M) :=
    HermLB.icls_eq_iff.1 (by simp only [M, HermLB.icls_tens, HermLB.icls_dual]; abel)
  have hn : (P.L.tens M).IsNef D :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ hi).2.1 (GlobalTheory.NefPow.isNef_pow hC k X p D hX _ c hAn)
  refine ⟨M.shift (fun _ => u) fun _ => rfl, (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ (isometric_shift_tens _ _ u)).2.1
    (GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX _ u hu hn), fun W => ?_⟩
  obtain ⟨R, hR, hR', h⟩ := exists_pair_small Q W g hg u
  refine ⟨R, hR, by rw [hR', hQ], fun S => h _ ?_⟩
  rw [hB]
  simp only [zero_mul, one_mul, zero_add]
  exact ⟨(hv S).1, fun σ y => ((hv S).2 σ y).trans (Real.exp_le_exp.2 (hvu S))⟩

end GlobalTheory.HSNef.BoxTwist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmallStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_twist_nef_squarefree_monomials_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  first | exact @GlobalTheory.HSNef.BoxTwist.exists_twist | exact GlobalTheory.HSNef.BoxTwist.exists_twist | (intros; apply GlobalTheory.HSNef.BoxTwist.exists_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUpper

theorem log_ncard_smallSec {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) :
    Real.log (P.L.smallSec.ncard : ℝ) = P.lc 1 0 1 := by
  have h := SmallBall.encard_eq_Bl P (Pair.rep_base k X p P).1 P.L.smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  unfold Pair.lc
  rw [Set.ncard_def, Set.ncard_def, h]

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro HC HA HS k _ X _ p D hX L N a hL ha ε hε
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX
  obtain ⟨H, hNH, hbox⟩ := GlobalTheory.T.exists_twist_nef_squarefree_monomials_small HC k X p D hX N x
  set G := N.tens H with hG

  have hnef : ∀ m : ℕ, ((L.pow m).tens G).IsNef D := fun m =>
    GlobalTheory.T.hermLineBundle_isNef_tens HC k X p D hX _ _ (GlobalTheory.NefPow.isNef_pow HC k X p D hX L m hL) hNH
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.SelfInterGrowth.main HC k X p D hX L G a ha
  have hα0 : ∀ m, 0 ≤ α m := fun m => by
    obtain ⟨h, Hh, e⟩ := hα m
    rw [← e]
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef HC HA HS k X p D hX _ (hnef m)).2 h Hh _
  have hg0 : ∀ m, 0 ≤ gdeg ((L.pow m).tens G) D := fun m =>
    GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ (hnef m).semiPos
  have hglim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow HC k X p D hX L G
  refine GlobalTheory.T.eventually_le_of_smallSectionLogCountUpperBound D (fun m => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ)) α
    (fun m => gdeg ((L.pow m).tens G) D) a (gdeg L D) hα0 hg0 hαlim hglim (fun m q hq => ?_) ε hε
  obtain ⟨P, hPL, hPA, hPbox⟩ := hbox ((L.pow m).tens N)
  have hiso : (P.L.tens P.A).Isometric ((L.pow m).tens G) := by
    rw [hPL, hPA]
    exact HermLB.isometric_tens_assoc _ _ _
  have T := GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric HC k X p D hX _ _ hiso.symm
  have hb := GlobalTheory.T.arith_log_small_sections_upper_bound HC HA HS k X p D hX P x (α m) q hx.1 hPbox (T.2.1 (hnef m)) (T.2.2.2.1 _ (hα m)) hq
  rw [hiso.gdeg_eq, ← log_ncard_smallSec] at hb
  have e : Real.log (P.L.smallSec.ncard : ℝ) = Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
    rw [hPL]
  simpa only [e] using hb

end GlobalTheory.NefUpper
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBoundStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arith_nef_volume_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.NefUpper.main | exact GlobalTheory.NefUpper.main | (intros; apply GlobalTheory.NefUpper.main <;> assumption)
end
end
