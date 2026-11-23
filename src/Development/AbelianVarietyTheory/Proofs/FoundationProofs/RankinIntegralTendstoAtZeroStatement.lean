module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStableStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurabl

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finsetSum _ fun r _ => h _))

theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurablStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧ (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧ ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  first | exact @GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | exact GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | (intros; apply GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZero

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma rpow_le_add_inv_of_mem_Icc {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    y ^ s ≤ y + y⁻¹ := by
  rcases le_or_gt 1 y with h | h
  · have : y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    have : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
    linarith
  · have h1 : y ^ s ≤ 1 := Real.rpow_le_one hy.le h.le hs0
    have h2 : 1 ≤ y⁻¹ := by rw [le_inv_comm₀ one_pos hy]; simpa using h.le
    linarith

lemma mod_ofReal_norm {F : ℍ → ℂ} (hF : Mod F) : Mod (fun τ => ((‖F τ‖ : ℝ) : ℂ)) := by
  obtain ⟨C, A, h⟩ := hF
  exact ⟨C, A, fun τ => by simpa using h τ⟩

lemma mod_im_pow (A : ℕ) : Mod (fun τ : ℍ => (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, A, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul]

lemma mod_im_add_inv : Mod (fun τ : ℍ => (((τ.im + τ.im⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, 1, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im + τ.im⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul, pow_one]

theorem rankin_tendsto : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  intro k j L L' N ε Φ ρ h b hk hj hL hL' hN hρ hh hb hΦ
  obtain ⟨⟨C, A, hC⟩, hmeas, hlim⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto j L Φ hj hL hΦ
  have hbc : Continuous (qs b) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2
  have hhc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have him : Continuous (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im
  set G : ℍ → ℂ := fun τ => ((‖qs b τ‖ : ℝ) : ℂ) * ((C : ℂ) * (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) *
    (((τ.im + τ.im⁻¹ : ℝ)) : ℂ) with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun τ : ℍ => (τ.im ^ A)⁻¹) :=
      (him.pow A).inv₀ (fun τ => (pow_pos τ.im_pos A).ne')
    have h2 : Continuous (fun τ : ℍ => τ.im⁻¹) := him.inv₀ (fun τ => τ.im_pos.ne')
    simp only [hG]
    fun_prop
  have hGmod : Mod G := by
    have M := GlobalTheory.T.hasModerateGrowth_algebra_slash_stable
    exact (M.1 _ _ ((M.1 _ _ (mod_ofReal_norm (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth b hb))
      ((M.1 _ _ (M.2.1 (C : ℂ)) (mod_im_pow A)).2)).2) mod_im_add_inv).2
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L' L' N ε h ρ G hk hL' hN hρ hh hGc.aestronglyMeasurable hGmod
  have hρm : Measurable (fun τ => (ρ τ : ℂ)) := Complex.measurable_ofReal.comp hρ.meas
  simp only [pet]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => ‖(ρ τ : ℂ) * (conj (qs h τ) * G τ * (τ.im : ℂ) ^ k)‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hs : Measurable (fun τ : ℍ => (((τ.im ^ s : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((him.measurable).pow_const s)
    exact (hρm.mul ((((Complex.continuous_conj.comp hhc).measurable).mul ((hbc.measurable.mul (hmeas s)).mul hs)).mul
      ((Complex.measurable_ofReal.comp him.measurable).pow_const k))).aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [hev] with s hs
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have hρ0 := hρ.nonneg τ
    have hl := hC s τ hs.1.le hs.2.le
    have hys := rpow_le_add_inv_of_mem_Icc hy hs.1.le hs.2.le
    have hX : 0 ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := le_trans (norm_nonneg _) hl
    have hys0 : 0 ≤ τ.im ^ s := Real.rpow_nonneg hy.le s
    have key : ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s ≤
        |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹) :=
      mul_le_mul (hl.trans (le_abs_self _)) hys hys0 (abs_nonneg _)
    simp only [hG, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow, Real.norm_eq_abs,
      norm_norm, abs_norm, Complex.ofReal_mul]
    rw [abs_of_nonneg hy.le, abs_of_nonneg (Real.rpow_nonneg hy.le s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ τ.im + τ.im⁻¹)]
    have hcomb : |C| * |τ.im ^ A + (τ.im ^ A)⁻¹| = |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| := (abs_mul _ _).symm
    have hP : 0 ≤ |ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k := by positivity
    calc |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) * τ.im ^ k)
        = (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) := by ring
      _ ≤ (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (|C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹)) :=
        mul_le_mul_of_nonneg_left key hP
      _ = |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * (|C| * |τ.im ^ A + (τ.im ^ A)⁻¹|) * (τ.im + τ.im⁻¹)) * τ.im ^ k) := by
        rw [hcomb]; ring
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have h1 : Tendsto (fun s : ℝ => (((τ.im ^ s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((τ.im ^ (0:ℝ) : ℝ)) : ℂ)) := by
      have : ContinuousAt (fun s : ℝ => τ.im ^ s) 0 :=
        Real.continuousAt_const_rpow hy.ne'
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp this.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_const_nhds (x := (ρ τ : ℂ))).mul
      (((tendsto_const_nhds (x := conj (qs h τ))).mul (((tendsto_const_nhds (x := qs b τ)).mul (hlim τ)).mul h1)).mul
        (tendsto_const_nhds (x := (τ.im : ℂ) ^ k))))
    simpa only [Real.rpow_zero, Complex.ofReal_one, mul_one] using h2

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZeroStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankinIntegral_tendsto_at_zero : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  first | exact @GlobalTheory.EisM.rankin_tendsto | exact GlobalTheory.EisM.rankin_tendsto | (intros; apply GlobalTheory.EisM.rankin_tendsto <;> assumption)
end
end
