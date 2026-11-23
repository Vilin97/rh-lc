module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCuspStatement
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOne
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLe

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (GlobalTheory.T.unitStrip_integral_eq_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLeStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le : ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  first | exact @GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | exact GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | (intros; apply GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOneStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOneStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_bound_norm_qs_of_one_le_im : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  first | exact @GlobalTheory.EisM.qs_bdd_above_one | exact GlobalTheory.EisM.qs_bdd_above_one | (intros; apply GlobalTheory.EisM.qs_bdd_above_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrand

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrandStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  first | exact @GlobalTheory.EisM.strip_integrable_rankin | exact GlobalTheory.EisM.strip_integrable_rankin | (intros; apply GlobalTheory.EisM.strip_integrable_rankin <;> assumption)
end
end
