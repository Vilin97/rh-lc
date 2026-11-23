module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBoun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBounStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)), ∃ (C : ℝ) (χ : ℕ → V n → ℝ), (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧ (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧ (∀ v : V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧ ∀ k v b, ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b ≤ C := by
  first | exact @GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | exact GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | (intros; apply GlobalTheory.GoodTop.exists_logCutoff_hyperplanes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupportStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n), IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) → (∀ v ∈ U, v ∉ K → f j v = 0) → ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | exact GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | (intros; apply GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanesStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.isOpen_offCoordinateHyperplanes : ∀ {n : ℕ} (S : Finset (Fin n)) (U : Set (V n)), IsOpen U → IsOpen (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | exact GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | (intros; apply GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicJacobianEqZeroPoincareGro

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousOn_det_dbar {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : Fin n → V n → ℂ}
    (hg : ∀ i, ContDiffOn ℝ 2 (g i) Ω) :
    ContinuousOn (fun v => (Matrix.of fun i b => dbar (g i) v (coordVec b)).det) Ω := by
  have he : ∀ i (w : V n), ContinuousOn (fun v => dbar (g i) v w) Ω := by
    intro i w
    have hd := (hg i).continuousOn_fderiv_of_isOpen hΩ one_le_two
    simp only [dbar_apply]
    exact ((hd.clm_apply continuousOn_const).add
      ((hd.clm_apply continuousOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hM : ContinuousOn (fun v => Matrix.of fun i b => dbar (g i) v (coordVec b)) Ω :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun b => he i _
  exact (continuous_id.matrix_det).comp_continuousOn hM

theorem det_dbar_eq_zero_of_row {n : ℕ} {g : Fin n → V n → ℂ} {v : V n} (j : Fin n)
    (h : g j =ᶠ[𝓝 v] fun _ => 0) :
    (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [dbar_congr h]

theorem integral_det_dbar_eq_zero_of_poincare : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ)
    (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U →
    (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) →
    (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) →
    (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) →
    IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n S U K f j u c hU hK hKU hsmall hf hf0 hfb hdb
  have hΩ : IsOpen (offHyp S U) := GlobalTheory.T.isOpen_offCoordinateHyperplanes S U hU
  have hΩm : MeasurableSet (offHyp S U) := hΩ.measurableSet
  have hKc : IsClosed K := hK.isClosed
  have hwt : ∀ v ∈ offHyp S U, ∀ a, 0 < poinWt S v a := fun v hv =>
    (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
  have hoff : ∀ g : Fin n → V n → ℂ, (∀ v ∈ offHyp S U, v ∉ K → g j v = 0) → ∀ v ∈ offHyp S U, v ∉ K →
      (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := fun g hg v hv hvK =>
    det_dbar_eq_zero_of_row j (Filter.eventually_of_mem ((hΩ.sdiff hKc).mem_nhds ⟨hv, hvK⟩)
      fun x hx => hg x hx.1 hx.2)
  have hbd : ∀ (g : Fin n → V n → ℂ) (c' : ℝ), (∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (g i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c') → ∀ v ∈ offHyp S U, v ∈ K →
      ‖(Matrix.of fun i b => dbar (g i) v (coordVec b)).det‖ ≤
        (n.factorial : ℝ) * |c'| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
    fun g c' h v hv hvK => GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u _ c' (hwt v hv) (h v hv hvK)
  have hint := GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) _ hU hK hKU hsmall
    (continuousOn_det_dbar hΩ hf) (hoff f hf0) (hbd f c hdb)
  refine ⟨hint, ?_⟩
  obtain ⟨C, χ, hχs, hχ01, hχ0, hχ1, hχd⟩ := GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound S
  let F : ℕ → Fin n → V n → ℂ := fun k => Function.update f j (fun x => (χ k x : ℂ) * f j x)
  have hFj : ∀ k, F k j = fun x => (χ k x : ℂ) * f j x := fun k => by simp [F]
  have hFi : ∀ k i, i ≠ j → F k i = f i := fun k i hi => by simp [F, Function.update_of_ne hi]
  have hχC : ∀ k, ContDiffOn ℝ 2 (fun x => (χ k x : ℂ)) (offHyp S U) := fun k =>
    (Complex.ofRealCLM.contDiff.comp (by exact_mod_cast contDiff_infty.1 (hχs k) 2)).contDiffOn
  have hFs : ∀ k i, ContDiffOn ℝ 2 (F k i) (offHyp S U) := by
    intro k i
    by_cases hi : i = j
    · rw [hi, hFj]; exact (hχC k).mul (hf j)
    · rw [hFi k i hi]; exact hf i
  have hF0 : ∀ k, ∀ v ∈ offHyp S U, v ∉ K → F k j v = 0 := fun k v hv hvK => by
    rw [hFj]; simp [hf0 v hv hvK]
  have hzero : ∀ k, ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det = 0 := by
    intro k
    have hsub : K ∩ tsupport (χ k) ⊆ offHyp S U := by
      rintro v ⟨hvK, hvt⟩
      refine ⟨hKU hvK, fun a ha h0 => ?_⟩
      exact (notMem_tsupport_iff_eventuallyEq.2 (hχ0 k v ⟨a, ha, h0⟩)) hvt
    refine GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport (offHyp S U) (K ∩ tsupport (χ k)) (F k) j hΩ (hK.inter_right (isClosed_tsupport _))
      hsub (hFs k) ?_
    intro v hv hvn
    by_cases hvK : v ∈ K
    · have : v ∉ tsupport (χ k) := fun h => hvn ⟨hvK, h⟩
      rw [hFj]; simp [image_eq_zero_of_notMem_tsupport this]
    · exact hF0 k v hv hvK
  have hFb : ∀ k, ∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (F k i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ |c| + |C| * |c| := by
    intro k v hv hvK i b
    have hw := hwt v hv
    have hCc : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hi : i = j
    · rw [hi, hFj]
      have hvn := hΩ.mem_nhds hv
      rw [dbar_mul (a := fun x => (χ k x : ℂ)) (b := f j)
        (((hχC k).differentiableOn two_ne_zero).differentiableAt hvn)
        (((hf j).differentiableOn two_ne_zero).differentiableAt hvn) (coordVec b)]
      have h1 := hdb v hv hvK j b
      have h2 := hχd k v b
      have h3 := hfb v hv hvK
      have hχv := hχ01 k v
      have hp : 0 ≤ poinWt S v (u j) * poinWt S v b := mul_nonneg (hw _).le (hw _).le
      have hA : 0 ≤ ‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b) :=
        mul_nonneg (norm_nonneg _) hp
      have hB : 0 ≤ ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b :=
        mul_nonneg (norm_nonneg _) (hw _).le
      have hE : 0 ≤ ‖f j v‖ * poinWt S v (u j) := mul_nonneg (norm_nonneg _) (hw _).le
      calc ‖(χ k v : ℂ) * dbar (f j) v (coordVec b) + dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖ *
            (poinWt S v (u j) * poinWt S v b)
          ≤ (‖(χ k v : ℂ) * dbar (f j) v (coordVec b)‖ + ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖) *
            (poinWt S v (u j) * poinWt S v b) := mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
        _ = χ k v * (‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b)) +
            (‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b) * (‖f j v‖ * poinWt S v (u j)) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hχv.1]; ring
        _ ≤ |c| + |C| * |c| := by
          refine add_le_add ?_ ?_
          · exact (mul_le_of_le_one_left hA hχv.2).trans (h1.trans (le_abs_self c))
          · exact mul_le_mul (h2.trans (le_abs_self C)) (h3.trans (le_abs_self c)) hE (abs_nonneg _)
    · rw [hFi k i hi]
      exact (hdb v hv hvK i b).trans ((le_abs_self c).trans (le_add_of_nonneg_right hCc))
  let bound : V n → ℝ := K.indicator fun v =>
    (n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2
  have hbint : Integrable bound (volume.restrict (offHyp S U)) := by
    rw [integrable_indicator_iff hKc.measurableSet, IntegrableOn,
      Measure.restrict_restrict hKc.measurableSet]
    exact IntegrableOn.mono_set ((GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hsmall v (hKU hv)).const_mul
      ((n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n)) Set.inter_subset_left
  have hmeas : ∀ k, AEStronglyMeasurable (fun v => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det)
      (volume.restrict (offHyp S U)) := fun k =>
    (continuousOn_det_dbar hΩ (hFs k)).aestronglyMeasurable hΩm
  have hle : ∀ k, ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      ‖(Matrix.of fun i b => dbar (F k i) v (coordVec b)).det‖ ≤ bound v := by
    intro k
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    by_cases hvK : v ∈ K
    · simp only [bound, Set.indicator_of_mem hvK]
      exact hbd (F k) _ (hFb k) v hv hvK
    · simp only [bound, Set.indicator_of_notMem hvK]
      rw [hoff (F k) (hF0 k) v hv hvK, norm_zero]
  have hlim : ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      Tendsto (fun k => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) atTop
        (𝓝 ((Matrix.of fun i b => dbar (f i) v (coordVec b)).det)) := by
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 v hv.2] with k hk
    congr 1
    ext i b
    by_cases hi : i = j
    · simp only [Matrix.of_apply, hi, hFj]
      rw [dbar_congr (f := f j) (g := fun x => (χ k x : ℂ) * f j x) (hk.mono fun x hx => by simp [hx])]
    · simp only [Matrix.of_apply, hFi k i hi]
  have hT := tendsto_integral_of_dominated_convergence bound hmeas hbint hle hlim
  have h0 : (fun k => ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) = fun _ => 0 :=
    funext hzero
  rw [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end GlobalTheory.GoodTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicJacobianEqZeroPoincareGroStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) → (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) → IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧ ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare | exact GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare | (intros; apply GlobalTheory.GoodTop.integral_det_dbar_eq_zero_of_poincare <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZero

section

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integral_mixTop_mdbar_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  intro n r _ _ S U K θ j c hU hK hKU hS hθ h0 hb hd
  have key : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      IntegrableOn (fun v => (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det = 0 := by
    intro p π u
    exact GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth S U K (fun i x => θ i (u i) x (p i) (p (π i))) j u c hU hK hKU hS
      (fun i v hv => (hθ i (u i) v hv (p i) (p (π i))).contDiffWithinAt)
      (fun v hv hvK => by simp [h0 (u j) v hv hvK])
      (fun v hv hvK => hb v hv hvK (u j) _ _)
      (fun v hv hvK i b => hd v hv hvK i (u i) b (p i) (p (π i)))
  have hI : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      Integrable (fun v => ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π u => Integrable.const_mul (key p π u).1 _
  have hI2 : ∀ (p : Fin n → r) (π : Equiv.Perm (Fin n)),
      Integrable (fun v => ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π => integrable_finsetSum _ fun u _ => hI p π u
  have hI3 : ∀ (p : Fin n → r),
      Integrable (fun v => ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p => integrable_finsetSum _ fun π _ => hI2 p π
  unfold mixTop
  refine ⟨Integrable.const_mul (integrable_finsetSum _ fun p _ => hI3 p) _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun p _ => hI3 p]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => ?_)
  rw [integral_finsetSum _ fun π _ => hI2 p π]
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [integral_finsetSum _ fun u _ => hI p π u]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_const_mul, (key p π u).2, mul_zero]

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZeroStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero | exact GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero | (intros; apply GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero <;> assumption)
end
end
