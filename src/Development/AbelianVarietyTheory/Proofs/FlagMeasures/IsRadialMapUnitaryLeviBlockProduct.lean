module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProdStatement
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProdStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtEqReTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroup
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePiStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.euclideanBallAsymptotics_finite_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) → (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) → IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  first | exact @GlobalTheory.LeviIso.isRadial_pi | exact GlobalTheory.LeviIso.isRadial_pi | (intros; apply GlobalTheory.LeviIso.isRadial_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (hs)

noncomputable section

namespace GlobalTheory.LeviIso.RadLoc

section
open scoped Matrix.Norms.Frobenius

theorem hs_eq_norm_sq {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : hs M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [hs]

theorem hs_inv_compare {j : ℕ} (x : Matrix (Fin j) (Fin j) ℂ) (hx : x.det ≠ 0) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (h : hs (x⁻¹ - 1) ≤ (1 - a) ^ 2) :
    a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1) := by
  simp only [hs_eq_norm_sq] at *
  have e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1)) := by
    rw [sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]
    simp
    abel
  have h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖ := by
    rw [e, norm_neg]; exact norm_mul_le _ _
  have h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)
  have h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)
  have hA := norm_nonneg (x - 1)
  have hB := norm_nonneg (x⁻¹ - 1)
  generalize ‖x - 1‖ = A at *
  generalize ‖x⁻¹ - 1‖ = B at *
  have h4 : B ≤ 1 - a := (sq_le_sq₀ hB (by linarith)).1 h
  have h5 : B * A ≤ (1 - a) * A := mul_le_mul_of_nonneg_right h4 hA
  rw [← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]
  constructor
  · linarith
  · have h6 : a * B ≤ a * ((2 - a) * A) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) hA]

end

theorem hs_nonneg {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : 0 ≤ hs M := by
  unfold hs; positivity

theorem continuous_hs {j : ℕ} : Continuous (hs : Matrix (Fin j) (Fin j) ℂ → ℝ) := by
  unfold hs; fun_prop

def unitBallAt (j : ℕ) (s : ℝ) : Set (Fin j → Fin j → ℂ) := {x | hs (Matrix.of x - 1) ≤ s ^ 2}

theorem measurableSet_unitBallAt (j : ℕ) (s : ℝ) : MeasurableSet (unitBallAt j s) := by
  refine (isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet
  exact (continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const

theorem volume_unitBallAt (j : ℕ) {s : ℝ} (hs0 : 0 < s) :
    volume (unitBallAt j s) = ENNReal.ofReal (s ^ (2 * j ^ 2)) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  set e := PoissonV.coords (Fin j) (Fin j) with he
  rw [← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage
    (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]
  have h1 : e ⁻¹' unitBallAt j s =
      Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s := by
    ext z
    rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he,
      map_sub, e.apply_symm_apply]
    rfl
  rw [h1, Measure.addHaar_closedBall _ _ hs0.le, hd]
  congr 1
  rw [← hd]
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem exists_subset {j : ℕ} {P : (Fin j → Fin j → ℂ) → Prop}
    (h : ∀ᶠ x in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)), P x) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ x ∈ unitBallAt j s, P x := by
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]
  intro r
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro c
  rw [← sq_le_sq₀ (norm_nonneg _) hs0]
  refine le_trans ?_ hx
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))
  exact Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

theorem eventually_good (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : Fin j → Fin j → ℂ in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)),
      (a ≤ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ∧ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (Matrix.of x - 1) ≤ hs ((Matrix.of x)⁻¹ - 1) ∧
      a ^ 2 * hs ((Matrix.of x)⁻¹ - 1) ≤ hs (Matrix.of x - 1) := by
  show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1,
      (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)
  have hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det := continuous_id.matrix_det
  have h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1 :=
    (((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j
  have h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1 := by
    refine continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  have h3 := h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))
  have h4 := h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))
  have h5 := h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by
    have : 0 < 1 - a := by linarith
    simpa [hs] using pow_pos this 2))
  have h6 := (hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)
  filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6
  exact ⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩

theorem sandwich (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) ≤
        (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ∧
      (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ≤
      ENNReal.ofReal (a⁻¹ ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  obtain ⟨δ, hδ, H⟩ := exists_subset (eventually_good j ha ha1)
  filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have h21 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < δ := by nlinarith
  have hr2 : a * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)
  have hr3 : a⁻¹ * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) ?_
    rwa [inv_mul_lt_iff₀ ha]
  have hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0 := by
    simpa using pow_pos hr _
  have hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b *
      volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2)) := by
    intro b hb
    rw [volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [div_pow, pow_mul √2, h22, mul_pow]
    field_simp
    ring
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha,
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1
    · have h3 := (H _ (by positivity) hr2 x hx).2.2
      have h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2 := by
        have : hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2 := hx
        rwa [div_pow, h22, mul_pow] at this
      have h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2 :=
        le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)
      have h6 : a ^ 2 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (by positivity) (by nlinarith)
      refine Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩
  · rw [ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity),
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_
    · have h1 := (Real.sqrt_le_iff.1 hx).2
      have h0 := hs_nonneg ((Matrix.of x)⁻¹ - 1)
      have h0' := hs_nonneg (Matrix.of x - 1)
      have h3 := (H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1
      have h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1) :=
        mul_le_of_le_one_left h0' (by nlinarith)
      show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2
      rw [div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]
      linarith
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2

end GlobalTheory.LeviIso.RadLoc

namespace GlobalTheory.LeviIso

open RadLoc

theorem isRadial_haarLoc (j : ℕ) : IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
    (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  unfold IsRadial
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω) := by
    have : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1) := by
      simpa using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))
    simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
  have hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨a, h1, h2, h3⟩ := (((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_lt_of_le h1 hr.1
  · obtain ⟨a, h1, h2, h3⟩ := ((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_le_of_lt hr.2 h1

end GlobalTheory.LeviIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverseStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse : ∀ j : ℕ, IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j) (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  first | exact @GlobalTheory.LeviIso.isRadial_haarLoc | exact GlobalTheory.LeviIso.isRadial_haarLoc | (intros; apply GlobalTheory.LeviIso.isRadial_haarLoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProduct

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.MapRadial

theorem continuous_hs {n : ℕ} : Continuous (Formalism.REAL.hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold Formalism.REAL.hs
  fun_prop

theorem hs_nonneg' {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs
  positivity

theorem measurable_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Measurable fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact (continuous_hs.comp (this.sub continuous_const)).measurable

theorem measurable_hs_loc (j : ℕ) : Measurable fun x : Fin j → Fin j → ℂ =>
    Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1) := by
  have h0 : Continuous fun x : Fin j → Fin j → ℂ => Matrix.of x := continuous_id
  have h1 : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := h0.matrix_det.measurable
  have h2 : ∀ r s, Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).adjugate r s :=
    fun r s => (h0.matrix_adjugate.matrix_elem r s).measurable
  refine (continuous_hs.comp (h0.sub continuous_const)).measurable.add ?_
  unfold Formalism.REAL.hs
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (((h1.inv.mul (h2 r s)).sub measurable_const).norm).pow_const 2

theorem isRadial_map_lev : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  intro n n₀ a j ε ε₀ B B₀ hF θ hθ hθe c hc
  have hG : IsRadial (ENNReal.ofReal c • Formalism.REAL.muG ε₀) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2) := by
    have := ((GlobalTheory.GaugeWhole.gauge_whole n₀ ε₀).1 c hc).2.2.2
    simpa [IsRadial] using this
  haveI : SigmaFinite (Formalism.REAL.muG ε₀) := by
    unfold Formalism.REAL.muG
    infer_instance
  have hP := GlobalTheory.T.euclideanBallAsymptotics_finite_pi a (fun i => Fin (j i) → Fin (j i) → ℂ)
    (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) _ (fun i => 2 * j i ^ 2)
    (fun i => measurable_hs_loc (j i)) (fun i x => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun i => GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse (j i))
  have h2 := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ _ _ _ _ _ _
    (Finset.measurable_sum _ fun i _ => (measurable_hs_loc (j i)).comp (measurable_pi_apply i))
    (measurable_hs_uMat ε₀)
    (fun x => Finset.sum_nonneg fun i _ => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun g => hs_nonneg' _) hP hG
  have hd : n₀ ^ 2 + 2 * ∑ i, j i ^ 2 = ∑ i, 2 * j i ^ 2 + n₀ ^ 2 := by
    rw [Finset.mul_sum, add_comm]
  rw [hd]
  have hae1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)),
      ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    have h0 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      rw [ae_iff]
      simpa using (haarLoc_conj_and_null (j i)).2
    exact (Measure.quasiMeasurePreserving_eval
      (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) i).ae (Measure.ae_smul_measure h0 _)
  have hae := (Measure.quasiMeasurePreserving_fst (ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀)).ae hae1
  unfold IsRadial at h2 ⊢
  refine h2.congr fun r => ?_
  rw [Measure.map_apply hθ (measurableSet_le (measurable_hs_uMat ε).sqrt measurable_const)]
  congr 1
  refine measure_congr ?_
  filter_upwards [hae] with z hz
  have e := hs_lev_sub_one n n₀ a j ε ε₀ B B₀ hF (fun i => Matrix.of (z.1 i)) (uMat z.2)
  rw [← hθe z hz] at e
  exact Iff.of_eq (congrArg (fun t => Real.sqrt t ≤ r) e.symm)

end GlobalTheory.LeviIso.MapRadial
end
end
