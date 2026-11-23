module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffBlockEntriesBoundedNormalFormPairOfFlagsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengths
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThreeBoxesVolumeProductLeExplicitPowerStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurableStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjectionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
import Mathlib.Tactic.ReduceModChar
import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengthsStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.radical_coordinates_bounded_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  first | exact @GlobalTheory.Amp.RadBound.radical_coords_le | exact GlobalTheory.Amp.RadBound.radical_coords_le | (intros; apply GlobalTheory.Amp.RadBound.radical_coords_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThree

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem vol_gram_codim_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  intro k j _ hjk m hm P hP0
  have hP : k - 2 ≤ Module.finrank ℂ P := by omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : d + 2 - 2 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 3 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 2 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (measure_mono fun B hB => ?_)
      (le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_))
    · exact ⟨hB.1, hB.2.2⟩
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have h2 : M ^ (2 * j ^ 2) ≤ 4 * M ^ (2 * j ^ 2 + 2 * j) := by
      have h3 : M ^ (2 * j ^ 2) ≤ M ^ (2 * j ^ 2 + 2 * j) := pow_le_pow_right₀ hM (Nat.le_add_right _ _)
      have h4 : 0 ≤ M ^ (2 * j ^ 2 + 2 * j) := by positivity
      linarith
    calc _ = (Real.pi * M ^ 2) ^ (3 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (3 * j) * (4 * M ^ (2 * j ^ 2 + 2 * j)) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = _ := by
          rw [← pow_mul (Real.exp 1 / s), mul_comm s j, ← mul_pow, mul_div_assoc, mul_assoc _ (4 : ℝ)]

end GlobalTheory.Amp.GramVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThreeStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.volume_gramCondition_codim_two_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  first | exact @GlobalTheory.Amp.GramVol.vol_gram_codim_three | exact GlobalTheory.Amp.GramVol.vol_gram_codim_three | (intros; apply GlobalTheory.Amp.GramVol.vol_gram_codim_three <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBound

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibNf

theorem card_UT (r : ℕ) : Fintype.card (UT r) = r * (r - 1) / 2 := by
  rw [Fintype.card_subtype, ← Nat.choose_two_right]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
  simpa using this

theorem vol_polydisc (ι : Type) [Fintype ι] {R : ℝ} (hR : 0 ≤ R) :
    volume {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = ENNReal.ofReal ((Real.pi * R ^ 2) ^ Fintype.card ι) := by
  have h : {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem vol_cube (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = ENNReal.ofReal ((2 * R) ^ r) := by
  have h : {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem sfinite_PPar (k r : ℕ) : SFinite (volume : Measure (PPar k r)) := by
  have : SFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  have : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := inferInstance
  infer_instance

theorem vol_PPar (k r : ℕ) (S : Set (Fin r → Fin (k + 1) → ℂ)) (T : Set (UT r → ℂ)) (U : Set (Fin r → ℝ)) :
    (volume : Measure (PPar k r)) (S ×ˢ (T ×ˢ U)) = volume S * (volume T * volume U) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]

theorem coords_upper {r : ℕ} (u : UT r → ℂ) : USplit.coords (upper u) = u := by
  funext p
  exact USplit.upper_of_lt u p.2

theorem measurable_coord (k r : ℕ) : Measurable fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) :=
  (show Continuous fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) from (NCoord.coord_homeo k r).2.1).measurable

theorem coord_mem (k r : ℕ) (u : UT r → ℂ) (q : PPar k r) : uEmb k r (upper u) * pOf k r q ∈ Nset k r := by
  have := (NCoord.coord_homeo k r).1.mapsTo (Set.mem_univ (u, q))
  simpa only using this

theorem coord_off_mem (k r : ℕ) (β : Fin r → ℕ) (y : UToff β → ℂ) (q : PPar k r) :
    uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := by
  unfold upperOff
  exact coord_mem k r _ q

theorem cut_le {k r : ℕ} {β : Fin r → ℕ} (φ : Mt k r → ℝ≥0∞) (hφ : SubCut (Nset k r) (lebR k r β) φ)
    (n : Mat k r) (hN : n ∈ Nset k r) :
    ∫⁻ x : UTin β → ℂ, φ (Matrix.of.symm (uEmb k r (upperIn β x) * n)) ≤ 1 := by
  have h1 := hφ.2 (Matrix.of.symm n) hN
  have hl : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (Matrix.of.symm n : Mt k r)) :=
    hφ.1.comp (continuous_rmulM n).measurable
  have hi : Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
      unfold upperIn
      refine (NCoord.cont_uEmb k r).comp (continuous_pi fun p => ?_)
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
    exact Continuous.measurable (γ := Mt k r) this
  unfold lebR at h1
  rw [lintegral_map hl hi] at h1
  exact h1

theorem lintegral_le {k r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (φ : Mt k r → ℝ≥0∞)
    (hφ : SubCut (Nset k r) (lebR k r β) φ) (E : Set (Mt k r)) (hE : MeasurableSet E)
    (A : Set (UToff β → ℂ)) (B : Set (PPar k r))
    (h : ∀ x y q, (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ∈ E →
      y ∈ A ∧ q ∈ B) :
    ∫⁻ n, φ n * E.indicator 1 n ∂(lebN k r) ≤ volume A * volume B := by
  have hm : Measurable fun n => φ n * E.indicator 1 n := hφ.1.mul (measurable_one.indicator hE)
  have hF := measurable_coord k r
  have := sfinite_PPar k r
  unfold lebN
  rw [lintegral_map hm hF, Measure.volume_eq_prod]
  refine le_trans (lintegral_prod_symm' _ (hm.comp hF)).le ?_
  refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_const_le B (volume A))
  have hc : Measurable fun U : Fin r → Fin r → ℂ => USplit.coords (Matrix.of U) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)
  have hs := (USplit.lebesgue_split r β hβ).2 _ ((hm.comp hF).comp (hc.prodMk (measurable_const (a := q))))
  simp only [Function.comp_apply, Equiv.apply_symm_apply, coords_upper] at hs
  have hp : ∀ x y, uEmb k r (upper (USplit.coords (upperIn β x * upperOff β y))) * pOf k r q =
      uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q) := by
    intro x y
    have : upper (USplit.coords (upperIn β x * upperOff β y)) = upperIn β x * upperOff β y :=
      USplit.upper_coords_mul _ _
    rw [this, UEmb.uEmb_mul, Matrix.mul_assoc]
  simp only [hp] at hs
  simp only [Function.comp_apply]
  rw [hs]
  have key : ∀ y, ∫⁻ x : UTin β → ℂ,
      φ (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q))) *
        E.indicator 1 (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ≤
      A.indicator (fun _ => B.indicator 1 q) y := by
    intro y
    by_cases hy : y ∈ A ∧ q ∈ B
    · rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hy.2]
      refine le_trans (lintegral_mono fun x => ?_) (cut_le φ hφ _ (coord_off_mem k r β y q))
      exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le) _)
    · refine le_trans (le_of_eq ?_) zero_le
      have : ∀ x : UTin β → ℂ, E.indicator (1 : Mt k r → ℝ≥0∞)
          (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) = 0 :=
        fun x => Set.indicator_of_notMem (fun hx => hy (h x y q hx)) _
      simp only [this, mul_zero, lintegral_zero]
  refine le_trans (lintegral_mono key) (le_trans (lintegral_indicator_const_le A _) (le_of_eq ?_))
  by_cases hq : q ∈ B <;> simp [hq]

theorem arith {a b c d e f g : ℝ} (hpos : 0 ≤ e * f) (har : a * (b * c) * d ≤ g) :
    a * (d * e * f * (b * c)) ≤ g * e * f := by
  have := mul_le_mul_of_nonneg_right har hpos
  refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_)) <;> ring

theorem null_of {k r : ℕ} (Z : Set (Mt k r)) (hZ : MeasurableSet Z) (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S = 0)
    (h : ∀ u q, (Matrix.of.symm (uEmb k r (upper u) * pOf k r q) : Mt k r) ∈ Z → q.1 ∈ S) : lebN k r Z = 0 := by
  have := sfinite_PPar k r
  unfold lebN
  rw [Measure.map_apply (measurable_coord k r) hZ]
  refine measure_mono_null (t := Set.univ ×ˢ (S ×ˢ (Set.univ ×ˢ Set.univ))) (fun q hq => ?_) ?_
  · exact ⟨trivial, h q.1 q.2 hq, trivial, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod, vol_PPar, hS, zero_mul, mul_zero]

theorem mem_of_mul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ ρ x : Mat k r} {R₀ y : ℝ}
    (hz : inWb k r z) (hz' : inWb k r z') (hg : g₀ ∈ GG k r) (hρ : ρ ∈ Rset k r g₀) (hx0 : x ∈ GG k r)
    (hx : (Matrix.of.symm (ρ * x) : Mt k r) ∈ Eset k r z z' g₀ R₀ y) :
    Sg k r z' x ≤ R₀ ∧ Sg k r z (g₀ * x) ≤ R₀ ∧ y < Yv k r z z' g₀ x ∧ Yv k r z z' g₀ x ≤ 2 * y := by
  have hx' : Sg k r z' (ρ * x) ≤ R₀ ∧ Sg k r z (g₀ * (ρ * x)) ≤ R₀ ∧ y < Yv k r z z' g₀ (ρ * x) ∧
      Yv k r z z' g₀ (ρ * x) ≤ 2 * y := hx.2
  have h1 : (1 : Mat k r) ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨(nSubgroup k r).1.1, one_mem _⟩
  have e1 := ((LInv.lengths_basic k r z' hz').1 _ hx0 _ (YInv.N_sub_S z' hρ.1) 1 h1).2
  have e2 := ((LInv.lengths_basic k r z hz).1 _ (YInv.mul_mem hg hx0) _ (YInv.N_sub_S z hρ.2) 1 h1).2
  have e3 := (YInv.yv_invariant k r z z' g₀ hz hz' hg _ hx0).2.2 _ hρ
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_assoc _ g₀⁻¹, ← Matrix.mul_assoc g₀⁻¹, Matrix.nonsing_inv_mul _ (YInv.det_unit hg),
    Matrix.one_mul, Matrix.mul_assoc g₀] at e2
  rwa [e1, e2, e3] at hx'

theorem vol_bound {k r : ℕ} (β : Fin r → ℕ) {R₀ De y : ℝ} (hr : 1 ≤ r) (hR : 1 ≤ R₀) (h1De : 1 ≤ De) (hy : 0 < y)
    (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S ≤ ENNReal.ofReal ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 *
      (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) *
      (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r)))) :
    volume {y : UToff β → ℂ | ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De} *
      (volume : Measure (PPar k r)) (S ×ˢ ({s : UT r → ℂ | ∀ p, ‖s p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2} ×ˢ
          {t : Fin r → ℝ | ∀ p, |t p| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2})) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  have hR1 : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) h1De
  have hR3 : 0 ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by positivity
  rw [vol_PPar, vol_polydisc _ (zero_le_one.trans hR1), vol_polydisc _ hR3, vol_cube _ hR3, card_UT]
  have hcard : Fintype.card (UToff β) ≤ r * (r - 1) / 2 := card_UT r ▸ Fintype.card_subtype_le _
  have hb : 1 ≤ Real.pi * (R₀ ^ (2 * r) * De) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) (one_le_pow₀ hR1)
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hb hcard))
    (mul_le_mul' hS le_rfl)) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have har := GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower r R₀ De hr hR h1De
  have hpos : 0 ≤ (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    (2 * y) ^ (2 * (k - 2 - r)) := by positivity
  unfold fibVol
  exact arith hpos har

theorem fibre_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  intro k r z z' g₀ β De hr hk hT hN hD m hm a ha
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection k r z z' g₀ β (by omega) hT hN m hm
  obtain ⟨hV0, hV⟩ := GlobalTheory.T.volume_gramCondition_codim_two_three k r hr hk m hm P₀ hP₀
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' g₀ hN.1
  have hU := fun R₀ hR => GlobalTheory.T.offBlock_entries_bounded_normalForm_pairOfFlags k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hB := fun R₀ hR => GlobalTheory.T.radical_coordinates_bounded_majorant_lengths k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hdG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := by
    apply UEmb.uEmb_mem
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  have hmG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hNq := coord_mem k r
  have hY' := fun u q => hY u q a ha
  have hU' := fun R₀ hR w q => hU R₀ hR w q a ha
  have hB' := fun R₀ hR w q => hB R₀ hR w q a ha
  have hcG := YInv.mul_mem hdG hmG
  simp only [Matrix.mul_assoc _ (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)))] at hY' hU' hB'
  clear hY hU hB
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = c at *
  have hrm : Measurable (rmulM c) := (continuous_rmulM c).measurable
  constructor
  · have hZ : MeasurableSet ((Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
        (fun x => Yv k r z z' g₀ (Matrix.of x)) ∘ rmulM c) ⁻¹' {0}) := (hM1.comp hrm) (measurableSet_singleton 0)
    refine measure_mono_null (fun n hn => ?_) (null_of _ hZ _ hV0 fun u q hq => ?_)
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    · have := Set.indicator_apply_eq_zero.1 hq (YInv.mul_mem (hNq u q).1 hcG)
      exact (hY' u q).symm.trans this
  · intro φ hφ R₀ y hR hy
    have h1De : 1 ≤ De := hD.1
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hR2 : 1 ≤ r * R₀ ^ (2 * r - 1) * De :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr' (one_le_pow₀ hR)) h1De
    refine le_trans ?_ (vol_bound β hr hR h1De hy _ (hV _ y hR2 hy))
    refine le_trans (le_of_eq ?_) (lintegral_le hN.2.2.1 φ hφ (rmulM c ⁻¹' Eset k r z z' g₀ R₀ y) (hrm (hM2 R₀ y)) _ _ ?_)
    · refine lintegral_congr fun n => ?_
      congr 1
    · intro x w q hx
      have hρ : uEmb k r (upperIn β x) ∈ Rset k r g₀ := by
        rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r g₀ β hN).1]; exact ⟨x, rfl⟩
      have hn0 : uEmb k r (upperOff β w) * pOf k r q ∈ Nset k r := coord_off_mem k r β w q
      have hx0 : uEmb k r (upperOff β w) * pOf k r q * c ∈ GG k r := YInv.mul_mem hn0.1 hcG
      have hx1 : (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β w) * pOf k r q * c)) : Mt k r) ∈
          Eset k r z z' g₀ R₀ y := by
        rw [← Matrix.mul_assoc]; exact hx
      obtain ⟨s1, s2, s3, s4⟩ := mem_of_mul hT.1 hT.2.1 hN.1 hρ hx0 hx1
      have e4 : Yv k r z z' g₀ (uEmb k r (upperOff β w) * pOf k r q * c) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
        unfold upperOff
        exact hY' _ q
      rw [e4] at s3 s4
      obtain ⟨b1, b2, b3⟩ := hB' R₀ hR w q s1 s2
      exact ⟨hU' R₀ hR w q s1 s2, ⟨b1, s3, s4⟩, b2, b3⟩

end GlobalTheory.Amp.FibNf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBoundStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibNf.fibre_bound | exact GlobalTheory.Amp.FibNf.fibre_bound | (intros; apply GlobalTheory.Amp.FibNf.fibre_bound <;> assumption)
end
end
