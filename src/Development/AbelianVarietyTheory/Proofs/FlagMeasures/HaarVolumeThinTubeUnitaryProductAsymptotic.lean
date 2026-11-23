module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolume
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KapMulLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetImageBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutiveStatement
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryTubeProductChartHasStrictFDerivAtEntryStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Mathlib.Analysis.Real.Pi.Bounds

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolumeStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  first | exact @GlobalTheory.TubeLie.exists_tang_equiv | exact GlobalTheory.TubeLie.exists_tang_equiv | (intros; apply GlobalTheory.TubeLie.exists_tang_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RotationInvariantMeasureUnitCircleArc

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

namespace GlobalTheory.CircleArc

local instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def par (x : AddCircle (2 * Real.pi)) : ℂ := (AddCircle.toCircle x : Circle)

theorem continuous_par : Continuous par :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

theorem par_injective : Function.Injective par := fun _ _ h =>
  AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext h)

theorem par_coe (s : ℝ) : par (s : AddCircle (2 * Real.pi)) = Complex.exp (s * Complex.I) := by
  rw [par, AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp]

theorem par_add (x y) : par (x + y) = par x * par y := by
  rw [par, AddCircle.toCircle_add, Circle.coe_mul]; rfl

theorem norm_par (x) : ‖par x‖ = 1 := Circle.norm_coe _

theorem range_par : Set.range par = {z | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact norm_par x
  · intro hz
    refine ⟨(z.arg : ℝ), ?_⟩
    rw [par_coe]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at this
    simpa using this

theorem image_ball (r : ℝ) :
    par '' Metric.ball 0 r = (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff] at hx
    obtain ⟨s, rfl, hs⟩ := hx
    exact ⟨s, mem_ball_zero_iff.2 hs, (par_coe s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ?_, par_coe s⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]
    exact ⟨s, rfl, mem_ball_zero_iff.1 hs⟩

theorem measure_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 →
    (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi →
    τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) =
      τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  intro τ ρ hfin hsupp hinv hρ hρπ
  haveI : IsFiniteMeasure τ := ⟨hfin⟩
  have hm : MeasurableEmbedding par :=
    (continuous_par.isClosedEmbedding par_injective).measurableEmbedding
  set ν : Measure (AddCircle (2 * Real.pi)) := τ.comap par with hν
  have hνa : ∀ S, ν S = τ (par '' S) := fun S => hm.comap_apply τ S
  haveI : IsFiniteMeasure ν := ⟨by rw [hνa]; exact measure_lt_top _ _⟩
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro a
    ext S hS
    rw [Measure.map_apply (measurable_const_add a) hS, hνa, hνa]
    conv_rhs => rw [← hinv (par a) (norm_par a)]
    rw [Measure.map_apply (measurable_const_mul _) (hm.measurableSet_image.2 hS)]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a + x, hx, par_add a x⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨-a + y, by simpa using hy, ?_⟩
      have h0 : par a ≠ 0 := by
        intro h0
        have := norm_par a
        rw [h0] at this
        simp at this
      apply mul_left_cancel₀ h0
      rw [← par_add, add_neg_cancel_left]
      exact h
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, ν = t • (volume : Measure (AddCircle (2 * Real.pi))) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hu : τ Set.univ = t * ENNReal.ofReal (2 * Real.pi) := by
    have h1 := hνa Set.univ
    rw [ht, Measure.smul_apply, AddCircle.measure_univ, Set.image_univ, range_par,
      ENNReal.smul_def, smul_eq_mul] at h1
    rw [h1]
    apply measure_congr
    exact (ae_eq_univ.2 hsupp).symm
  rw [← image_ball, ← hνa, hu, ht, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall,
    min_eq_right (by linarith), mul_assoc, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
  congr 2
  have := Real.pi_pos
  field_simp

end GlobalTheory.CircleArc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RotationInvariantMeasureUnitCircleArcStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.rotationInvariant_measure_unitCircle_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 → (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi → τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) = τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  first | exact @GlobalTheory.CircleArc.measure_arc | exact GlobalTheory.CircleArc.measure_arc | (intros; apply GlobalTheory.CircleArc.measure_arc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThinUnitaryTubeVolumeLimitArith

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

theorem tendsto_div_pow_of_sandwich (k : ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) (F F' : ℝ → ℝ≥0∞)
    (hFF : ∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s)
    (h : Tendsto (fun t : ℝ => F t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 C) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [h.eventually (lt_mem_nhds ha), self_mem_nhdsWithin] with t ht ht0
    exact ht.trans_le (ENNReal.div_le_div_right (hFF t (t + 1) ht0 (by linarith)).1 _)
  · intro b hb
    have h1 : Tendsto (fun l : ℝ => C * ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 C) := by
      have h2 : Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝[>] 1) (𝓝 1) := by
        have : Tendsto (fun l : ℝ => ENNReal.ofReal (l ^ k)) (𝓝 1)
            (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ k))) :=
          (ENNReal.continuous_ofReal.comp (continuous_pow k)).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hC)
    obtain ⟨l, hl, hl1⟩ := ((h1.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have hl1 : 1 < l := hl1
    have hl0 : 0 < l := by linarith
    have h3 : Tendsto (fun t : ℝ => l * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => l * t) (𝓝 0) (𝓝 (l * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos hl0 ht
    have h4 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (l ^ k)) (h.comp h3)
      (Or.inr ENNReal.ofReal_ne_top)
    filter_upwards [h4.eventually (gt_mem_nhds hl), self_mem_nhdsWithin] with t ht ht0
    have ht0 : 0 < t := ht0
    refine lt_of_le_of_lt ?_ ht
    have hlk : ENNReal.ofReal (l ^ k) ≠ 0 := by
      simpa using pow_pos hl0 k
    have e : F (l * t) / ENNReal.ofReal ((l * t) ^ k) * ENNReal.ofReal (l ^ k)
        = F (l * t) / ENNReal.ofReal (t ^ k) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_pos hl0 k).le, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hlk) (Or.inl ENNReal.ofReal_ne_top), mul_assoc, mul_right_comm,
        ENNReal.inv_mul_cancel hlk ENNReal.ofReal_ne_top, one_mul]
    simp only [Function.comp]
    rw [e]
    exact ENNReal.div_le_div_right (hFF t (l * t) ht0 (by nlinarith)).2 _

theorem thin_tube_limit_arith : ∀ (k : ℕ) (c c₀ : ℝ) (F F' M V : ℝ → ℝ≥0∞), 0 < c → 0 < c₀ → (∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s) → (∀ ρ : ℝ, 0 < ρ → 0 < V ρ ∧ V ρ < ⊤) → Tendsto (fun ρ : ℝ => M ρ / V ρ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c₀)) → Tendsto (fun ρ : ℝ => M ρ * (F (ρ ^ 2 / 2) * ENNReal.ofReal (ρ / Real.pi)) / (V ρ * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c)) → Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  intro k c c₀ F F' M V hc hc₀ hFF hV hMV hQ
  refine tendsto_div_pow_of_sandwich k _ ENNReal.ofReal_ne_top F F' hFF ?_
  have hpi := Real.pi_pos
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  set K : ℝ := (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hc0' : ENNReal.ofReal c₀ ≠ 0 := by simpa using hc₀
  have hc' : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have h1 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal K)
    (ENNReal.Tendsto.div hQ (Or.inl hc') hMV (Or.inr ENNReal.ofReal_ne_top))
    (Or.inr ENNReal.ofReal_ne_top)
  have e0 : ENNReal.ofReal c / ENNReal.ofReal c₀ * ENNReal.ofReal K
      = ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)) := by
    rw [← ENNReal.ofReal_div_of_pos hc₀, ← ENNReal.ofReal_mul (by positivity), hK, mul_div_assoc]
  rw [e0] at h1
  have h2 : Tendsto (fun ρ : ℝ => F (ρ ^ 2 / 2) / ENNReal.ofReal ((ρ ^ 2 / 2) ^ k)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
    refine h1.congr' ?_
    filter_upwards [hMV.eventually (isOpen_ne.mem_nhds hc0'),
      hMV.eventually (isOpen_ne.mem_nhds ENNReal.ofReal_ne_top), self_mem_nhdsWithin]
      with ρ hm0 hmt hρ
    have hρ : 0 < ρ := hρ
    obtain ⟨hv0, hvt⟩ := hV ρ hρ
    rw [ENNReal.mul_div_mul_comm (Or.inl hv0.ne') (Or.inl hvt.ne), mul_comm (M ρ / V ρ),
      mul_div_assoc (_ / _), ENNReal.div_self hm0 hmt, mul_one, mul_div_assoc, mul_assoc,
      ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      div_eq_mul_inv (F _), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 2
    rw [hK, div_pow, ← pow_mul, mul_pow]
    field_simp
    ring
  have h3 : Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝 0) (𝓝 (Real.sqrt (2 * 0))) :=
        (by fun_prop : Continuous fun t : ℝ => Real.sqrt (2 * t)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : 0 < t := ht
      exact Real.sqrt_pos.2 (by linarith)
  refine (h2.comp h3).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have : Real.sqrt (2 * t) ^ 2 / 2 = t := by
    rw [Real.sq_sqrt (by linarith)]; ring
  simp only [Function.comp, this]

end GlobalTheory.Tube
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThinUnitaryTubeVolumeLimitArithStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.thinUnitaryTube_volume_limit_arith : ∀ (k : ℕ) (c c₀ : ℝ) (F F' M V : ℝ → ℝ≥0∞), 0 < c → 0 < c₀ → (∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s) → (∀ ρ : ℝ, 0 < ρ → 0 < V ρ ∧ V ρ < ⊤) → Tendsto (fun ρ : ℝ => M ρ / V ρ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c₀)) → Tendsto (fun ρ : ℝ => M ρ * (F (ρ ^ 2 / 2) * ENNReal.ofReal (ρ / Real.pi)) / (V ρ * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c)) → Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  first | exact @GlobalTheory.Tube.thin_tube_limit_arith | exact GlobalTheory.Tube.thin_tube_limit_arith | (intros; apply GlobalTheory.Tube.thin_tube_limit_arith <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarVolumeThinTubeUnitaryProductAsymptotic

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Tube

theorem unrealify_cont {m : ℕ} : Continuous (unrealify (m := m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => (x (i, j, false) : ℂ) + (x (i, j, true) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [unrealify]
  rw [this]; fun_prop

theorem chart_zero (k : ℕ) (η : ℝ) : chart η (0 : Par k) = 1 := by
  have h1 : unrealify (m := k) (0 : EuclideanSpace ℝ _) = 0 := by
    ext i j; apply Complex.ext <;> simp [unrealify]
  have h2 : hv (0 : EuclideanSpace ℂ (Fin k)) = 0 := by funext j; simp [hv]
  simp [chart, h1, h2, kap_one, sec_zero]

theorem thin_tube : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∀ (μ : Measure (PI.MtM (k + 1))) (μ₀ : Measure (PI.MtM k)) (c c₀ : ℝ), 0 < c → 0 < c₀ → PI.IsHaarOnM (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ → HasDens (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ (ENNReal.ofReal c) → PI.IsHaarOnM (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ → μ₀ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ (ENNReal.ofReal c₀) → Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  intro k η hk hη μ μ₀ c c₀ hc hc₀ hμ hd hμ₀ h1 hd₀
  change PI.IsHaarOnM (UH (Hd k η)) μ at hμ
  change HasDens (UH (Hd k η)) μ _ at hd
  have hexp : ∀ X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)),
      NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _)) ∈ UH (1 : Matrix (Fin k) (Fin k) ℂ) := fun X =>
    CCRuleCW.exp_mem_UH _ _ ((GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive k 1 X.1 (Matrix.one_mul _)).1 X.2)
  obtain ⟨L, hL, hvol⟩ := GlobalTheory.T.exists_productChart_tangentEquiv_ballVolume k η hk hη
  have hmem : ∀ᶠ x in 𝓝 (0 : Par k), chart η x ∈ UH (Hd k η) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par k) one_pos] with x hx
    have hw : ‖x.2.2‖ < 1 := ((norm_snd_le x.2).trans (norm_snd_le x)).trans_lt (mem_ball_zero_iff.1 hx)
    refine (comp hη (hexp x.1) (Complex.norm_exp_ofReal_mul_I x.2.1) ?_).1
    rw [nsq_hv]; have := norm_nonneg x.2.2; nlinarith
  have hch := GlobalTheory.T.tendsto_measure_image_ball_div_volume (k + 1) (UH (Hd k η)) μ _ (GlobalTheory.GramExp.isMatGroup_UH _ (Hd_sq k hη)) hμ hd (Par k)
    (chart η) L (chart_zero k η) hmem (fun i j => by
      obtain ⟨D, h, h'⟩ := GlobalTheory.T.unitaryTubeProductChart_hasStrictFDerivAt_entry k η i j
      exact ⟨D, h, fun v => by rw [h', hL]⟩)
  refine GlobalTheory.T.thinUnitaryTube_volume_limit_arith k c c₀ (fun t => μ (tubeO k η t)) _
    (fun ρ => μ₀ (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)))
    (fun ρ => volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ)) hc hc₀ (fun t s ht hs => ⟨?_, ?_⟩)
    (fun ρ hρ => ⟨Metric.measure_ball_pos _ _ hρ, measure_ball_lt_top⟩) hd₀ (hch.congr' ?_)
  · refine measure_mono fun g hg => ?_
    exact (abs_id hη hg.1).le.trans hg.2.le
  · refine measure_mono_ae ?_
    have : ∀ᵐ g ∂μ, Matrix.of g ∈ UH (Hd k η) := hμ.2.2.1
    filter_upwards [this] with g hg h
    exact ⟨hg, ((abs_id hη hg).ge.trans h).trans_lt hs⟩
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ρ hρ
    have hρ' : ρ ^ 2 / 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
    have hA0 : Continuous fun X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) =>
        (Matrix.of.symm (NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _))) : PI.MtM k) :=
      GlobalTheory.GramExp.exp_cont.comp (unrealify_cont.comp continuous_subtype_val)
    have hA : MeasurableSet (expSet (UH (1 : Matrix (Fin k) (Fin k) ℂ)) (Metric.ball 0 ρ)) :=
      GlobalTheory.GramExp.measurableSet_image_ball hA0 _ _
    have hB : MeasurableSet ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) :=
      GlobalTheory.GramExp.measurableSet_image_ball (by fun_prop) _ _
    obtain ⟨τ, t1, t2, t3, t4⟩ := phase_law hη hμ hρ'
    rw [hvol ρ hρ.1, chart_image hη hexp hρ.1 hρ.2, prod_top hη hμ hμ₀ h1 hρ' hA hB, ← t1 _ hB,
      GlobalTheory.T.rotationInvariant_measure_unitCircle_arc τ ρ t2 t3 t4 hρ.1 (by linarith [hρ.2, Real.pi_gt_three]), t1 _ MeasurableSet.univ]
    simp

end GlobalTheory.Tube
end
end
end
