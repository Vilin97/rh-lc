module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevPointwiseBound

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.SupG

theorem norm_cls_sq_eq {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {K : Mat n → V}
    (h : MemLp (fun y : G n => K y.val) 2 μ) :
    ‖cls μ K‖ ^ 2 = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
  have hc : cls μ K = h.toLp _ := dif_pos h
  rw [hc, Lp.norm_toLp, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_unit {n : ℕ} {x : Mat n} (hx : x ∈ GLs n) : ∃ g : G n, g.val = x :=
  ⟨((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit, rfl⟩

theorem sup_sq_bound : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ (S : Finset (List (Bool × Fin n × Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (h : Mat n → V), ContDiffOn ℝ ∞ h (GLs n) → (∀ w, MemLp (fun y : G n => Rw w h y.val) 2 μ) → ∀ x ∈ GLs n, ‖h x‖ ^ 2 ≤ C * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 := by
  intro hS n _ _ μ _
  obtain ⟨S, r, C, hC⟩ := hS n μ
  refine ⟨S, max C 0, le_max_right _ _, fun V _ _ _ h hsm hL x hx => ?_⟩
  obtain ⟨g, rfl⟩ := exists_unit hx
  have h0 := hC V h hsm g.val hx
  have hw : ∀ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ ≤
      ‖cls μ (Rw w h)‖ ^ 2 := by
    intro w _
    set K := Rw w h with hK
    have hm : MemLp (fun y : G n => K y.val) 2 μ := hL w
    have hφ : Integrable (fun y : G n => ‖K y.val‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    have hψ : Integrable (fun y : G n => ‖K (g.val * y.val)‖ ^ 2) μ := by
      simpa only [Units.val_mul] using hφ.comp_mul_left g
    have e1 : ∫ y : G n, ‖K (g.val * y.val)‖ ^ 2 ∂μ = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
      simpa only [Units.val_mul] using
        integral_mul_left_eq_self (μ := μ) (fun y : G n => ‖K y.val‖ ^ 2) g
    rw [norm_cls_sq_eq hm, ← e1]
    exact setIntegral_le_integral hψ (Filter.Eventually.of_forall fun y => by positivity)
  have hI : 0 ≤ ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
    Finset.sum_nonneg fun w _ => integral_nonneg fun y => by positivity
  calc ‖h g.val‖ ^ 2
      ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ := h0
    _ ≤ max C 0 * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hI
    _ ≤ max C 0 * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_max_right _ _)

end GlobalTheory.CompanionTheory.PresSobA.SupG
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSequenceUniformCauchy

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.RwCauchy

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem Rw_sub_on {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : Mat n → V}
    (ha : ContDiffOn ℝ ∞ a (GLs n)) (hb : ContDiffOn ℝ ∞ b (GLs n))
    (w : List (Bool × Fin n × Fin n)) :
    ∀ z ∈ GLs n, Rw w (a - b) z = Rw w a z - Rw w b z := by
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    have h1 : Rw (p :: w) (a - b) z = Rd (bs p) (Rw w a - Rw w b) z :=
      Rd_congr (f := Rw w (a - b)) (f' := Rw w a - Rw w b) (fun y hy => ih y hy) (bs p) z hz
    rw [h1]
    have hU := isOpen_GLs.mem_nhds hz
    have da : DifferentiableAt ℝ (Rw w a) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' ha w).contDiffAt hU).differentiableAt (by simp)
    have db : DifferentiableAt ℝ (Rw w b) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hb w).contDiffAt hU).differentiableAt (by simp)
    show fderiv ℝ (Rw w a - Rw w b) z (z * bs p) =
      fderiv ℝ (Rw w a) z (z * bs p) - fderiv ℝ (Rw w b) z (z * bs p)
    have e := (da.hasFDerivAt.sub db.hasFDerivAt).fderiv
    exact DFunLike.congr_fun e (z * bs p)

theorem uniformCauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  intro hS n _ _ μ _ V _ _ _ g x hg hm hc w
  obtain ⟨S, C, hC, hsup⟩ := GlobalTheory.CompanionTheory.PresSobA.SupG.sup_sq_bound hS n μ
  have hbound : ∀ k l, ∀ z ∈ GLs n, ‖Rw w (g k) z - Rw w (g l) z‖ ^ 2 ≤
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l))‖ ^ 2 := by
    intro k l z hz
    have sk := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
    have sl := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg l) w
    have key : ∀ w', ∀ y ∈ GLs n, Rw w' (Rw w (g k) - Rw w (g l)) y =
        Rw (w' ++ w) (g k) y - Rw (w' ++ w) (g l) y := by
      intro w' y hy
      rw [Rw_sub_on sk sl w' y hy, Rw_append, Rw_append]
    have hcl : ∀ w', MemLp (fun y : G n => Rw w' (Rw w (g k) - Rw w (g l)) y.val) 2 μ ∧
        cls μ (Rw w' (Rw w (g k) - Rw w (g l))) =
          cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l)) := by
      intro w'
      refine cls_of_ae μ ?_
      filter_upwards [Lp.coeFn_sub (cls μ (Rw (w' ++ w) (g k))) (cls μ (Rw (w' ++ w) (g l))),
        coe_cls μ (hm k (w' ++ w)), coe_cls μ (hm l (w' ++ w))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, key w' _ (val_mem_GLs y)]
    have := hsup V (Rw w (g k) - Rw w (g l)) (sk.sub sl) (fun w' => (hcl w').1) z hz
    simp only [hcl] at this
    exact this
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hT : Tendsto (fun p : ℕ × ℕ =>
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun p : ℕ × ℕ =>
        C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 (C * ∑ w' ∈ S, ‖x (w' ++ w) - x (w' ++ w)‖ ^ 2)) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun w' _ => ?_)
      exact ((((hc _).comp tendsto_fst).sub ((hc _).comp tendsto_snd)).norm).pow 2
    simpa using h0
  have hev := hT.eventually (gt_mem_nhds (pow_pos hε 2))
  rw [prod_atTop_atTop_eq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 hev
  refine ⟨N, fun k hk l hl z hz => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hbound k l z hz).trans_lt (hN k hk l hl))

end GlobalTheory.CompanionTheory.PresSobA.RwCauchy
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSequenceUniformCauchyStatement

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.sobolev_sequence_uniform_cauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy | exact GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy | (intros; apply GlobalTheory.CompanionTheory.PresSobA.RwCauchy.uniformCauchy <;> assumption)
end
end
end
