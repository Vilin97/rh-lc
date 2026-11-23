module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBallsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCoverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

-- Source module: ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem mem_ovl {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) :
    A.chart j y ∈ ovl A.chart j i :=
  ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hi]⟩

theorem trans_contDiffAt {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ 2 ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) :=
  ((A.trans_contDiffOn j i).contDiffAt ((A.isOpen_ovl j i).mem_nhds (A.mem_ovl hj hi))).of_le
    (by norm_cast)

theorem levi_transfer (la : La) (f : Y → ℝ) (hf : A.SmoothFn f) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt j (fun x => A.ph la j x + f x) y ξ =
      A.leviAt i (fun x => A.ph la i x + f x) y
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)).ofLp := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : ContDiffAt ℂ 2 Φ v0 := A.trans_contDiffAt hj hi
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set h : V n → ℝ := fun u => A.ph la i ((A.chart i).symm u) + f ((A.chart i).symm u)
  have hh : ContDiffAt ℝ 2 h (Φ v0) := by
    rw [hΦv]
    exact (((A.smooth_ph la i).add (hf i)).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).of_le (by norm_cast)
  set G := A.g la j i ∘ (A.chart j).symm
  have hG : ContDiffAt ℂ 2 G v0 :=
    contDiffAt_two_of_holo (A.isOpen_ovl j i) (A.holo_g la j i) hv0
  have hG0 : G v0 ≠ 0 := by
    simp only [G, Function.comp, v0, (A.chart j).left_inv hj]; exact A.g_ne la j i y hj hi
  set u2 : Fin 2 → V n → ℝ := ![fun v => h (Φ v), fun v => Real.log (Complex.normSq (G v))]
  have hu2 : ∀ k, ContDiffAt ℝ 2 (u2 k) v0 := by
    intro k; fin_cases k
    · exact hh.comp v0 (hΦ.restrict_scalars ℝ)
    · exact (contDiffAt_normSq_comp hG).log (Complex.normSq_pos.2 hG0).ne'
  have hev : (fun v => ((A.ph la j ((A.chart j).symm v) + f ((A.chart j).symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((∑ k, u2 k v : ℝ) : ℂ) := by
    filter_upwards [hO] with v hv
    have hxj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hxi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    have hsy : (A.chart i).symm (Φ v) = (A.chart j).symm v := by
      simp only [Φ, Function.comp]; exact (A.chart i).left_inv hxi
    have hne : ‖A.g la j i ((A.chart j).symm v)‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la j i _ hxj hxi)
    simp only [Fin.sum_univ_two, u2, Matrix.cons_val_zero, Matrix.cons_val_one, h, hsy, G,
      Function.comp, A.ph_trans la j i _ hxj hxi, Complex.normSq_eq_norm_sq]
    push_cast; ring
  unfold leviAt
  rw [leviV_congr hev, leviV_ofReal_sum hu2, Fin.sum_univ_two]
  have e1 : u2 0 = fun v => h (Φ v) := rfl
  have e2 : u2 1 = fun v => Real.log (Complex.normSq (G v)) := rfl
  rw [e1, e2, leviV_log_normSq hG hG0, add_zero]
  have hc := leviV_comp (f := fun u => ((h u : ℝ) : ℂ)) (Φ := Φ) (y := v0) ?_ hΦ ξ
  · rw [show (fun v => ((h (Φ v) : ℝ) : ℂ)) = (fun u => ((h u : ℝ) : ℂ)) ∘ Φ from rfl, hc, hΦv]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hh

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmul

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.SemiPosLarge

theorem semipos_add_smul : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  intro n Y _ _ _ _ _ _ ι La _ A H G hH
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH 0
  refine ⟨k0, fun k hk i y hy ξ => ?_⟩
  have hcurv := hk0 k hk

  have hex : ∃ a, C.chi a y ≠ 0 := by
    by_contra hno
    push_neg at hno
    have := C.sum_one y
    simp [hno] at this
  obtain ⟨a, ha⟩ := hex
  have hts : y ∈ tsupport (C.chi a) := subset_tsupport _ (Function.mem_support.2 ha)
  obtain ⟨hsrc, hball⟩ := C.supp a hts
  have hsm : A.SmoothFn (fun _ : Y => (0 : ℝ)) := fun _ => contDiffOn_const
  have ht := A.levi_transfer (G + k • H) (fun _ => (0 : ℝ)) hsm i (C.idx a) hy hsrc ξ
  simp only [add_zero] at ht ⊢
  rw [ht]
  have h1 := hcurv a (A.chart (C.idx a) y) hball
    (fderiv ℂ ((A.chart (C.idx a)) ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp
  rw [(A.chart (C.idx a)).left_inv hsrc, zero_mul] at h1
  exact h1

end GlobalTheory.SemiPosLarge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmulStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  first | exact @GlobalTheory.SemiPosLarge.semipos_add_smul | exact GlobalTheory.SemiPosLarge.semipos_add_smul | (intros; apply GlobalTheory.SemiPosLarge.semipos_add_smul <;> assumption)
end
end
