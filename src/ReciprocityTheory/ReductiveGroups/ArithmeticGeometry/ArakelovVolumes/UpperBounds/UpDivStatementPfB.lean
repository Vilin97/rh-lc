module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntegrableOn

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfA

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  have hsub : e.target ⊆ U := by
    intro y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  refine (hf.mono hsub).congr (fun y hy => ?_)
  show f (e.symm y).1 = f y
  rw [chart_z_symm n Subtype.val e he y hy]

theorem skoda_open (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (t : ℝ) (f : V n → ℂ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (ht : (p : ℝ) - 1 < t) (hf : DifferentiableOn ℂ f U)
    (hI : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) < ⊤) :
    ∃ hh : Fin p → V n → ℂ, (∀ i, DifferentiableOn ℂ (hh i) U) ∧
      (∀ y ∈ U, f y = ∑ i, g i y * hh i y) ∧
      ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) ≤
        ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) := by
  classical
  have hzl : IsLocalHomeomorph (Subtype.val : U → V n) := hz ▸ S.isLocalHomeomorph
  have hemb : MeasurableEmbedding (Subtype.val : U → V n) := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hvol : vol n (Subtype.val : U → V n) = (volume : Measure (V n)).comap Subtype.val := by
    ext A hA
    rw [vol_image n Subtype.val hzl Set.univ isOpen_univ Subtype.val_injective.injOn A hA (Set.subset_univ _),
      hemb.comap_apply]
  have htgt : ∀ (e : OpenPartialHomeomorph U (V n)), IsChart n Subtype.val e → e.target ⊆ U := by
    intro e he y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  have hleviC : ∀ (g₁ g₂ : V n → ℂ) (y : V n), g₁ =ᶠ[𝓝 y] g₂ → ∀ ξ, leviV n g₁ y ξ = leviV n g₂ y ξ := by
    intro g₁ g₂ y h ξ
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [wd_congr (h := h.eventually_nhds.mono fun y' h' => wdb_congr (h := h'))]
  have hsm : SmoothR n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro e he
    have hc : ContDiffOn ℝ ∞ (fun y => ((ph0 y : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hph
    refine (hc.mono (htgt e he)).congr (fun y hy => ?_)
    show ((ph0 (e.symm y).1 : ℝ) : ℂ) = ((ph0 y : ℝ) : ℂ)
    rw [chart_z_symm n Subtype.val e he y hy]
  have hlev : LeviNonneg n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro x ξ
    obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl x
    rw [levi_eq_leviV n Subtype.val e he _ x hxe ξ]
    have heq : (fun y => ((ph0 (e.symm y).1 : ℝ) : ℂ)) =ᶠ[𝓝 x.1] fun y => ((ph0 y : ℝ) : ℂ) := by
      have hxt : x.1 ∈ e.target := by
        rw [he hxe]
        exact e.map_source hxe
      filter_upwards [e.open_target.mem_nhds hxt] with y hy
      rw [chart_z_symm n Subtype.val e he y hy]
    rw [hleviC _ _ _ heq ξ]
    exact hl x.1 x.2 ξ
  have hI' : ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z < ⊤ := by
    rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
      (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    exact hI
  obtain ⟨hh, hhH, hhf, hhI⟩ := skoda n U S p (fun i x => g i x.1) (fun x => ph0 x.1) t (fun x => f x.1) hp
    (fun i => by rw [hz]; exact holo_val (hg i)) (fun x => hnz x.1 x.2) hsm hlev ht (by rw [hz]; exact holo_val hf) hI'
  refine ⟨fun i y => if h : y ∈ U then hh i ⟨y, h⟩ else 0, fun i y hy => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl ⟨y, hy⟩
    have hH : DifferentiableOn ℂ (hh i ∘ e.symm) e.target := by
      have := hhH i
      rw [hz] at this
      exact this e he
    have hyt : y ∈ e.target := by
      have h1 : e ⟨y, hy⟩ = y := (he hxe).symm
      rw [← h1]
      exact e.map_source hxe
    have hD := (hH y hyt).differentiableAt (e.open_target.mem_nhds hyt)
    refine (hD.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [e.open_target.mem_nhds hyt] with w hw
    have hwU : w ∈ U := htgt e he hw
    rw [dite_eq_left hwU]
    show hh i ⟨w, hwU⟩ = hh i (e.symm w)
    congr 1
    exact Subtype.ext (chart_z_symm n Subtype.val e he w hw).symm
  · have := hhf ⟨y, hy⟩
    simpa [hy] using this
  · have hL : ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖(if h : y ∈ U then hh i ⟨y, h⟩ else 0)‖ ^ 2) *
        (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh i x‖ ^ 2) * (∑ i, ‖g i x.1‖ ^ 2) ^ (-t) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, ← lintegral_subtype_comap hU.measurableSet]
      refine lintegral_congr fun x => ?_
      simp [x.2]
    have hR : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
        (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    rw [hL, hR]
    exact hhI

end UpDivA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfB

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivB

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  calc ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

def stp {p : ℕ} (α : Fin p → ℕ) (k : Fin p) : Fin p → ℕ := fun i => α i + if i = k then 1 else 0

theorem mem_step {p N : ℕ} {α : Fin p → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple p N) (k : Fin p) :
    stp α k ∈ Finset.Nat.antidiagonalTuple p (N + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hα ⊢
  simp [stp, Finset.sum_add_distrib, hα]

theorem pow_step {p : ℕ} (g : Fin p → ℂ) (α : Fin p → ℕ) (k : Fin p) :
    ∏ i, g i ^ stp α k i = (∏ i, g i ^ α i) * g k := by
  simp only [stp, pow_add, Finset.prod_mul_distrib]
  congr 1
  have h : ∀ i, g i ^ (if i = k then 1 else 0) = if i = k then g i else 1 := by
    intro i; split_ifs <;> simp
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem iter_div (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (τ0 : ℝ) : ∀ (N : ℕ), (p : ℝ) - 1 < τ0 - N - 1 + 1 →
    ∀ F : V n → ℂ, DifferentiableOn ℂ F U →
    ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-τ0) * Real.exp (-ph0 y)) < ⊤ →
    ∃ H : (Fin p → ℕ) → V n → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple p N, DifferentiableOn ℂ (H α) U ∧
        ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - N)) *
          Real.exp (-ph0 y)) < ⊤) ∧
      ∀ y ∈ U, F y = ∑ α ∈ Finset.Nat.antidiagonalTuple p N, (∏ i, g i y ^ α i) * H α y := by
  have hSpos : ∀ y ∈ U, 0 < ∑ i, ‖g i y‖ ^ 2 := by
    intro y hy
    obtain ⟨i, hi⟩ := hnz y hy
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hScont : ContinuousOn (fun y => ∑ i, ‖g i y‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => ((hg i).continuousOn.norm).pow 2
  intro N
  induction N with
  | zero =>
    intro _ F hF hI
    refine ⟨fun _ => F, fun α hα => ⟨hF, by simpa using hI⟩, fun y _ => ?_⟩
    rw [Finset.Nat.antidiagonalTuple_zero_right]
    simp
  | succ N ih =>
    intro hN F hF hI
    have hN' : (p : ℝ) - 1 < τ0 - N - 1 + 1 := by push_cast at hN; linarith
    obtain ⟨H, hH, hid⟩ := ih hN' F hF hI
    set t : ℝ := τ0 - N - 1 with htdef
    have ht : (p : ℝ) - 1 < t := by rw [htdef]; push_cast at hN; linarith
    have hstep : ∀ α ∈ Finset.Nat.antidiagonalTuple p N, ∃ hh : Fin p → V n → ℂ,
        (∀ i, DifferentiableOn ℂ (hh i) U) ∧ (∀ y ∈ U, H α y = ∑ i, g i y * hh i y) ∧
        ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 y)) < ⊤ := by
      intro α hα
      have hIα : ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) *
          Real.exp (-ph0 y)) < ⊤ := by
        have e : -(t + 1) = -(τ0 - N) := by rw [htdef]; ring
        rw [e]; exact (hH α hα).2
      obtain ⟨hh, hhd, hhid, hhest⟩ := UpDivA.skoda_open hU S hz g ph0 t (H α) hp hg hnz hph hl ht
        (hH α hα).1 hIα
      exact ⟨hh, hhd, hhid, lt_of_le_of_lt hhest (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIα)⟩
    choose! hh hhd hhid hhI using hstep
    set A := Finset.Nat.antidiagonalTuple p N with hA
    obtain ⟨w, hw⟩ : ∃ w : V n → ℝ, w = fun y => (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y) :=
      ⟨_, rfl⟩
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      rw [hw]; exact mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
        (Real.exp_pos _).le
    have hwc : ContinuousOn w U := by
      rw [hw]
      exact (hScont.rpow_const fun y hy => Or.inl (hSpos y hy).ne').mul
        (Real.continuous_exp.comp_continuousOn hph.continuousOn.neg)
    refine ⟨fun β y => ∑ α ∈ A, ∑ k, if stp α k = β then hh α k y else 0,
      fun β _ => ⟨?_, ?_⟩, ?_⟩
    · have hk : ∀ α ∈ A, ∀ k ∈ (Finset.univ : Finset (Fin p)),
          DifferentiableOn ℂ (fun y => if stp α k = β then hh α k y else 0) U := by
        intro α hα k _
        by_cases hk : stp α k = β
        · simp only [hk, if_true]; exact hhd α hα k
        · simp only [hk, if_false]; exact differentiableOn_const (c := (0 : ℂ))
      have hα : ∀ α ∈ A, DifferentiableOn ℂ
          (fun y => ∑ k, if stp α k = β then hh α k y else 0) U := fun α hα =>
        (DifferentiableOn.sum (u := Finset.univ) (A := fun k y => if stp α k = β then hh α k y else 0)
          (hk α hα)).congr fun y _ => by simp [Finset.sum_apply]
      exact (DifferentiableOn.sum (u := A)
        (A := fun α y => ∑ k, if stp α k = β then hh α k y else 0) hα).congr fun y _ => by
          simp [Finset.sum_apply]
    · set C : ℝ := ((A ×ˢ (Finset.univ : Finset (Fin p))).card : ℝ) with hC
      have hpt : ∀ y, ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          ≤ C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2 := by
        intro y
        rw [← Finset.sum_product']
        refine (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact le_rfl
        · simp
      have hbound : ∀ y, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          * w y) ≤ ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y) := by
        intro y
        rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
          by positivity) (hw0 y)), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y
            ≤ (C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2) * w y := mul_le_mul_of_nonneg_right (hpt y) (hw0 y)
          _ = C * ∑ α ∈ A, (∑ k, ‖hh α k y‖ ^ 2) * w y := by rw [mul_assoc, Finset.sum_mul]
      have hfin : ∫⁻ y in U, ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y)
          < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [lintegral_finsetSum']
        · refine ENNReal.sum_lt_top.mpr fun α hα => ?_
          have := hhI α hα
          rw [hw]
          simpa [mul_assoc] using this
        · intro α hα
          have hc : ContinuousOn (fun y => (∑ k, ‖hh α k y‖ ^ 2) * w y) U :=
            (continuousOn_finsetSum _ fun k _ => ((hhd α hα k).continuousOn.norm).pow 2).mul hwc
          exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hU.measurableSet
      have e2 : (fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y))) =
          fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y) := by
        funext y
        rw [hw, mul_assoc]
        congr 4
        rw [htdef]; push_cast; ring
      show ∫⁻ y in U, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y)) < ⊤
      rw [e2]
      exact lt_of_le_of_lt (lintegral_mono hbound) hfin
    · intro y hy
      rw [hid y hy]
      have h1 : ∀ α ∈ A, (∏ i, g i y ^ α i) * H α y =
          ∑ k, (∏ i, g i y ^ stp α k i) * hh α k y := by
        intro α hα
        rw [hhid α hα y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_step]; ring
      rw [Finset.sum_congr rfl h1]
      symm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (mem_step hα k)]

end UpDivB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end
