module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ContDiff ENNReal

namespace GlobalTheory.SkodaIter

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def integrand (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G : V n → ℂ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  exact (hf.mono (HE.target_sub he)).congr (HE.comp_symm_eqOn f he)

theorem normSq_continuousOn {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (fun z => ∑ k, ‖s k z‖ ^ 2) U := by
  exact continuousOn_finsetSum _ (fun k _ => ((hs k).continuousOn.norm).pow 2)

theorem normSq_pos {s : Fin n → V n → ℂ} {z : V n} {k : Fin n} (h : s k z ≠ 0) :
    0 < ∑ k, ‖s k z‖ ^ 2 := by
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2)
    (Finset.single_le_sum (f := fun j => ‖s j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))

theorem extend (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    {ph : V n → ℝ} (hph : ContinuousOn ph U) {t : ℝ} (ht : 0 ≤ t) {G : V n → ℂ}
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ s k0 y ≠ 0})
    (hI : ∫⁻ z in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G z < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ s k0 y ≠ 0} ∧
      ∫⁻ z in U, integrand s ph t G' z < ⊤ := by
  have hM : IsOpen {y | y ∈ U ∧ s k0 y ≠ 0} := HE.isOpen_punct hU (hs k0)
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    have hKU : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hbU : ball p (ε / 2) ⊆ U := ball_subset_closedBall.trans hKU
    have hK : IsCompact (closedBall p (ε / 2)) := isCompact_closedBall p _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((normSq_continuousOn hs).mono hKU)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hph.mono hKU)
    refine ⟨ε / 2, half_pos hε, hbU, ?_⟩
    have hAM : ball p (ε / 2) \ {y | s k0 y = 0} ⊆ {y | y ∈ U ∧ s k0 y ≠ 0} :=
      fun y hy => ⟨hbU hy.1, hy.2⟩
    have hAeq : ball p (ε / 2) \ {y | s k0 y = 0} = ball p (ε / 2) ∩ {y | y ∈ U ∧ s k0 y ≠ 0} := by
      ext y
      exact ⟨fun h => ⟨h.1, hbU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hAm : MeasurableSet (ball p (ε / 2) \ {y | s k0 y = 0}) := by
      rw [hAeq]; exact (isOpen_ball.inter hM).measurableSet
    have hpt : ∀ y ∈ ball p (ε / 2) \ {y | s k0 y = 0},
        ENNReal.ofReal (‖G y‖ ^ 2) ≤ ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y := by
      intro y hy
      have hyK : y ∈ closedBall p (ε / 2) := ball_subset_closedBall hy.1
      have hpos : 0 < ∑ k, ‖s k y‖ ^ 2 := normSq_pos (k := k0) hy.2
      have hfB : ∑ k, ‖s k y‖ ^ 2 ≤ B := (Real.le_norm_self _).trans (hB y hyK)
      have hB0 : 0 < B := hpos.trans_le hfB
      have hphC : ph y ≤ C := (Real.le_norm_self _).trans (hC y hyK)
      have h1 : 1 ≤ (∑ k, ‖s k y‖ ^ 2) ^ (-t) * B ^ t := by
        rw [Real.rpow_neg hpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hpos t)]
        exact Real.rpow_le_rpow hpos.le hfB ht
      have h2 : 1 ≤ Real.exp C * Real.exp (-ph y) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h3 := mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
      simp only [integrand]
      rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hB0 t) (Real.exp_pos C)).le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖G y‖)]
    calc ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0},
            ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hAm hpt)
      _ = ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, integrand s ph t G y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G y :=
          mul_le_mul (le_refl _) (lintegral_mono_set hAM) zero_le zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
  obtain ⟨G', hG'd, hG'eq⟩ := HE.ext_glue hU (s k0) G (hs k0) hgn hG hloc
  refine ⟨G', hG'd, hG'eq, ?_⟩
  have hnull : volume {y | y ∈ U ∧ s k0 y = 0} = 0 := HE.zeros_null hU (hs k0) hgn
  have hae : (U : Set (V n)) =ᵐ[volume] {y | y ∈ U ∧ s k0 y ≠ 0} := by
    have e1 : volume (U \ {y | y ∈ U ∧ s k0 y ≠ 0}) = 0 :=
      measure_mono_null (fun y (hy : y ∈ U \ {y | y ∈ U ∧ s k0 y ≠ 0}) =>
        (⟨hy.1, Classical.byContradiction fun h => hy.2 ⟨hy.1, h⟩⟩ : y ∈ {y | y ∈ U ∧ s k0 y = 0})) hnull
    have e2 : volume ({y | y ∈ U ∧ s k0 y ≠ 0} \ U) = 0 :=
      measure_mono_null (fun y hy => (hy.2 hy.1.1).elim) measure_empty
    exact (ae_eq_set (μ := volume)).2 ⟨e1, e2⟩
  rw [Measure.restrict_congr_set hae]
  rw [lintegral_congr_ae (ae_restrict_of_forall_mem hM.measurableSet
    (fun y hy => show integrand s ph t G' y = integrand s ph t G y by simp only [integrand, hG'eq hy]))]
  exact hI

theorem step (hn : 2 ≤ n) (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (hS : ∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val)
    {ph : V n → ℝ} (hph : ContDiffOn ℝ ∞ ph U)
    (hl : ∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph w : ℝ) : ℂ)) z ξ).re)
    {t : ℝ} (ht : (n : ℝ) - 1 < t) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hI : ∫⁻ z in U, integrand s ph (t + 1) F z < ⊤) :
    ∃ h : Fin n → V n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U ∧
      ∫⁻ z in U, integrand s ph t (h i) z < ⊤) ∧ ∀ z ∈ U, F z = ∑ i, s i z * h i z := by
  obtain ⟨S, hSz⟩ := hS
  have hM : IsOpen {z | z ∈ U ∧ s k0 z ≠ 0} := HE.isOpen_punct hU (hs k0)
  have ht0 : 0 ≤ t := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (‖F x.1‖ ^ 2 * (∑ i, ‖s i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph x.1))
      ∂(vol n S.z) < ⊤ := by
    rw [hSz]
    refine (HE.lintegral_val hM (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖s i y‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph y)))).trans_lt ?_
    exact lt_of_le_of_lt (lintegral_mono_set (fun y hy => hy.1)) hI
  obtain ⟨hh, hhh, hdec, hbound⟩ := ReciprocityTheory.L2DbarEstimates.skoda n _ S n (fun i x => s i x.1) (fun x => ph x.1) t
    (fun x => F x.1) hn
    (fun i => by rw [hSz]; exact holo_val ((hs i).mono (fun y hy => hy.1)))
    (fun x => ⟨k0, x.2.2⟩)
    (by rw [hSz]; exact HE.smoothR_val (hph.mono (fun y hy => hy.1)))
    (by rw [hSz]; intro x ξ; rw [HE.levi_val hM ph x ξ]; exact hl x.1 x.2.1 ξ)
    ht
    (by rw [hSz]; exact holo_val (hF.mono (fun y hy => hy.1)))
    hint
  have hfin := lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
  rw [hSz] at hfin
  have hhv : ∀ i, Holo n (Subtype.val : {z // z ∈ {z | z ∈ U ∧ s k0 z ≠ 0}} → V n) (hh i) := by
    intro i; rw [← hSz]; exact hhh i
  have hGd : ∀ i, DifferentiableOn ℂ (HE.ext0 (hh i)) {z | z ∈ U ∧ s k0 z ≠ 0} :=
    fun i => HE.differentiableOn_extendByZero hM (hhv i)
  have hGi : ∀ i, ∫⁻ y in {z | z ∈ U ∧ s k0 z ≠ 0}, integrand s ph t (HE.ext0 (hh i)) y < ⊤ := by
    intro i
    refine ((HE.lintegral_val hM (fun y => integrand s ph t (HE.ext0 (hh i)) y)).symm.trans_le ?_).trans_lt hfin
    refine lintegral_mono (fun x => ?_)
    simp only [integrand, HE.extendByZeroOnSubset_apply_coe]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  choose H hHd hHeq hHint using fun i => extend hU k0 hs hgn hph.continuousOn ht0 (hGd i) (hGi i)
  refine ⟨H, fun i => ⟨hHd i, hHint i⟩, ?_⟩
  have hDc : ContinuousOn (fun z => F z - ∑ i, s i z * H i z) U :=
    hF.continuousOn.sub (continuousOn_finsetSum _ (fun i _ => (hs i).continuousOn.mul (hHd i).continuousOn))
  intro z hz
  by_contra hne
  have hW := hDc.isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨y, ⟨hyU, hyD⟩, hy0⟩ := hgn _ hW Set.inter_subset_left ⟨z, hz, by simpa [sub_eq_zero] using hne⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyD
  apply hyD
  have hd := hdec ⟨y, hyU, hy0⟩
  dsimp only at hd
  rw [sub_eq_zero, hd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hHeq i ⟨hyU, hy0⟩]
  exact (congrArg (fun w => s i y * w) (HE.extendByZeroOnSubset_apply_coe (hh i) ⟨y, hyU, hy0⟩)).symm

end

end GlobalTheory.SkodaIter
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SmoothWtContDiffOn

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivUpPf

noncomputable section

theorem logSum_contDiffAt {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖g k y‖ ^ 2)) z := by
  have h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)
  exact h.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (∑ k, ‖g k y‖ ^ 2) : ℝ) : ℂ)) z ξ).re := by
  obtain ⟨k, hk⟩ := hne
  have hne' : (fun i => g i z) ≠ 0 := fun h => hk (congrFun h k)
  have h := leviLogNormSq n N g z ξ
    (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'
  simp only [← Complex.normSq_eq_norm_sq]
  have e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) := rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem w_diffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (k : Fin Xa.N) :
    DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k : Fin (nd X)) :
    DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1

theorem logw_contDiffAt (Xa : ArchInM X) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2)) z :=
  logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz)

end

end GlobalTheory.Up.DivUpPf

namespace GlobalTheory.Up

open DivUpPf

end GlobalTheory.Up
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeight

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.DivOne

open GlobalTheory.Up GlobalTheory.Up.DivUpPf

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWtG (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

theorem smoothWtG_contDiffOn (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWtG Xa G x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz G).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

theorem smoothWtG_levi (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWtG Xa G x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWtG
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

theorem inAt_iffG (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb t : ℝ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (fun x => open Classical in if x ∈ X.dom then
      ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-t) else 0) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-t) *
        Real.exp (-smoothWtG Xa G x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdom : cpt X x0 z ∈ X.dom := hz
  have hw := sum_normSq_w_pos Xa hdom
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [if_pos hdom, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hsp,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hsp, ← Real.exp_add, ← Real.exp_add,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold smoothWtG
  ring

end

theorem divOne_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  intro E _ _ _ r X Xa Fl G x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hgn := HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds)
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0) hgn
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hcast : ((nd X + 1 : ℕ) : ℝ) - 1 / 2 = ((nd X : ℝ) - 1 / 2) + 1 := by
    push_cast; ring
  rw [inAt_iffG Xa Fl G x0 bb _ k0 hnull, hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.step Xa.n_ge hU (s := fun k z => Fl.s k (cpt X x0 z)) k0
    (s_diffOn Fl x0) hgn ⟨S, hS⟩ (smoothWtG_contDiffOn Xa G x0 bb)
    (fun z hz ξ => smoothWtG_levi Xa G x0 bb hz ξ (hm z hz ξ)) (t := (nd X : ℝ) - 1 / 2)
    (by linarith) hF hI
  exact ⟨H, fun k => ⟨(hH k).1, (inAt_iffG Xa Fl G x0 bb _ k0 hnull _).2 (hH k).2⟩, hFH⟩

end GlobalTheory.Shares.DivOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeightStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.one_division_upstairs_free_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  first | exact @GlobalTheory.Shares.DivOne.divOne_up | exact GlobalTheory.Shares.DivOne.divOne_up | (intros; apply GlobalTheory.Shares.DivOne.divOne_up <;> assumption)
end
end
