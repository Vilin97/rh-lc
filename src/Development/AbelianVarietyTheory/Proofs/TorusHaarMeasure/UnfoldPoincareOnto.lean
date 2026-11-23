module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
import Mathlib.Algebra.Order.Star.Real
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeDensity
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeSqrtWeightNearOrthonormal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PairUnfoldOfUnfold
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSummableIsBddSec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegralEqIntegralTsumOfLintegral

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnfoldComplex

theorem integral_eq_integral_tsum_of_lintegral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (f : α → ℂ) (g : ι → α → ℂ) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (H : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (f z) ∂μ = ∫⁻ z, ∑' i, φ (g i z) ∂ν)
    (hi : Integrable f μ) : ∫ z, f z ∂μ = ∫ z, ∑' i, g i z ∂ν := by
  have hmap : μ.map f = Measure.sum fun i => ν.map (g i) := by
    ext s hs
    have hφ : Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hs
    have h1 := H _ hφ
    rw [lintegral_tsum (f := fun i z => s.indicator (1 : ℂ → ℝ≥0∞) (g i z))
      fun i => (hφ.comp (hg i)).aemeasurable] at h1
    rw [Measure.sum_apply _ hs, ← lintegral_indicator_one hs, lintegral_map hφ hf, h1]
    refine tsum_congr fun i => ?_
    rw [← lintegral_indicator_one hs, lintegral_map hφ (hg i)]
  have hfin : ∑' i, ∫⁻ z, ‖g i z‖ₑ ∂ν ≠ ⊤ := by
    have h1 := H (fun w => ‖w‖ₑ) measurable_enorm
    rw [lintegral_tsum fun i => (hg i).enorm.aemeasurable] at h1
    rw [← h1]
    exact hi.2.ne
  have hid : Integrable (fun w : ℂ => w) (μ.map f) :=
    (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mpr hi
  rw [integral_tsum (fun i => (hg i).aestronglyMeasurable) hfin]
  calc ∫ z, f z ∂μ = ∫ w, w ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∑' i, ∫ w, w ∂(ν.map (g i)) := by
        rw [hmap] at hid ⊢
        exact integral_sum_measure hid
    _ = ∑' i, ∫ z, g i z ∂ν :=
        tsum_congr fun i => integral_map (hg i).aemeasurable aestronglyMeasurable_id

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun y : Frame Ψ r =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  have hM : Continuous fun y : Frame Ψ r => mat y τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem unfold_integral :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) := by
  intro H r X x0 ho FF hFF h hm hinv hint
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  refine integral_eq_integral_tsum_of_lintegral (muF X x0) ((muF X x0).restrict FF)
    (fun z => h (cpt X x0 z)) (fun (γ : X.Γ) z => h (lact γ.1 (cpt X x0 z))) (hm.comp hc)
    (fun γ => hm.comp ((continuous_lact γ.1).measurable.comp hc)) ?_ hint
  intro φ hφ
  exact H r X x0 ho FF hFF (fun x => φ (h x)) (hφ.comp hm)
    (fun x hx b hb => by simp only [hinv x hx b hb])

end GlobalTheory.UnfoldComplex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaUnfoldOfUnfoldOfKappa

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kaUnfold_of_unfold_of_kappa :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (KaUnfoldStatement (E := E)) := by
  intro hU hK r X x0 ho hP FF hFF bb hbb
  obtain ⟨κ, hκm, hκ1, hκB, hκka, ⟨C, hC, hsum⟩, -⟩ := hK r X x0 ho hP bb hbb
  refine ⟨C, hC, fun φ hφm hφB hφΓ => ?_⟩
  have h1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (κ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 :=
    lintegral_congr_ae ((OntoH.ae_mem_Om X x0).mono fun z hz => by simp only [hκka z hz])
  have h2 := hU r X x0 ho FF hFF (fun x => ENNReal.ofReal (κ x) * φ x)
    (hκm.ennreal_ofReal.mul hφm) (fun x hx b hb => by simp only [hκB x hx b hb, hφB x hx b hb])
  rw [h1, h2, ← lintegral_const_mul' _ _ hC.ne]
  refine setLIntegral_mono' hFF.1 fun z hz => ?_
  have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  calc ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 (cpt X x0 z))) * φ (lact γ.1 (cpt X x0 z))
      ≤ ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z)))) * φ (cpt X x0 z) := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        rw [hφΓ γ.1 γ.2 _ hx]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        obtain ⟨h0, h1⟩ := hκ1 _ (OntoS.dom_lact X γ.2 hx)
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
    _ = (∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z))))) * φ (cpt X x0 z) :=
        ENNReal.tsum_mul_right
    _ ≤ C * φ (cpt X x0 z) := mul_le_mul' (hsum _ hx) le_rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealTsumSqLeTsumDivMulTsum

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ofReal_tsum_sq_le_tsum_div_mul_tsum {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by
  have ht : Filter.Tendsto (fun s : Finset ι => ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((∑' i, a i) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.pow hs.hasSum 2)
  refine le_of_tendsto' ht fun s => ?_
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / Real.sqrt (k i))
      (fun i => Real.sqrt (k i))
    have e1 : ∀ i, a i / Real.sqrt (k i) * Real.sqrt (k i) = a i := fun i =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hk i)).ne'
    have e2 : ∀ i, Real.sqrt (k i) ^ 2 = k i := fun i => Real.sq_sqrt (hk i).le
    simp only [e1, div_pow, e2] at h0
    exact h0
  have hd : ∀ i, 0 ≤ a i ^ 2 / k i := fun i => div_nonneg (sq_nonneg _) (hk i).le
  calc ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)
      ≤ ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i) := ENNReal.ofReal_le_ofReal h1
    _ = (∑ i ∈ s, ENNReal.ofReal (a i ^ 2 / k i)) * ∑ i ∈ s, ENNReal.ofReal (k i) := by
      rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hd i),
        ENNReal.ofReal_sum_of_nonneg fun i _ => hd i,
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hk i).le]
    _ ≤ _ := mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s)

theorem ae_mem_OmF_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (OntoB.isOpen_OmF X x0).measurableSet)

theorem poincare_sqIntegrable_fundSet :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) := by
  intro hunf r X x0 hx0 la W bb κ hκ hW _ F P hF hP hPF hsum FF hFF
  obtain ⟨hκm, hκp, hκB, hκa, ⟨C, hC, hκC⟩, -⟩ := hκ
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ with hψ
  have hψm : Measurable ψ :=
    (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul hκm.inv.ennreal_ofReal
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [hψ, OntoE.phiF_B X hP.2 hW x hx b hb, hκB x hx b hb]
  have hψd : ∀ x ∈ X.dom, ψ x = ENNReal.ofReal (‖P x‖ ^ 2 / κ x) * W x := by
    intro x hx
    simp only [hψ, OntoE.phiF_dom X P W hx]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hfin : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hF
    filter_upwards [ae_mem_OmF_muF X x0] with z hz
    rw [hψd _ hz, hPF z hz, hκa z hz]
  rw [hunf r X x0 hx0 FF hFF ψ hψm hψB] at hfin
  have hpt : ∀ x ∈ X.dom, ENNReal.ofReal (‖poin X la P x‖ ^ 2) * W x ≤
      C * ∑' γ : X.Γ, ψ (lact γ.1 x) := by
    intro x hx
    have hγx : ∀ γ : X.Γ, lact γ.1 x ∈ X.dom := fun γ => OntoS.dom_lact X γ.2 hx
    have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := by
      intro γ
      rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have h1 : ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ :=
      norm_tsum_le_tsum_norm (hsum x hx)
    have h2 := ofReal_tsum_sq_le_tsum_div_mul_tsum _ (fun γ : X.Γ => κ (lact γ.1 x)) (hsum x hx)
      fun γ => (hκp _ (hγx γ)).1
    have h3 : ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 x)) ≤ C := by
      refine le_trans (ENNReal.tsum_le_tsum fun γ => ENNReal.ofReal_le_ofReal ?_) (hκC x hx)
      obtain ⟨h0, h1⟩ := hκp _ (hγx γ)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have h4 : ∑' γ : X.Γ, ψ (lact γ.1 x) =
        (∑' γ : X.Γ, ENNReal.ofReal (‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ ^ 2 / κ (lact γ.1 x))) *
          W x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [hψd _ (hγx γ), hn, hW.2.2 γ.1 γ.2 x hx]
    rw [h4, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    calc ENNReal.ofReal (‖poin X la P x‖ ^ 2)
        ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      _ ≤ _ := h2
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' h3 le_rfl
  unfold InFF
  calc _ ≤ ∫⁻ z in FF, C * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 fun z hz => hpt _ (hFF.2.1 hz)
    _ = C * ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        lintegral_const_mul' _ _ hC.ne
    _ < ⊤ := ENNReal.mul_lt_top hC hfin

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinStatementOf

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoincareAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_chi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h := congrArg norm (hpow γ hγ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem cpt_lact {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)
  simp only [mat, lact, cpt, rmul]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ))
    (Matrix.of (nmat X z τ))

theorem dom_of_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : lact γ x ∈ X.dom) : x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have h := (hx τ).1
    rw [e1, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [OntoS.gram_lact X hγ] at this

theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

theorem phla_lact {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) : phla X la (lact γ x) = phla X la x := by
  unfold phla Data.nfac dmin
  simp only [OntoS.gram_lact X hγ]

theorem poin_mul {r : ℕ} (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ)
    (hg : X.IsSec la' g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  have h1 : X.χ la' γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la' γ.2]; exact one_ne_zero
  have h2 : X.χ la γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la γ.2]; exact one_ne_zero
  simp only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  field_simp

theorem poinStatement_of :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (κ : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ), IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) → (PoinStatement (E := E)) := by
  intro hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF
  obtain ⟨κ, hκ⟩ := hκ r X x0 ho hPD bb hbb
  obtain ⟨hs, hb⟩ := hbdd r X la κ P hP hκ.2.2.2.2.1
    (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)
  refine ⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_,
    fun la' g hg x hx => poin_mul X la la' P g hg hx⟩
  obtain ⟨C, hC⟩ := hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1
  obtain ⟨K, hK, hKs⟩ := hκ.2.2.2.2.1
  refine ⟨C * K.toReal, fun x hx hxo => ?_⟩
  set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS
  have hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤
      ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) := by
    intro γ
    rw [← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
    refine (hC _ (isOrth_lact X γ.2 hxo)).trans ?_
    rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]
    gcongr
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_
    rw [cpt_lact] at hd ⊢
    have hd' := dom_of_lact X γ.2 hd
    rw [phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']
    exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))
  calc ENNReal.ofReal ‖poin X la P x‖
      = ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := ofReal_norm _
    _ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' γ : X.Γ, ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal C * S * K := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact hKs x hx
    _ = ENNReal.ofReal (C * K.toReal) * S := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]

end GlobalTheory.PoincareAssembly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.PoincareClosed

theorem unfold_poincare_onto :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) ∧ (KaUnfoldStatement (E := E)) ∧ (PairUnfoldStatement (E := E)) ∧ (PoinStatement (E := E)) ∧ (OntoStatement (E := E)) := by
  obtain ⟨-, hMeas, -, hExt⟩ := GlobalTheory.FrameMeasureClosed.measure_statements (E := E)
  have hUnf := GlobalTheory.Unfold.lintegral_unfold (E := E) hMeas
  have hκ := GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic
    GlobalTheory.MinorRatioNear.minorRatio_near (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep)
  have hKa : KaUnfoldStatement (E := E) := GlobalTheory.kaUnfold_of_unfold_of_kappa hUnf hκ
  have hPair : PairUnfoldStatement (E := E) :=
    GlobalTheory.PairUnfold.pairUnfold_of_unfold (GlobalTheory.UnfoldComplex.unfold_integral hUnf) hKa
  have hN := GlobalTheory.NormFactor.nfac_transform (E := E)
  have hPoin : PoinStatement (E := E) :=
    GlobalTheory.PoincareAssembly.poinStatement_of hκ
      (GlobalTheory.PointSup.pointSup hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.norm_le_sqrt_weight_near_orthonormal hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.PoinHol.poin_summable_isBddSec GlobalTheory.differentiableOn_tsum_of_norm_le hN)
      (GlobalTheory.poincare_sqIntegrable_fundSet hUnf)
  exact ⟨hUnf, hKa, hPair, hPoin,
    onto_of hPoin hExt RhGradFStatement_holds exhaustG_holds hKa hPair bigCellStatement_holds
      OmFConnStatement_holds⟩

end GlobalTheory.PoincareClosed
end
end
