module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KDensB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Measure.WithDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.UnGrpHaarProbExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KDensC

section

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

section KDC

variable {E X : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def kdNu (m : Measure X) (f : E → X) (U : Set E) : Measure E :=
  Measure.map (Subtype.val : U → E) (Measure.comap (fun x : U => f x) m)

lemma kdNu_apply {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) {A : Set E} (hA : MeasurableSet A) : kdNu m f U A = m (f '' (A ∩ U)) := by
  have hI : Function.Injective (fun x : U => f x) := fun a b h => Subtype.ext (hinj a.2 b.2 h)
  have hM : ∀ s : Set U, MeasurableSet s → MeasurableSet ((fun x : U => f x) '' s) := by
    intro s hs
    have e : (fun x : U => f x) '' s = f '' (Subtype.val '' s) := by rw [image_image]
    rw [e]
    have hsub : Subtype.val '' s ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    exact (hU.subtype_image hs).image_of_continuousOn_injOn (hf.mono hsub) (hinj.mono hsub)
  rw [kdNu, Measure.map_apply measurable_subtype_coe hA,
    Measure.comap_apply _ hI hM _ (measurable_subtype_coe hA)]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hxA, rfl⟩; exact ⟨x, ⟨hxA, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxA, hx⟩, rfl⟩; exact ⟨⟨x, hx⟩, hxA, rfl⟩

lemma kdNu_finite {m : Measure X} [IsFiniteMeasure m] {f : E → X} {U : Set E} (hU : MeasurableSet U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsFiniteMeasure (kdNu m f U) :=
  ⟨by rw [kdNu_apply hU hf hinj MeasurableSet.univ]; exact measure_lt_top _ _⟩

lemma kdNu_le {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (c : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → m (f '' A) ≤ c * lam A) : kdNu m f U ≤ c • lam.restrict U := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [kdNu_apply hU hf hinj hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  exact h _ inter_subset_right (hA.inter hU)

lemma kdNu_ge {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (d : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → d * lam A ≤ m (f '' A)) : d • lam.restrict U ≤ kdNu m f U := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [kdNu_apply hU hf hinj hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  exact h _ inter_subset_right (hA.inter hU)

end KDC

section KDC2

variable {E₁ E₂ X₁ X₂ : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
  [TopologicalSpace X₁] [T2Space X₁] [MeasurableSpace X₁] [BorelSpace X₁] [SecondCountableTopology X₁]
  [TopologicalSpace X₂] [T2Space X₂] [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₂]

lemma kdNu_prod {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) :
    (kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂) = kdNu (m₁.prod m₂) (Prod.map f₁ f₂) (U₁ ×ˢ U₂) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) (hs.prod ht),
    kdNu_apply hU₁ hf₁ hi₁ hs, kdNu_apply hU₂ hf₂ hi₂ ht, prod_inter_prod, prodMap_image_prod,
    Measure.prod_prod]

theorem kd_prod_bounds {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (lam₁ : Measure E₁) (lam₂ : Measure E₂) [SigmaFinite lam₁] [SigmaFinite lam₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) (c₁ d₁ c₂ d₂ : ℝ≥0∞)
    (h₁ : ∀ A ⊆ U₁, MeasurableSet A → m₁ (f₁ '' A) ≤ c₁ * lam₁ A ∧ d₁ * lam₁ A ≤ m₁ (f₁ '' A))
    (h₂ : ∀ A ⊆ U₂, MeasurableSet A → m₂ (f₂ '' A) ≤ c₂ * lam₂ A ∧ d₂ * lam₂ A ≤ m₂ (f₂ '' A))
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hBU : B ⊆ U₁ ×ˢ U₂) :
    (m₁.prod m₂) (Prod.map f₁ f₂ '' B) ≤ c₁ * c₂ * (lam₁.prod lam₂) B ∧
      d₁ * d₂ * (lam₁.prod lam₂) B ≤ (m₁.prod m₂) (Prod.map f₁ f₂ '' B) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  have e : (m₁.prod m₂) (Prod.map f₁ f₂ '' B) = ((kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂)) B := by
    rw [kdNu_prod hU₁ hU₂ hf₁ hf₂ hi₁ hi₂,
      kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) hB, inter_eq_left.2 hBU]
  have hs : ∀ a b : ℝ≥0∞,
      ((a • lam₁.restrict U₁).prod (b • lam₂.restrict U₂)) B = a * b * (lam₁.prod lam₂) B := by
    intro a b
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict, smul_smul,
      Measure.smul_apply, Measure.restrict_apply hB, inter_eq_left.2 hBU, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e, ← hs c₁ c₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_le hU₁ hf₁ hi₁ lam₁ c₁ fun A hA hm => (h₁ A hA hm).1)
      (kdNu_le hU₂ hf₂ hi₂ lam₂ c₂ fun A hA hm => (h₂ A hA hm).1)) B
  · rw [e, ← hs d₁ d₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_ge hU₁ hf₁ hi₁ lam₁ d₁ fun A hA hm => (h₁ A hA hm).2)
      (kdNu_ge hU₂ hf₂ hi₂ lam₂ d₂ fun A hA hm => (h₂ A hA hm).2)) B

end KDC2

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KdMeasImageProd

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma kd_volU_pos (M : ℕ) : 0 < volU M :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

def kdTM {N : ℕ} (u : UNgrp N) : Fin N → Fin N → ℂ := Matrix.of.symm (toM u)

lemma continuous_kdTM {N : ℕ} : Continuous (kdTM (N := N)) := continuous_toM _

lemma kd_factor {N : ℕ} (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ)
    (hη : 0 < η) : ∃ r > 0, Set.InjOn (kdF N) (Metric.ball 0 r) ∧
      ∀ A ⊆ Metric.ball (0 : UCo N) r, MeasurableSet A →
        (μ.map kdTM) (kdF N '' A) ≤ ENNReal.ofReal ((1 + η) / volU N) * volume A ∧
          ENNReal.ofReal ((1 - η) / volU N) * volume A ≤ (μ.map kdTM) (kdF N '' A) := by
  obtain ⟨δ, hδ, hd⟩ := volU_density μ η hη
  obtain ⟨r, hr, hinj⟩ := kdF_injOn (N := N)
  refine ⟨min δ r, lt_min hδ hr, hinj.mono (Metric.ball_subset_ball (min_le_right _ _)), ?_⟩
  intro A hA hAm
  have hAr : A ⊆ Metric.ball 0 r := hA.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hmeas : MeasurableSet (kdF N '' A) :=
    hAm.image_of_continuousOn_injOn continuous_kdF.continuousOn (hinj.mono hAr)
  have e : kdTM ⁻¹' (kdF N '' A) = {k : UNgrp N | ∃ x ∈ A, toM k = NormedSpace.exp (skMat x)} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (Matrix.of.symm.injective h).symm⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [kdF, kdTM, h]⟩
  rw [Measure.map_apply continuous_kdTM.measurable hmeas, e]
  refine hd A hAm fun x hx => ?_
  have := hA hx
  rw [Metric.mem_ball, dist_zero_right] at this
  exact this.trans_le (min_le_left _ _)

lemma kd_meas_image_prod {E₁ E₂ X : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁]
    [BorelSpace E₁] [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] {f : E₁ × E₂ → X}
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hf : ContinuousOn f B) (hi : Set.InjOn f B) :
    MeasurableSet (f '' B) :=
  hB.image_of_continuousOn_injOn hf hi

theorem dk_density (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (KCo ε), MeasurableSet B → (∀ w ∈ B, ‖w‖ < δ) →
      dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} ≤
          ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) * volume B ∧
        ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) * volume B ≤
          dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} := by
  obtain ⟨μp, hHp, hPp⟩ := unGrp_haarProb_exists (pOf ε)
  obtain ⟨μq, hHq, hPq⟩ := unGrp_haarProb_exists (qOf ε)
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by linarith) (by norm_num)
  have hη'1 : η' ≤ η / 3 := min_le_left _ _
  have hη'2 : η' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨rp, hrp, hip, hp⟩ := kd_factor μp η' hη'0
  obtain ⟨rq, hrq, hiq, hq⟩ := kd_factor μq η' hη'0
  refine ⟨min rp rq, lt_min hrp hrq, fun B hB hBδ => ?_⟩
  set S := {k : KG ε | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} with hS
  set B' : Set (UCo (pOf ε) × UCo (qOf ε)) := kdT ε '' B with hB'
  have hB'm : MeasurableSet B' := (kdT ε).measurableSet_image.2 hB
  have hvol : volume B' = volume B := by
    rw [hB', MeasurableEquiv.image_eq_preimage_symm]
    exact (MeasurePreserving.symm _ (kdT_mp ε)).measure_preimage hB.nullMeasurableSet
  have hB'U : B' ⊆ Metric.ball 0 rp ×ˢ Metric.ball 0 rq := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hBδ w hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, kdT_fst]
      exact (norm_kdCoS_le w true).trans_lt (h1.trans_le (min_le_left _ _))
    · rw [Metric.mem_ball, dist_zero_right, kdT_snd]
      exact (norm_kdCoS_le w false).trans_lt (h1.trans_le (min_le_right _ _))
  have hpre : (kdPsi ε) ⁻¹' S = Prod.map kdTM kdTM ⁻¹' (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, Set.mem_image, hB']
    constructor
    · rintro ⟨w, hw, he⟩
      rw [toMK_kdPsi, kMat_eq_kdD, exp_kdD] at he
      have he' := kdD_injective ε he
      refine ⟨kdT ε w, ⟨w, hw, rfl⟩, Prod.ext ?_ ?_⟩
      · show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1)
        rw [kdT_fst]; exact congrArg _ (congrFun he' true).symm
      · show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2)
        rw [kdT_snd]; exact congrArg _ (congrFun he' false).symm
    · rintro ⟨z, ⟨w, hw, rfl⟩, hz⟩
      refine ⟨w, hw, ?_⟩
      have h1 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1) :=
        congrArg Prod.fst hz
      have h2 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2) :=
        congrArg Prod.snd hz
      rw [kdT_fst] at h1
      rw [kdT_snd] at h2
      rw [toMK_kdPsi, kMat_eq_kdD, exp_kdD]
      congr 1
      funext s
      cases s
      · exact (Matrix.of.symm.injective h2).symm
      · exact (Matrix.of.symm.injective h1).symm
  have hYm : MeasurableSet (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') :=
    kd_meas_image_prod hB'm (continuous_kdF.prodMap continuous_kdF).continuousOn
      ((hip.prodMap hiq).mono hB'U)
  have hdk : dk ε S = ((μp.map kdTM).prod (μq.map kdTM)) (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') := by
    rw [kd_dk_eq_map ε μp μq]
    have hc : (⇑(kdPsi ε)) = ⇑(kdHomeo ε).toMeasurableEquiv := rfl
    rw [hc, MeasurableEquiv.map_apply, ← hc, hpre,
      Measure.map_prod_map _ _ continuous_kdTM.measurable continuous_kdTM.measurable,
      Measure.map_apply (continuous_kdTM.measurable.prodMap continuous_kdTM.measurable) hYm]
  obtain ⟨hup, hlo⟩ := kd_prod_bounds (m₁ := μp.map kdTM) (m₂ := μq.map kdTM) volume volume
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet continuous_kdF.continuousOn
    continuous_kdF.continuousOn hip hiq _ _ _ _ hp hq hB'm hB'U
  have hvp := kd_volU_pos (pOf ε)
  have hvq := kd_volU_pos (qOf ε)
  have hpq : 0 < volU (pOf ε) * volU (qOf ε) := mul_pos hvp hvq
  have hvol' : (volume.prod volume) B' = volume B := hvol
  rw [hvol'] at hup hlo
  rw [hdk]
  have hcu : ENNReal.ofReal ((1 + η') / volU (pOf ε)) * ENNReal.ofReal ((1 + η') / volU (qOf ε)) ≤
      ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right (by nlinarith) hpq.le
  have hcl : ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) ≤
      ENNReal.ofReal ((1 - η') / volU (pOf ε)) * ENNReal.ofReal ((1 - η') / volU (qOf ε)) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) hvp.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right (by nlinarith) hpq.le
  exact ⟨hup.trans (by gcongr), le_trans (by gcongr) hlo⟩

end ReciprocityTheory.ChartRestriction.DS
end
end
end
