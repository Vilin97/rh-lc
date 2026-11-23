module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRA
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.MeasureTheory.Function.Jacobian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LintegralGaussTri
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QrMapMeasurableSetImage
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUSetMeasurable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUMeasurableSetTriPos

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRB

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWR

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Set Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

open ChartWRAux in
theorem chartWR_vol (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (UCo N)) (E : Set (TriCo N)), MeasurableSet B → MeasurableSet E →
      (∀ x ∈ B, ‖x‖ < δ) → (∀ t ∈ E, ‖t‖ < δ) →
      volume (chartWR '' (B ×ˢ E)) ≤ ENNReal.ofReal (1 + η) * (volume B * volume E) ∧
        ENNReal.ofReal (1 - η) * (volume B * volume E) ≤ volume (chartWR '' (B ×ˢ E)) := by
  have : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let L : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ) := (lamE : (UCo N × TriCo N) ≃L[ℝ] _)
  let g : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ) := fun z => chartWR (lamE.symm z)
  have hg : HasStrictFDerivAt g (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) 0 := by
    have hc : HasStrictFDerivAt (chartWR (N := N)) L (lamE.symm 0) := by
      rw [map_zero]; exact chartWR_strict
    have h := hc.comp (0 : Fin N → Fin N → ℂ)
      ((lamE.symm : (Fin N → Fin N → ℂ) ≃L[ℝ] (UCo N × TriCo N)) :
        (Fin N → Fin N → ℂ) →L[ℝ] (UCo N × TriCo N)).hasStrictFDerivAt
    rwa [ContinuousLinearEquiv.coe_comp_coe_symm] at h
  have hdet : ENNReal.ofReal |(ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)).det| = 1 := by
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
  have ev1 := addHaar_image_le_mul_of_det_lt (μ := (volume : Measure (Fin N → Fin N → ℂ)))
    (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 + η).toNNReal) (by
      rw [hdet]; exact_mod_cast (show (1 : ℝ) < (1 + η).toNNReal by
        rw [Real.coe_toNNReal _ (by linarith)]; linarith))
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : NNReal), ∀ (s : Set (Fin N → Fin N → ℂ)) (f : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)),
      ApproximatesLinearOn f (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) s δ →
        ENNReal.ofReal (1 - η) * volume s ≤ volume (f '' s) := by
    rcases lt_or_ge η 1 with h1 | h1
    · have := mul_le_addHaar_image_of_lt_det (μ := (volume : Measure (Fin N → Fin N → ℂ)))
        (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 - η).toNNReal) (by
          rw [hdet]; exact_mod_cast (show ((1 - η).toNNReal : ℝ) < 1 by
            rw [Real.coe_toNNReal _ (by linarith)]; linarith))
      exact this
    · refine Filter.Eventually.of_forall fun δ s f _ => ?_
      rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]; exact bot_le
  obtain ⟨c, ⟨hc1, hc2⟩, hcpos⟩ := ((ev1.and ev2).and self_mem_nhdsWithin).exists
  obtain ⟨s, hs, hap⟩ := hg.approximates_deriv_on_nhds (Or.inr hcpos)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  refine ⟨r / (‖L‖ + 1), by positivity, fun B E hB hE hBδ hEδ => ?_⟩
  have hLr : ‖L‖ * (r / (‖L‖ + 1)) < r := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hball : (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) '' (B ×ˢ E) ⊆ s := by
    rintro _ ⟨p, hp, rfl⟩
    apply hrs
    rw [Metric.mem_ball, dist_zero_right]
    have hp' : ‖p‖ < r / (‖L‖ + 1) := by
      rw [Prod.norm_def]; exact max_lt (hBδ _ hp.1) (hEδ _ hp.2)
    calc ‖lamE p‖ = ‖L p‖ := rfl
      _ ≤ ‖L‖ * ‖p‖ := L.le_opNorm p
      _ ≤ ‖L‖ * (r / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hp'.le hL0
      _ < r := hLr
  have hap' := hap.mono_set hball
  have himg : chartWR '' (B ×ˢ E) = g '' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
    rw [Set.image_image]
    refine Set.image_congr fun p _ => ?_
    simp [g]
  have hmp : MeasurePreserving (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) volume volume := by
    have e : (⇑(lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ))) = lam := funext lamE_apply
    rw [e]; exact mp_lam
  have hme : MeasurableEmbedding (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) :=
    lamE.toHomeomorph.measurableEmbedding
  have hvol : volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) = volume B * volume E := by
    calc volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))
        = (Measure.map lamE volume) ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
          rw [hmp.map_eq]
      _ = volume (lamE ⁻¹' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))) := hme.map_apply _ _
      _ = volume (B ×ˢ E) := by rw [Set.preimage_image_eq _ lamE.injective]
      _ = volume B * volume E := Measure.prod_prod _ _
  rw [himg]
  refine ⟨?_, ?_⟩
  · have := hc1 _ g hap'
    rw [hvol] at this
    exact this
  · have := hc2 _ g hap'
    rw [hvol] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_density (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (UCo N), MeasurableSet B → (∀ x ∈ B, ‖x‖ < δ) →
      μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} ≤ ENNReal.ofReal ((1 + η) / volU N) * volume B ∧
        ENNReal.ofReal ((1 - η) / volU N) * volume B ≤ μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} := by
  obtain ⟨C, -, hC⟩ := qr_lintegral μ
  have hCV : C = volU N := qr_const μ C hC
  subst hCV
  have hV := volU_pos' N
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 - ε) * (1 + η) = 1 + ε :=
    ⟨η / (2 + η), by positivity, by rw [div_lt_one (by linarith)]; linarith,
      by field_simp; ring⟩
  obtain ⟨δ1, hδ1, hchart⟩ := chartWR_vol (N := N) ε hε0
  obtain ⟨δ2, hδ2, hinj⟩ := volU_exp_injOn (N := N)
  obtain ⟨ρw, hρw, hw⟩ := Metric.continuousAt_iff.1
    (volU_continuous_qrWt (N := N)).continuousAt ε hε0
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ1 ∧ ρ ≤ ρw ∧ ρ ≤ 1 :=
    ⟨min δ1 (min ρw 1), lt_min hδ1 (lt_min hρw one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun B hB hBs => ?_⟩
  show μ (volUSet B) ≤ _ ∧ _ ≤ μ (volUSet B)
  have hBsub : B ⊆ Metric.ball 0 δ2 := fun x hx =>
    mem_ball_zero_iff.2 ((hBs x hx).trans_le (min_le_right _ _))
  have hA : MeasurableSet (volUSet B) := volUSet_measurable hinj hB hBsub
  have hE'pos : Metric.ball (volUOne N) ρ ⊆ triPos N := volU_ball_sub_triPos hρ3
  set S := qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) with hSdef
  have hS : MeasurableSet S := qrMap_measurableSet_image _ (hA.prod Metric.isOpen_ball.measurableSet)
    (fun p hp => ⟨Set.mem_univ _, hE'pos hp.2⟩)
  set I := ∫⁻ t in Metric.ball (volUOne N) ρ, ENNReal.ofReal (qrWt t) with hIdef
  have hmem : ∀ k (t : TriCo N), t ∈ triPos N →
      (qrMap (k, t) ∈ S ↔ k ∈ volUSet B ∧ t ∈ Metric.ball (volUOne N) ρ) := by
    intro k t ht
    constructor
    · rintro ⟨⟨k', t'⟩, ⟨hk', ht'⟩, heq⟩
      have := qrMap_injOn ⟨Set.mem_univ _, hE'pos ht'⟩ ⟨Set.mem_univ _, ht⟩ heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      exact ⟨hk', ht'⟩
    · rintro ⟨hk, ht'⟩
      exact ⟨(k, t), ⟨hk, ht'⟩, rfl⟩
  have hin : ∀ k, (∫⁻ t in triPos N, S.indicator 1 (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) =
      (volUSet B).indicator (fun _ => I) k := by
    intro k
    by_cases hk : k ∈ volUSet B
    · rw [Set.indicator_of_mem hk, hIdef,
        ← Set.inter_eq_left.2 hE'pos, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
      refine setLIntegral_congr_fun volU_measurableSet_triPos (fun t ht => ?_)
      by_cases ht' : t ∈ Metric.ball (volUOne N) ρ
      · rw [Set.indicator_of_mem ((hmem k t ht).2 ⟨hk, ht'⟩), Set.indicator_of_mem ht', Pi.one_apply,
          one_mul]
      · rw [Set.indicator_of_notMem (fun h => ht' ((hmem k t ht).1 h).2), Set.indicator_of_notMem ht',
          zero_mul]
    · rw [Set.indicator_of_notMem hk]
      rw [setLIntegral_congr_fun volU_measurableSet_triPos (g := fun _ => 0) (fun t ht => by
        simp only
        rw [Set.indicator_of_notMem (fun h => hk ((hmem k t ht).1 h).1), zero_mul])]
      simp
  have hSeq : volume S = ENNReal.ofReal (volU N) * (I * μ (volUSet B)) := by
    have h := hC (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS] at h
    rw [h, lintegral_congr hin, lintegral_indicator_const hA]
  have : Measure.IsAddHaarMeasure (volume : Measure (TriCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have : Measure.IsAddHaarMeasure (volume : Measure (UCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.2 < ab.1} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hE : volume (Metric.ball (volUOne N) ρ) = volume (Metric.ball (0 : TriCo N) ρ) :=
    Measure.addHaar_ball_center _ _ _
  have hIlo : ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : TriCo N) ρ) ≤ I := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [neg_abs_le (qrWt t - 1)]
  have hIhi : I ≤ ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : TriCo N) ρ) := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [le_abs_self (qrWt t - 1)]
  obtain ⟨hup, hlo⟩ := hchart B (Metric.ball 0 ρ) hB Metric.isOpen_ball.measurableSet
    (fun x hx => (hBs x hx).trans_le (min_le_left _ _))
    (fun t ht => (mem_ball_zero_iff.1 ht).trans_le hρ1)
  rw [volU_image_eq, ← hSdef, hSeq] at hup hlo

  have hEpos : 0 < volume (Metric.ball (0 : TriCo N) ρ) := Metric.measure_ball_pos _ _ hρ0
  have hEfin : volume (Metric.ball (0 : TriCo N) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ((measure_mono hBsub).trans_lt measure_ball_lt_top).ne
  have hAfin : μ (volUSet B) ≠ ⊤ := measure_ne_top μ _
  have hIfin : I ≠ ⊤ := (hIhi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin.lt_top)).ne
  set a := (μ (volUSet B)).toReal
  set b := (volume B).toReal
  set e := (volume (Metric.ball (0 : TriCo N) ρ)).toReal
  set i := I.toReal
  have ha' : μ (volUSet B) = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAfin).symm
  have hb' : volume B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBfin).symm
  have he' : volume (Metric.ball (0 : TriCo N) ρ) = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEfin).symm
  have hi' : I = ENNReal.ofReal i := (ENNReal.ofReal_toReal hIfin).symm
  have he0 : 0 < e := ENNReal.toReal_pos hEpos.ne' hEfin
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hi0 : 0 ≤ i := ENNReal.toReal_nonneg
  rw [ha', hb', he', hi'] at hup hlo
  rw [he', hi'] at hIlo hIhi
  rw [← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul hV.le] at hup hlo
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul (by linarith)] at hup
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul' (by positivity)] at hlo
  rw [← ENNReal.ofReal_mul (by linarith)] at hIhi
  rw [← ENNReal.ofReal_mul' he0.le] at hIlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have h3 := (ENNReal.ofReal_le_ofReal_iff hi0).1 hIlo
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hIhi
  obtain ⟨r1, r2⟩ := volU_real hV he0 ha0 hb0 hε0 hε1 hη hkey h1 h2 h3 h4
  rw [ha', hb']
  constructor
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal r1
  · rw [← ENNReal.ofReal_mul' hb0]
    exact ENNReal.ofReal_le_ofReal r2

end ReciprocityTheory.ChartRestriction.DS
end
end
end
