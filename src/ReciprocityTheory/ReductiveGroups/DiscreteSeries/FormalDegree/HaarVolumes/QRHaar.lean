module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaarA

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DetNull

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem measurableSet_mem_span_range (n m : ℕ) :
    MeasurableSet {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) |
      p.1 ∈ Submodule.span ℂ (Set.range p.2)} := by
  have h : {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) | p.1 ∈ Submodule.span ℂ (Set.range p.2)} =
      Set.range (fun q : (Fin n → ℂ) × (Fin n → Fin m → ℂ) => (∑ j, q.1 j • q.2 j, q.2)) := by
    ext ⟨x, W⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq, Prod.exists]
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, W, hc, rfl⟩
    · rintro ⟨c, W', hc, rfl⟩
      exact ⟨c, hc⟩
  rw [h]
  obtain ⟨K, hK, hKe⟩ := isSigmaCompact_range (X := (Fin n → ℂ) × (Fin n → Fin m → ℂ))
    (f := fun q => (∑ j, q.1 j • q.2 j, q.2)) (by fun_prop)
  rw [← hKe]
  exact MeasurableSet.iUnion fun k => (hK k).measurableSet

theorem volume_span_range_eq_zero (n : ℕ) (W : Fin n → Fin (n + 1) → ℂ) :
    volume ((Submodule.span ℂ (Set.range W) : Submodule ℂ (Fin (n + 1) → ℂ)) :
      Set (Fin (n + 1) → ℂ)) = 0 := by
  have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range W)) ≤ n := by
    first
    | simpa using finrank_span_range_le_card (R := ℂ) W
    | simpa using Submodule.finrank_span_range_le_card (R := ℂ) W
    | simpa using finrank_range_le_card (R := ℂ) W
    | (have h2 := finrank_range_le_card (R := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := finrank_range_le_card (K := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := rank_span_le_of_finite (R := ℂ) (Set.finite_range W)
       exact absurd h2 (by simp))
  have hne : (Submodule.span ℂ (Set.range W)) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hne' : (Submodule.span ℂ (Set.range W)).restrictScalars ℝ ≠ ⊤ := by
    intro h
    apply hne
    first
    | exact (Submodule.restrictScalars_eq_top_iff ℝ ℂ _).mp h
    | exact Submodule.restrictScalars_injective ℝ ℂ (Fin (n + 1) → ℂ) (by rw [h]; rfl)
  exact MeasureTheory.Measure.addHaar_submodule volume _ hne'

theorem exists_row_mem_span_of_det_eq_zero {n : ℕ} (Z : Fin (n + 1) → Fin (n + 1) → ℂ)
    (hZ : (Matrix.of Z).det = 0) :
    ∃ i : Fin (n + 1), Z i ∈ Submodule.span ℂ (Set.range fun j : Fin n => Z (i.succAbove j)) := by
  have hli : ¬ LinearIndependent ℂ Z := by
    intro h
    have hu : IsUnit (Matrix.of Z) := Matrix.linearIndependent_rows_iff_isUnit.mp h
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hZ
  have hex : ∃ i, Z i ∈ Submodule.span ℂ (Z '' (Set.univ \ {i})) := by
    by_contra hno
    push_neg at hno
    apply hli
    first
    | exact linearIndependent_iff_not_mem_span.mpr hno
    | exact linearIndependent_iff_notMem_span.mpr hno
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have himg : Z '' (Set.univ \ {i}) = Set.range fun j : Fin n => Z (i.succAbove j) := by
    rw [show (fun j : Fin n => Z (i.succAbove j)) = Z ∘ i.succAbove from rfl, Set.range_comp,
      Fin.range_succAbove, Set.compl_eq_univ_diff]
  rw [himg] at hi
  exact hi

theorem volume_det_eq_zero :
    volume {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} = 0 := by
  cases N with
  | zero =>
    have h : {Z : Fin 0 → Fin 0 → ℂ | (Matrix.of Z).det = 0} = ∅ := by
      ext Z
      simp [Matrix.det_isEmpty]
    rw [h, measure_empty]
  | succ n =>
    let T : Set ((Fin (n + 1) → ℂ) × (Fin n → Fin (n + 1) → ℂ)) :=
      {p | p.1 ∈ Submodule.span ℂ (Set.range p.2)}
    have hT : MeasurableSet T := measurableSet_mem_span_range n (n + 1)
    have hsub : {Z : Fin (n + 1) → Fin (n + 1) → ℂ | (Matrix.of Z).det = 0} ⊆
        ⋃ i : Fin (n + 1),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℂ) i) ⁻¹' T := by
      intro Z hZ
      obtain ⟨i, hi⟩ := exists_row_mem_span_of_det_eq_zero Z hZ
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have mp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) i
    have h1 := mp.measure_preimage hT.nullMeasurableSet
    change (Measure.pi fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) _ = 0
    rw [h1, Measure.prod_apply_symm hT]
    exact (lintegral_congr fun W => volume_span_range_eq_zero n W).trans lintegral_zero

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaar

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.QRH

variable {N : ℕ}

theorem qr_lintegral (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
  haveI hcpt : CompactSpace (UNgrp N) := by
    by_contra hnc
    rw [not_compactSpace_iff] at hnc
    have h1 := MeasureTheory.measure_univ_of_isMulLeftInvariant μ
    rw [measure_univ] at h1
    exact ENNReal.one_ne_top h1
  obtain ⟨c, hct, hkap⟩ := kap_eq (N := N)
  haveI : SigmaFinite (triMeas N) := by
    unfold triMeas triDens
    infer_instance
  haveI : SigmaFinite (kap N) := by
    rw [hkap]
    lift c to NNReal using hct
    show SigmaFinite (c • triMeas N)
    infer_instance
  have hprod := nuQR_eq_prod (N := N) μ
  have hcd : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
    Continuous.matrix_det (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)
  have hdet : Measurable fun Z : Fin N → Fin N → ℂ => ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) :=
    ((hcd.norm.pow _).measurable).ennreal_ofReal
  have hgm : Measurable (gmDens N) := by
    have he : gmDens N = fun Z => ENNReal.ofReal ((‖(Matrix.of Z).det‖ ^ (2 * N))⁻¹) := by
      funext Z
      unfold gmDens
      rw [_root_.zpow_neg, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [he]
    exact ((hcd.norm.pow _).measurable.inv).ennreal_ofReal
  have htd : Measurable (triDens (N := N)) := by
    unfold triDens
    first
    | fun_prop
    | measurability
  have key : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = c * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
    intro f hf
    have hg : Measurable fun Z => f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) := hf.mul hdet
    have hgq : Measurable fun p : UNgrp N × TriCo N =>
        f (qrMap p) * ENNReal.ofReal (‖(Matrix.of (qrMap p)).det‖ ^ (2 * N)) := hg.comp measurable_qrMap
    have s1 : ∫⁻ Z, f Z = ∫⁻ Z in glSet N, f Z := by
      rw [← lintegral_add_compl f (measurableSet_glSet (N := N))]
      have hc : (glSet N)ᶜ = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} := by
        ext Z
        simp [glSet]
      rw [hc, setLIntegral_measure_zero _ _ volume_det_eq_zero, add_zero]
    have s2 : ∫⁻ Z in glSet N, f Z =
        ∫⁻ Z, f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) ∂((gmMeas N).restrict (glSet N)) := by
      unfold gmMeas
      rw [restrict_withDensity measurableSet_glSet, lintegral_withDensity_eq_lintegral_mul _ hgm hg]
      apply setLIntegral_congr_fun measurableSet_glSet
      intro Z hZ
      simp only [Pi.mul_apply]
      rw [mul_comm (f Z), ← mul_assoc, gmDens_mul Z hZ, one_mul]
    rw [s1, s2, ← map_qrMap_nuQR, lintegral_map hg measurable_qrMap, ← hprod,
      lintegral_prod _ hgq.aemeasurable, ← lintegral_const_mul' _ _ hct]
    apply lintegral_congr
    intro k
    rw [hkap, lintegral_smul_measure]
    congr 1
    unfold triMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ htd (by
      first
      | exact hgq.comp measurable_prodMk_left
      | exact hgq.comp measurable_prod_mk_left)]
    apply setLIntegral_congr_fun measurableSet_triPos
    intro t ht
    simp only [Pi.mul_apply]
    rw [d_qrMap k t ht, mul_comm, mul_assoc, mul_comm _ (triDens t), triDens_mul t ht]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := key (fun _ => 1) measurable_const
    rw [h0, zero_mul, lintegral_const, one_mul] at h1
    have hv : (volume : Measure (Fin N → Fin N → ℂ)) Set.univ ≠ 0 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro i _
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro j _
      exact isOpen_univ.measure_ne_zero volume Set.univ_nonempty
    exact hv h1
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  intro f hf
  rw [ENNReal.ofReal_toReal hct]
  exact key f hf

end ReciprocityTheory.ChartRestriction.DS
end
end
end
