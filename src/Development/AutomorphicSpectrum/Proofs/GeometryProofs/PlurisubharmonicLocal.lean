module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
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
import Mathlib.Order.CompletePartialOrder
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExtB
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPshLocal

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real

noncomputable section

variable {D : ℕ} {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

theorem PshLocal.usc
    (hloc : ∀ p ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ) :
    UpperSemicontinuousOn φ U := by
  intro x hx y hy
  obtain ⟨W, hWo, hxW, -, hW⟩ := hloc x hx
  have h := hW.1 x hxW y hy
  rw [hWo.nhdsWithin_eq hxW] at h
  exact nhdsWithin_le_nhds h

theorem PshLocal.isPsh_max {W : Set (Fin D → ℂ)} (h : IsPsh W φ) (a : ℝ) :
    IsPsh W (fun x => max (φ x) a) := by
  refine ⟨h.1.sup upperSemicontinuousOn_const, fun z w hd => ?_⟩
  obtain ⟨hi, hm⟩ := h.2 z w hd
  have hca : CircleIntegrable (fun _ : ℂ => a) 0 1 := intervalIntegrable_const
  have hi' : CircleIntegrable (fun ζ : ℂ => max (φ (z + ζ • w)) a) 0 1 :=
    ⟨hi.1.sup hca.1, hi.2.sup hca.2⟩
  refine ⟨hi', max_le ?_ ?_⟩
  · exact hm.trans (circleAverage_mono hi hi' fun x _ => le_max_left _ _)
  · calc a = circleAverage (fun _ : ℂ => a) 0 1 := (circleAverage_const a 0 1).symm
      _ ≤ _ := circleAverage_mono hca hi' fun x _ => le_max_right _ _

theorem PshLocal.core (hU : IsOpen U)
    (hloc : ∀ p ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ)
    (z w : Fin D → ℂ) (hD : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) {c : ℝ}
    (hc : ∀ θ : ℝ, c ≤ φ (z + circleMap 0 1 θ • w)) :
    IntervalIntegrable (fun θ => φ (z + circleMap 0 1 θ • w)) volume 0 (2 * π) ∧
      φ z ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, φ (z + circleMap 0 1 θ • w) := by
  have husc := PshLocal.usc hloc
  set K := (fun ζ : ℂ => z + ζ • w) '' closedBall (0 : ℂ) 1 with hKdef
  have hKc : IsCompact K := (isCompact_closedBall _ _).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hD ζ (mem_closedBall_zero_iff.1 hζ)
  have hγ : Continuous (fun θ : ℝ => z + circleMap 0 1 θ • w) :=
    continuous_const.add ((continuous_circleMap 0 1).smul continuous_const)
  have hcirc : ∀ θ : ℝ, z + circleMap 0 1 θ • w ∈ K := fun θ =>
    ⟨circleMap 0 1 θ, mem_closedBall_zero_iff.2 (by simp), rfl⟩
  have hzK : z ∈ K := ⟨0, mem_closedBall_self zero_le_one, by simp⟩
  choose W hWo hpW hWU hWpsh using hloc
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hKc (c := fun p : U => W p.1 p.2)
    (fun p => hWo _ _) (fun x hx => mem_iUnion.2 ⟨⟨x, hKU hx⟩, hpW _ _⟩)
  obtain ⟨δ', hδ', hδ'U⟩ := hKc.exists_cthickening_subset_open hU hKU
  obtain ⟨M, hM⟩ := (husc.mono hδ'U).bddAbove_of_isCompact hKc.cthickening
  have hMK : ∀ y ∈ cthickening δ' K, φ y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  obtain ⟨ρ⟩ := mollifierInhabit_thm D
  have hε0 : 0 < min (δ / 2) δ' := lt_min (by linarith) hδ'
  have step : ∀ ε, 0 < ε → ε < min (δ / 2) δ' →
      (∀ x ∈ K, φ x ≤ molli ρ ε φ x ∧ molli ρ ε φ x ≤ M) ∧
      Continuous (fun θ : ℝ => molli ρ ε φ (z + circleMap 0 1 θ • w)) ∧
      molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by
    intro ε hε hεlt
    have hεδ : ε < δ := by have := min_le_left (δ / 2) δ'; linarith
    have hεδ' : ε ≤ δ' := by have := min_le_right (δ / 2) δ'; linarith
    have hm := fun p : U => (mollify_thm D ρ (W p.1 p.2) φ (hWo _ _) (hWpsh _ _)).1 ε hε
    have hm2 : ∀ p : U, ContDiffOn ℝ 2 (molli ρ ε φ) (shrink (W p.1 p.2) ε) := fun p =>
      (hm p).2.1.of_le (WithTop.coe_le_coe.2 le_top)
    set V := ⋃ p : U, shrink (W p.1 p.2) ε with hV
    have hVo : IsOpen V := isOpen_iUnion fun p => (hm p).1
    have hKV : ∀ x ∈ K, ∃ p : U, x ∈ shrink (W p.1 p.2) ε := by
      intro x hx
      obtain ⟨p, hp⟩ := hδK x hx
      exact ⟨p, (closedBall_subset_ball hεδ).trans hp⟩
    have hcd : ContDiffOn ℝ 2 (molli ρ ε φ) V := by
      refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
      obtain ⟨p, hp⟩ := mem_iUnion.1 hy
      exact ⟨_, (hm p).1, hp, (hm2 p).mono inter_subset_right⟩
    have hpsh : IsPsh V (molli ρ ε φ) := by
      refine (isPsh_iff_isLeviPsh_thm D V _ hVo hcd).2 ⟨hcd, fun y hy v => ?_⟩
      obtain ⟨p, hp⟩ := mem_iUnion.1 hy
      exact ((isPsh_iff_isLeviPsh_thm D _ _ (hm p).1 (hm2 p)).1 (hm p).2.2.1).2 y hp v
    have hmemV : ∀ x ∈ K, x ∈ V := fun x hx =>
      let ⟨p, hp⟩ := hKV x hx
      mem_iUnion.2 ⟨p, hp⟩
    refine ⟨fun x hx => ?_, hcd.continuousOn.comp_continuous hγ fun θ => hmemV _ (hcirc θ),
      (hpsh.2 z w fun ζ hζ => hmemV _ ⟨ζ, mem_closedBall_zero_iff.2 hζ, rfl⟩).2⟩
    obtain ⟨p, hp⟩ := hKV x hx
    obtain ⟨h1, h2⟩ := (hm p).2.2.2 x hp
    refine ⟨h1, h2.trans (polyMax_le' hε.le fun y hy => hMK y ?_)⟩
    exact cthickening_mono hεδ' K (closedBall_subset_cthickening hx ε hy)
  set f : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w) with hf
  set B := max |c| |M|
  have hbd : ∀ t : ℝ, c ≤ t → t ≤ M → |t| ≤ B := fun t h1 h2 => by
    rw [abs_le]
    constructor
    · have := neg_abs_le c
      have := le_max_left |c| |M|
      linarith
    · have := le_abs_self M
      have := le_max_right |c| |M|
      linarith
  have hfM : ∀ θ, f θ ≤ M := fun θ => hMK _ (self_subset_cthickening K (hcirc θ))
  have hfm : Measurable f :=
    (upperSemicontinuousOn_univ_iff.1
      (husc.comp hγ.continuousOn fun θ _ => hKU (hcirc θ))).measurable
  refine ⟨PlurisubharmonicExtension.ii_of_bdd hfm B (fun θ => hbd _ (hc θ) (hfM θ)) _ _, ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < min (δ / 2) δ' := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε0)] with ε h1 h2
    exact ⟨h1, h2⟩
  have hT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * π) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε θ => molli ρ ε φ (z + circleMap 0 1 θ • w)) (f := f) (fun _ => B)
    (hev.mono fun ε h => (step ε h.1 h.2).2.1.aestronglyMeasurable)
    (hev.mono fun ε h => ae_of_all _ fun θ _ => by
      obtain ⟨h1, h2⟩ := (step ε h.1 h.2).1 _ (hcirc θ)
      rw [Real.norm_eq_abs]
      exact hbd _ ((hc θ).trans h1) h2)
    intervalIntegrable_const
    (ae_of_all _ fun θ _ =>
      (mollify_thm D ρ _ φ (hWo _ (hKU (hcirc θ))) (hWpsh _ _)).2 _ (hpW _ _))
  refine ge_of_tendsto (hT.const_mul (2 * π)⁻¹) (hev.mono fun ε h => ?_)
  obtain ⟨h1, -, h3⟩ := step ε h.1 h.2
  rw [circleAverage_def, smul_eq_mul] at h3
  exact (h1 z hzK).1.trans h3

end

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.AnForm.PshLocal

open Filter Topology ReciprocityTheory.AnForm.A

theorem isPsh_mono {n : ℕ} {V W : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (hWV : W ⊆ V)
    (h : IsPsh V φ) : IsPsh W φ := by
  unfold ReciprocityTheory.AnForm.A.IsPsh at h ⊢
  obtain ⟨hu, hm⟩ := h
  exact ⟨hu.mono hWV, fun z w hzw => hm z w fun ζ hζ => hWV (hzw ζ hζ)⟩

theorem isPsh_of_locally :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U →
      (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro n U φ hU hloc
  have hloc' : ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ := by
    intro p hp
    obtain ⟨V, hV, hpV, hψ⟩ := hloc p hp
    exact ⟨V ∩ U, hV.inter hU, ⟨hpV, hp⟩, Set.inter_subset_right, isPsh_mono Set.inter_subset_left hψ⟩
  have hlocg : ∀ k : ℕ, ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      IsPsh W (fun x => max (φ x) (-(k : ℝ))) := by
    intro k p hp
    obtain ⟨W, hW, hpW, hWU, hψ⟩ := hloc' p hp
    exact ⟨W, hW, hpW, hWU, GroundTheory.Heights₂.Heights.NineStatements.PshLocal.isPsh_max hψ _⟩
  have husc := GroundTheory.Heights₂.Heights.NineStatements.PshLocal.usc hloc'
  unfold ReciprocityTheory.AnForm.A.IsPsh
  refine ⟨husc, ?_⟩
  intro z w hzw
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let F : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w)
  let f : ℕ → ℝ → ℝ := fun k θ => max (F θ) (-(k : ℝ))
  have hcore : ∀ k : ℕ, IntervalIntegrable (f k) MeasureTheory.volume 0 (2 * Real.pi) ∧
      max (φ z) (-(k : ℝ)) ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ := fun k =>
    GroundTheory.Heights₂.Heights.NineStatements.PshLocal.core hU (hlocg k) z w hzw (c := -(k : ℝ))
      (fun θ => le_max_right _ _)
  have hint : ∀ k, MeasureTheory.Integrable (f k) μ := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp (hcore k).1
  have hanti : ∀ θ, Antitone fun k : ℕ => f k θ := by
    intro θ
    refine antitone_nat_of_succ_le fun k => ?_
    show max (F θ) (-(((k + 1 : ℕ)) : ℝ)) ≤ max (F θ) (-(k : ℝ))
    push_cast
    exact max_le_max le_rfl (by linarith)
  have htend : ∀ θ, Tendsto (fun k : ℕ => f k θ) atTop (𝓝 (F θ)) := by
    intro θ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈-F θ⌉₊) fun k hk => ?_
    have hc := Nat.le_ceil (-F θ)
    have hk' : ((⌈-F θ⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    exact max_eq_left (by linarith)
  have hlow : ∀ k : ℕ, 2 * Real.pi * φ z ≤ ∫ θ, f k θ ∂μ := by
    intro k
    have h1 := le_trans (le_max_left (φ z) (-(k : ℝ))) (hcore k).2
    rw [intervalIntegral.integral_of_le h2π] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 h2π
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h3
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).aestronglyMeasurable)
      (Filter.Eventually.of_forall htend)
  have hGnn : ∀ (k : ℕ) θ, 0 ≤ f 0 θ - f k θ := fun k θ => sub_nonneg.mpr (hanti θ (Nat.zero_le k))
  have hFle : ∀ θ, F θ ≤ f 0 θ := fun θ => le_max_left _ _
  have hGint : MeasureTheory.Integrable (fun θ => f 0 θ - F θ) μ := by
    refine ⟨(hint 0).aestronglyMeasurable.sub hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => sub_nonneg.mpr (hFle θ))]
    have hlim : ∀ θ, Tendsto (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop
        (𝓝 (ENNReal.ofReal (f 0 θ - F θ))) :=
      fun θ => (ENNReal.continuous_ofReal.tendsto _).comp ((htend θ).const_sub _)
    have hterm : ∀ k : ℕ, ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ ≤
        ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) := by
      intro k
      have e := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun θ => f 0 θ - f k θ)
        ((hint 0).sub (hint k)) (Filter.Eventually.of_forall (hGnn k))
      rw [← e, MeasureTheory.integral_sub (hint 0) (hint k)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hlow k])
    calc ∫⁻ θ, ENNReal.ofReal (f 0 θ - F θ) ∂μ
        = ∫⁻ θ, liminf (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop ∂μ := by
          congr 1
          funext θ
          exact ((hlim θ).liminf_eq).symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' fun k => ((hint 0).sub (hint k)).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hterm)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFint : MeasureTheory.Integrable F μ :=
    ((hint 0).sub hGint).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hlimI := MeasureTheory.integral_tendsto_of_tendsto_of_antitone hint hFint
    (Filter.Eventually.of_forall hanti) (Filter.Eventually.of_forall htend)
  have hge : 2 * Real.pi * φ z ≤ ∫ θ, F θ ∂μ := ge_of_tendsto' hlimI hlow
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mpr hFint, ?_⟩
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π]
  have h4 := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr h2π)
  rwa [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h4

end GlobalTheory.CompanionTheory.AnForm.PshLocal
end
end
