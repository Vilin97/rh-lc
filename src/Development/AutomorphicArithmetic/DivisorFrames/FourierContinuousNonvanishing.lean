module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs

@[expose] public section

open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem iter_ne_zero : ∀ {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb]
    [μa.IsOpenPosMeasure] [μb.IsOpenPosMeasure] [SFinite μa] [SFinite μb]
    (F : α → β → ℂ) (hF : Continuous (Function.uncurry F)) (C : Set (α × β)) (hC : IsCompact C)
    (h0 : ∀ p ∉ C, F p.1 p.2 = 0) (c : ℂ) (hpos : ∀ a b, 0 ≤ (starRingEnd ℂ c * F a b).re) (a₀ : α) (b₀ : β)
    (h₀ : 0 < (starRingEnd ℂ c * F a₀ b₀).re),
    ∫ a, ∫ b, F a b ∂μb ∂μa ≠ 0 := by
  intro α β _ _ _ _ _ _ _ _ μa μb _ _ _ _ _ _ F hF C hC h0 c hpos a₀ b₀ h₀
  set G : α × β → ℂ := Function.uncurry F with hG
  have hsub : Function.support G ⊆ C := by
    intro p hp
    by_contra hpC
    exact hp (h0 p hpC)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have hbound : ∀ p, ‖G p‖ ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ C
    · exact (hM p hp).trans (le_max_left _ _)
    · have : G p = 0 := h0 p hp
      rw [this, norm_zero]; exact le_max_right _ _
  have hintC : IntegrableOn G C (μa.prod μb) :=
    Measure.integrableOn_of_bounded (M := max M 0) hC.measure_lt_top.ne
      hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hint : Integrable G (μa.prod μb) := (integrableOn_iff_integrable_of_support_subset hsub).1 hintC
  have hprod : ∫ p, G p ∂(μa.prod μb) = ∫ a, ∫ b, F a b ∂μb ∂μa := integral_prod G hint
  intro hzero
  have hint2 : Integrable (fun p => starRingEnd ℂ c * G p) (μa.prod μb) := hint.const_mul _
  have hre : ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) = 0 := by
    have := integral_re hint2
    rw [integral_const_mul, hprod, hzero, mul_zero] at this
    simpa using this
  have hcont : Continuous (fun p : α × β => (starRingEnd ℂ c * G p).re) :=
    Complex.continuous_re.comp (continuous_const.mul hF)
  have hnn : 0 ≤ fun p : α × β => (starRingEnd ℂ c * G p).re := fun p => hpos p.1 p.2
  have hpos2 : 0 < ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) := by
    rw [integral_pos_iff_support_of_nonneg hnn (Complex.reCLM.integrable_comp hint2)]
    have hopen : IsOpen (Function.support fun p : α × β => (starRingEnd ℂ c * G p).re) :=
      hcont.isOpen_support
    refine hopen.measure_pos _ ⟨(a₀, b₀), ?_⟩
    exact ne_of_gt h₀
  linarith

private theorem compact_pre {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [TopologicalSpace K] [CompactSpace K]
    (η : K → Fin n × ι → ℂ) (hη : Continuous η) (h0 : ∀ k w, ∃ i, η k (i, w) ≠ 0)
    (hπ : Continuous fun p : K × (ι → ℂ) => sc p.2 (η p.1)) (x : Fin n × ι → ℂ) (r : ℝ) :
    IsCompact ((fun p : K × (ι → ℂ) => sc p.2 (η p.1)) ⁻¹' Metric.closedBall x r) := by
  have hm : ∀ w : ι, ∃ m : ℝ, 0 < m ∧ ∀ k ∈ (Set.univ : Set K), m ≤ ‖fun i : Fin n => η k (i, w)‖ := by
    intro w
    refine isCompact_univ.exists_forall_le' (Continuous.continuousOn (by fun_prop)) fun k _ => ?_
    obtain ⟨i, hi⟩ := h0 k w
    exact norm_pos_iff.2 fun h => hi (congrFun h i)
  choose m hm0 hm using hm
  have hc : IsCompact ((Set.univ : Set K) ×ˢ (Set.pi Set.univ fun w : ι => Metric.closedBall (0 : ℂ) ((‖x‖ + r) / m w))) :=
    isCompact_univ.prod (isCompact_univ_pi fun w => isCompact_closedBall _ _)
  refine hc.of_isClosed_subset (Metric.isClosed_closedBall.preimage hπ) ?_
  rintro ⟨k, y⟩ hp
  refine ⟨trivial, fun w _ => ?_⟩
  have h1 : ‖sc y (η k)‖ ≤ ‖x‖ + r := norm_le_of_mem_closedBall hp
  have h2 : ‖y w • fun i : Fin n => η k (i, w)‖ ≤ ‖sc y (η k)‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (sc y (η k)) (i, w)
  rw [norm_smul] at h2
  rw [mem_closedBall_zero_iff, le_div_iff₀ (hm0 w)]
  have h3 := mul_le_mul_of_nonneg_left (hm w k trivial) (norm_nonneg (y w))
  exact h3.trans (h2.trans h1)
