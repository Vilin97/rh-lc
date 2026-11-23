module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MapRestrictSubgroupEqCommonSmulHaar

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory

theorem map_restrict_subgroup_eq_smul_haar (G : Type) [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (hμ : μ H ≠ 0)
    (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Measurable ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t) (hf : ∀ t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ ⁻¹' W) ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ (μ.restrict H).map ψ = κ • ν ∧ ν.IsMulRightInvariant := by
  set m : Measure R := (μ.restrict H).map ψ with hm
  have happ : ∀ s, MeasurableSet s → m s = μ (ψ ⁻¹' s ∩ H) := by
    intro s hs'
    rw [hm, Measure.map_apply hψ hs', Measure.restrict_apply (hψ hs')]
  have hL : m.IsMulLeftInvariant := by
    rw [← forall_measure_preimage_mul_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_const_mul _ hs'), ← measure_preimage_mul μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_left hh]
  have hR : m.IsMulRightInvariant := by
    rw [← forall_measure_preimage_mul_right_iff]
    intro t s hs'
    obtain ⟨h, hh, rfl⟩ := hs t
    rw [happ _ hs', happ _ (measurable_mul_const _ hs'),
      ← measure_preimage_mul_right μ h (ψ ⁻¹' s ∩ H)]
    congr 1
    ext g
    simp [H.mul_mem_cancel_right hh]
  have hF : IsLocallyFiniteMeasure m := by
    refine ⟨fun t => ?_⟩
    obtain ⟨W, hW, hW'⟩ := hf t
    refine ⟨interior W, interior_mem_nhds.2 hW, ?_⟩
    rw [happ _ isOpen_interior.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.2 hW')
    intro g hg
    exact ⟨hg.2, interior_subset (s := W) hg.1⟩
  have h0 : m ≠ 0 := by
    intro h
    have := happ Set.univ MeasurableSet.univ
    rw [h] at this
    apply hμ
    simpa using this.symm
  have hκ := Measure.isMulLeftInvariant_eq_smul m ν
  set c := Measure.haarScalarFactor m ν
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact h0 hκ
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  have hκ' : m = (c : ℝ≥0∞) • ν := hκ
  refine ⟨c, hc', ENNReal.coe_ne_top, hκ', ?_⟩
  have : ν = (c : ℝ≥0∞)⁻¹ • m := by
    rw [hκ', smul_smul, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_smul]
  rw [this]
  infer_instance

theorem map_restrict_subgroup_eq_common_smul_haar : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (H : Subgroup G), MeasurableSet (H : Set G) → μ H ≠ 0 → ∀ (ι : Type) (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ g, ψ k' g = e (α (ψ k g))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ k, (μ.restrict H).map (ψ k) = κ • ν k := by
  intro G _ _ _ μ _ _ H hH hμ ι R _ _ _ _ _ _ _ _ ν _ ψ hψ hs hf hc
  choose κ h0 htop hκ hR using fun k =>
    map_restrict_subgroup_eq_smul_haar G μ H hH hμ (R k) (ν k) (ψ k) (hψ k) (hs k) (hf k)
  have key : ∀ k k', κ k = κ k' := by
    intro k k'
    obtain ⟨e, α, u, he, hα, hψe, hαα⟩ := hc k k'
    have := hR k
    have h1 : κ k' • ν k' = (κ k • (ν k).map α).map e := by
      rw [← hκ k', ← Measure.map_smul _ hα.aemeasurable, ← hκ k, Measure.map_map hα (hψ k),
        Measure.map_map e.measurable (hα.comp (hψ k))]
      congr 1
      funext g
      exact hψe g
    have h2 : κ k' • ν k = κ k • (ν k).map α := by
      have := congrArg (Measure.map e.symm) h1
      rw [Measure.map_smul _ e.symm.measurable.aemeasurable, (he.symm e).map_eq, MeasurableEquiv.map_symm_map] at this
      exact this
    have h3 : ((ν k).map α).map α = ν k := by
      rw [Measure.map_map hα hα]
      have : α ∘ α = (fun t => t * u) ∘ (fun t => u⁻¹ * t) := funext hαα
      rw [this, ← Measure.map_map (measurable_mul_const u) (measurable_const_mul u⁻¹),
        map_mul_left_eq_self, map_mul_right_eq_self]
    have h4 : κ k' • (ν k).map α = κ k • ν k := by
      have := congrArg (Measure.map α) h2
      rw [Measure.map_smul _ hα.aemeasurable, Measure.map_smul _ hα.aemeasurable, h3] at this
      exact this
    have h5 : (κ k' * κ k') • ν k = (κ k * κ k) • ν k := by
      rw [mul_smul, h2, smul_comm, h4, mul_smul]
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (R k)) := inferInstance
    have hK0 : ν k K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior (ν k) K.interior_nonempty).ne'
    have hKt : ν k K ≠ ⊤ := K.isCompact.measure_ne_top
    have h6 := congrArg (fun m : Measure (R k) => m K) h5
    simp only [Measure.smul_apply, smul_eq_mul] at h6
    have h7 : κ k' * κ k' = κ k * κ k := (ENNReal.mul_left_inj hK0 hKt).1 h6
    rcases lt_trichotomy (κ k) (κ k') with h | h | h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne'
    · exact h
    · exact absurd h7 (ENNReal.mul_lt_mul h h).ne
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, fun k => hι.elim k⟩
  · exact ⟨κ k₀, h0 k₀, htop k₀, fun k => by rw [hκ k, key k k₀]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LintegralUnfoldArithmeticQuotientDoubleCosets

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory.PeterssonUnfold

theorem unfold_lintegral :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  classical
  intro G _ _ _ μ _ _ Γ H Kf _ 𝓕 h𝓕 h0 htop hH hKH ι _ R _ _ _ _ _ _ _ _ ν _ ψ Λ s g P Q dict pt
    hψ hsurj hK hΓ hcomp hdisc hQ hdict hpt hcov hsep hΛ
  have hD := fun k => GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete (R k) (Λ k) (hdisc k)
  have hcount : ∀ k, Countable (Λ k) := fun k => (hD k).1
  choose D hDm hDu using fun k => (hD k).2
  have hpt' : ∀ k y, (g k)⁻¹ * y ∈ H → Q (dict y) (pt k (s k * ψ k ((g k)⁻¹ * y))) := by
    intro k y hy
    have := hpt k _ hy
    rwa [mul_inv_cancel_left] at this
  have hΓQ : ∀ δ ∈ Γ, ∀ y, Q (dict y) (dict (δ * y)) := fun δ hδ y =>
    (hdict _ _).2 ⟨δ, hδ, 1, Kf.one_mem, by rw [mul_one]⟩
  have inj1 : ∀ k k' y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k')⁻¹ * (δ * y) ∈ H →
      Q (pt k (s k * ψ k ((g k)⁻¹ * y))) (pt k' (s k' * ψ k' ((g k')⁻¹ * (δ * y)))) :=
    fun k k' y δ hδ hy hy' =>
      hQ.trans (hQ.symm (hpt' k y hy)) (hQ.trans (hΓQ δ hδ y) (hpt' k' _ hy'))
  have inj2 : ∀ k y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k)⁻¹ * (δ * y) ∈ H →
      ∃ w ∈ Λ k, s k * ψ k ((g k)⁻¹ * (δ * y)) = w * (s k * ψ k ((g k)⁻¹ * y)) ∧
        (w = 1 → δ = 1) := by
    intro k y δ hδ hy hy'
    obtain ⟨w, hw, he⟩ := (hΛ k _ _).1 (inj1 k k y δ hδ hy hy')
    refine ⟨w, hw, he, fun h1 => hΓ k δ hδ ?_⟩
    rw [h1, one_mul, mul_right_inj, map_mul, map_mul, map_mul, mul_right_inj] at he
    exact mul_eq_right.1 he
  let E : ι → Set G := fun k => {y | (g k)⁻¹ * y ∈ H ∧ s k * ψ k ((g k)⁻¹ * y) ∈ D k}
  have hms : ∀ k, Measurable fun y : G => s k * ψ k ((g k)⁻¹ * y) := fun k =>
    ((hψ k).comp (measurable_const_mul _)).const_mul _
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (measurable_const_mul (g k)⁻¹ hH).inter (hms k (hDm k))
  have cover : ∀ x, ∃ γ ∈ Γ, ∃ k, γ * x ∈ E k := by
    intro x
    obtain ⟨k, t, hq⟩ := hcov x
    obtain ⟨w, hw, -⟩ := hDu k t
    obtain ⟨h, hh, he⟩ := hsurj k ((s k)⁻¹ * (w * t))
    have h1 : Q (pt k t) (pt k (s k * ψ k h)) :=
      (hΛ k _ _).2 ⟨w, w.2, by rw [he, mul_inv_cancel_left]⟩
    obtain ⟨γ, hγ, z, hz, hx⟩ := (hdict x (g k * h)).1
      (hQ.trans hq (hQ.trans h1 (hQ.symm (hpt k h hh))))
    have h2 : (g k)⁻¹ * (γ * x) = h * z⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
    refine ⟨γ, hγ, k, ?_, ?_⟩
    · rw [h2]; exact H.mul_mem hh (H.inv_mem (hKH hz))
    · rw [h2, map_mul, map_inv, hK k z hz, inv_one, mul_one, he, mul_inv_cancel_left]
      exact hw
  have uniq : ∀ k k' y, ∀ δ ∈ Γ, y ∈ E k → δ * y ∈ E k' → k = k' ∧ δ = 1 := by
    intro k k' y δ hδ hy hy'
    obtain rfl : k = k' := hsep _ _ _ _ (inj1 k k' y δ hδ hy.1 hy'.1)
    refine ⟨rfl, ?_⟩
    obtain ⟨w, hw, he, h1⟩ := inj2 k y δ hδ hy.1 hy'.1
    refine h1 ?_
    have := (hDu k (s k * ψ k ((g k)⁻¹ * y))).unique (y₁ := ⟨w, hw⟩) (y₂ := 1)
      (by have := hy'.2; rwa [he] at this) (by simpa using hy.2)
    exact congrArg Subtype.val this
  have hE : IsFundamentalDomain Γ (⋃ k, E k) μ := by
    refine IsFundamentalDomain.mk' (MeasurableSet.iUnion hEm).nullMeasurableSet fun x => ?_
    obtain ⟨γ, hγ, k, hx⟩ := cover x
    refine ⟨⟨γ, hγ⟩, Set.mem_iUnion.2 ⟨k, hx⟩, fun γ' hγ' => ?_⟩
    obtain ⟨k', hx'⟩ := Set.mem_iUnion.1 hγ'
    have := (uniq k k' (γ * x) (γ' * γ⁻¹) (Γ.mul_mem γ'.2 (Γ.inv_mem hγ)) hx
      (by rw [mul_assoc, inv_mul_cancel_left]; exact hx')).2
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hH0 : μ H ≠ 0 := by
    intro hH0
    apply h0
    rw [h𝓕.measure_eq hE]
    refine measure_iUnion_null fun k => measure_mono_null (t := (fun y => (g k)⁻¹ * y) ⁻¹' H)
      (fun y hy => hy.1) ?_
    rw [measure_preimage_mul, hH0]
  have hloc : ∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤ := by
    intro k t
    obtain ⟨U, hU, hΛU⟩ := hdisc k
    obtain ⟨V₀, hV₀, hVU⟩ := exists_nhds_split_inv hU
    obtain ⟨V, hVV, hVo, hV1⟩ := mem_nhds_iff.1 hV₀
    have ho : IsOpen {u : R k | s k * u * (s k * t)⁻¹ ∈ V} := hVo.preimage (by fun_prop)
    refine ⟨_, ho.mem_nhds (by simpa using hV1), fun hinf => ?_⟩
    rw [← measure_preimage_mul μ (g k)⁻¹] at hinf
    obtain ⟨x, hx, y, hy, δ, hδ, hxy⟩ := h𝓕.exists_ne_one_smul_eq
      (measurable_const_mul (g k)⁻¹ (hH.inter (hψ k ho.measurableSet))).nullMeasurableSet
      (by rw [hinf]; exact lt_top_iff_ne_top.2 htop)
    subst hxy
    obtain ⟨w, hw, he, h1⟩ := inj2 k x δ δ.2 hx.1 hy.1
    refine hδ (Subtype.ext (h1 (hΛU w hw ?_)))
    have h2 : s k * ψ k ((g k)⁻¹ * (δ * x)) * (s k * t)⁻¹ ∈ V := hy.2
    have h3 : s k * ψ k ((g k)⁻¹ * x) * (s k * t)⁻¹ ∈ V := hx.2
    rw [he, mul_assoc] at h2
    have := hVU _ (hVV h2) _ (hVV h3)
    rwa [mul_div_cancel_right] at this
  obtain ⟨κ, hκ0, hκt, hκ⟩ := GlobalTheory.map_restrict_subgroup_eq_common_smul_haar G μ H hH hH0 ι R ν ψ hψ hsurj hloc hcomp
  refine ⟨κ, D, hκ0, hκt, fun k => ⟨hcount k,
    IsFundamentalDomain.mk' (hDm k).nullMeasurableSet (hDu k)⟩, fun Φ hΦ hΦm => ?_⟩
  have hinv : ∀ δ ∈ Γ, ∀ y, Φ (dict (δ * y)) = Φ (dict y) := fun δ hδ y => hΦ _ _ (hΓQ δ hδ y)
  have hval : ∀ k y, (g k)⁻¹ * y ∈ H → Φ (dict y) = Φ (pt k (s k * ψ k ((g k)⁻¹ * y))) :=
    fun k y hy => (hΦ _ _ (hpt' k y hy)).symm
  refine ⟨fun B hB => ?_, ?_⟩
  · have : (fun x => Φ (dict x)) ⁻¹' B = ⋃ γ : Γ, ⋃ k, (fun x => (γ : G) * x) ⁻¹'
        (((fun y => (g k)⁻¹ * y) ⁻¹' H) ∩
          (fun y => Φ (pt k (s k * ψ k ((g k)⁻¹ * y)))) ⁻¹' B) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨γ, hγ, k, hk⟩ := cover x
        refine ⟨⟨γ, hγ⟩, k, hk.1, ?_⟩
        rw [← hval k _ hk.1, hinv γ hγ]; exact hx
      · rintro ⟨γ, k, hk, hx⟩
        rwa [← hval k _ hk, hinv γ γ.2] at hx
    rw [this]
    exact MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun k => measurable_const_mul _
      ((measurable_const_mul _ hH).inter (((hΦm k).comp (hms k)) hB))
  · rw [h𝓕.setLIntegral_eq hE _ fun γ x => hinv γ γ.2 x,
      lintegral_iUnion hEm (fun k k' hk => Set.disjoint_left.2 fun y hy hy' =>
        hk (uniq k k' y 1 Γ.one_mem hy (by rwa [one_mul])).1), tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    let F : R k → ℝ≥0∞ := (D k).indicator fun t => Φ (pt k t)
    have hF : Measurable F := (hΦm k).indicator (hDm k)
    calc ∫⁻ x in E k, Φ (dict x) ∂μ
        = ∫⁻ x, (H : Set G).indicator (fun h => F (s k * ψ k h)) ((g k)⁻¹ * x) ∂μ := by
          rw [← lintegral_indicator (hEm k)]
          refine lintegral_congr fun x => ?_
          by_cases hx : (g k)⁻¹ * x ∈ H
          · rw [Set.indicator_of_mem (s := (H : Set G)) hx]
            by_cases hx' : s k * ψ k ((g k)⁻¹ * x) ∈ D k
            · rw [Set.indicator_of_mem (show x ∈ E k from ⟨hx, hx'⟩), hval k x hx]
              exact (Set.indicator_of_mem hx' fun t => Φ (pt k t)).symm
            · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx' h.2)]
              exact (Set.indicator_of_notMem hx' fun t => Φ (pt k t)).symm
          · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx h.1),
              Set.indicator_of_notMem (s := (H : Set G)) hx]
      _ = ∫⁻ h in (H : Set G), F (s k * ψ k h) ∂μ := by
          rw [lintegral_mul_left_eq_self
            ((H : Set G).indicator (fun h => F (s k * ψ k h))) (g k)⁻¹, lintegral_indicator hH]
      _ = ∫⁻ t, F (s k * t) ∂((μ.restrict H).map (ψ k)) :=
          (lintegral_map (f := fun t => F (s k * t)) (hF.comp (measurable_const_mul _)) (hψ k)).symm
      _ = κ * ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
          rw [hκ, lintegral_smul_measure, lintegral_mul_left_eq_self F, lintegral_indicator (hDm k),
            smul_eq_mul]

end GlobalTheory.PeterssonUnfold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LintegralUnfoldArithmeticQuotientDoubleCosetsStatement

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_unfold_arithmetic_quotient_doubleCosets : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  first | exact @GlobalTheory.PeterssonUnfold.unfold_lintegral | exact GlobalTheory.PeterssonUnfold.unfold_lintegral | (intros; apply GlobalTheory.PeterssonUnfold.unfold_lintegral <;> assumption)
end
end
