module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace GlobalTheory.UnipAvg

-- These private lemmas adapt the averaging argument from IsMulRightInvariantOfCovolumeOne.
private theorem tsum_eq_tsum_quotient {A : Type*} [Group A] (S : Subgroup A) (f : A → ℝ≥0∞) :
    ∑' a, f a = ∑' q : A ⧸ S, ∑' s : S, f (q.out * s) := by
  rw [← tsum_fiberwise f (QuotientGroup.mk : A → A ⧸ S)]
  refine tsum_congr fun q => ?_
  change (∑' a : {a : A | (a : A ⧸ S) = q}, f a) = _
  conv_lhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq_class_eq_leftCoset]
  exact ((Subgroup.leftCosetEquivSubgroup (s := S) q.out).symm.tsum_eq _).symm

section Covolume

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

private theorem isMulRightInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsMulRightInvariant := by
  have : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  refine ⟨fun u => ?_⟩
  have hD' : IsFundamentalDomain U₀ ((· * u) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν u) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x u)
  have h1 : (ν.map (· * u)) D = 1 := by
    have := (MeasurableEquiv.mulRight u).map_apply (μ := ν) D
    simp only [MeasurableEquiv.coe_mulRight] at this
    rw [this, hD'.measure_eq hD, hνD]
  have : SigmaFinite (ν.map (· * u)) := (MeasurableEquiv.mulRight u).sigmaFinite_map
  have h := measure_eq_div_smul (ν.map (· * u)) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [h, h1, hνD]; simp

private theorem isInvInvariant_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1) :
    ν.IsInvInvariant := by
  have := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have h := measure_eq_div_smul ν.inv ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  rw [hνD, div_one] at h
  set c := ν.inv D with hc
  have h2 : ν = (c * c) • ν := by
    calc ν = ν.inv.inv := (Measure.inv_inv ν).symm
      _ = (c • ν).inv := by rw [← h]
      _ = c • ν.inv := Measure.map_smul c measurable_inv.aemeasurable
      _ = (c * c) • ν := by rw [h, smul_smul]
  have h3 : c * c = 1 := by
    have := congrArg (fun m : Measure U => m D) h2
    simpa [hνD] using this.symm
  have h4 : c = 1 := by
    rcases lt_trichotomy c 1 with hlt | heq | hgt
    · have : c * c < 1 := lt_of_le_of_lt (by simpa using mul_le_mul_right hlt.le c) hlt
      exact absurd h3 this.ne
    · exact heq
    · have : 1 < c * c := lt_of_lt_of_le hgt (by simpa using mul_le_mul_right hgt.le c)
      exact absurd h3 this.ne'
  exact ⟨by rw [h, h4, one_smul]⟩


omit [MeasurableInv U] in
private theorem tsum_setLIntegral_eq_index (ν : Measure U) [ν.IsMulLeftInvariant]
    (U₀ L : Subgroup U) [Countable U₀] (hle : U₀ ≤ L) {D : Set U} (hD : IsFundamentalDomain U₀ D ν)
    (ψ : U → ℝ≥0∞) :
    ∑' l : L, ∫⁻ u in D, ψ (l * u) ∂ν = ∑' _q : L ⧸ U₀.subgroupOf L, ∫⁻ u, ψ u ∂ν := by
  have : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  rw [tsum_eq_tsum_quotient (U₀.subgroupOf L)]
  refine tsum_congr fun q => ?_
  rw [← lintegral_mul_left_eq_self ψ ((q.out : L) : U), hD.lintegral_eq_tsum'',
    ← (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq]
  refine tsum_congr fun b => lintegral_congr fun u => ?_
  congr 1
  exact mul_assoc _ _ _

theorem measurePreserving_mulEquiv_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (c : U ≃* U) (hc : Measurable c) (hc' : Measurable c.symm)
    (h₁ : ∀ b ∈ U₀, c b ∈ U₀) (h₂ : ∀ b ∈ U₀, c.symm b ∈ U₀) : MeasurePreserving c ν ν := by
  have : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  let e : U ≃ᵐ U := ⟨c.toEquiv, hc, hc'⟩
  have : SigmaFinite (ν.map c) := e.sigmaFinite_map
  have : (ν.map c).IsMulLeftInvariant := ⟨fun g => by
    rw [map_map (measurable_const_mul g) hc]
    conv_rhs => rw [← map_mul_left_eq_self ν (c.symm g), map_map hc (measurable_const_mul _)]
    congr 1
    ext x
    simp⟩
  have h := measure_eq_div_smul (ν.map c) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  have hq : QuasiMeasurePreserving c ν ν := ⟨hc.aemeasurable, by rw [h]; exact smul_absolutelyContinuous⟩
  have hD' : IsFundamentalDomain U₀ (c ⁻¹' D) ν :=
    hD.preimage_of_equiv hq (e := fun b : U₀ => (⟨c.symm b, h₂ b b.2⟩ : U₀))
      ⟨fun b b' hb => Subtype.ext (c.symm.injective (congrArg Subtype.val hb)),
        fun b => ⟨⟨c b, h₁ b b.2⟩, Subtype.ext (c.symm_apply_apply b)⟩⟩
      (fun b x => by
        change c (c.symm b * x) = b * c x
        simp)
  have h1 : (ν.map c) D = 1 := by
    have : (ν.map c) D = ν (c ⁻¹' D) := e.map_apply (μ := ν) D
    rw [this, hD'.measure_eq hD, hνD]
  refine ⟨hc, ?_⟩
  rw [h, h1, hνD]; simp

theorem setLIntegral_mul_right_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (f : U → ℝ≥0∞) (hf : ∀ b ∈ U₀, ∀ u, f (b * u) = f u) (v : U) :
    ∫⁻ u in D, f (u * v) ∂ν = ∫⁻ u in D, f u ∂ν := by
  have : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  have := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have hD' : IsFundamentalDomain U₀ ((· * v) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν v) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x v)
  rw [hD.setLIntegral_eq hD' (fun u => f (u * v)) (fun b x => by
    change f ((b : U) * x * v) = _
    rw [mul_assoc, hf _ b.2])]
  exact (measurePreserving_mul_right ν v).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.mulRight v).measurableEmbedding f D

end Covolume

theorem setLIntegral_add_left_of_periodic {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (ν : Measure A) [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀] {D : Set A}
    (hD : IsAddFundamentalDomain A₀ D ν) (f : A → ℝ≥0∞) (hf : ∀ b ∈ A₀, ∀ y, f (b + y) = f y) (t : A) :
    ∫⁻ y in D, f (t + y) ∂ν = ∫⁻ y in D, f y ∂ν := by
  have : VAddInvariantMeasure A₀ A ν := ⟨fun γ s _ => measure_preimage_add ν (γ : A) s⟩
  have hD' : IsAddFundamentalDomain A₀ ((t + ·) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_left ν t).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => add_left_comm t (g : A) x)
  rw [hD.setLIntegral_eq hD' (fun u => f (t + u)) (fun b x => by
    change f (t + ((b : A) + x)) = _
    rw [add_left_comm, hf _ b.2])]
  exact (measurePreserving_add_left ν t).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding f D

theorem exists_covolume_one_of_cocompact {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
    [LocallyCompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (U₀ : Subgroup U) [DiscreteTopology U₀] {K : Set U} (hK : IsCompact K) (hcov : ∀ u, ∃ b ∈ U₀, b * u ∈ K) :
    ∃ (ν : Measure U) (D : Set U), SigmaFinite ν ∧ ν.IsMulLeftInvariant ∧ IsFundamentalDomain U₀ D ν ∧ ν D = 1 := by
  have := countable_of_discrete_subgroup U₀
  obtain ⟨D, -, -, hD⟩ := exists_isFundamentalDomain_subgroup U₀
  let m : Measure U := haar
  have : SMulInvariantMeasure U₀ U m := ⟨fun γ s _ => measure_preimage_mul m (γ : U) s⟩
  have h0 : m D ≠ 0 := (hD m).measure_ne_zero (NeZero.ne m)
  have h1 : m D ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := m)))
    rw [(hD m).measure_eq_tsum K]
    refine le_trans (measure_mono fun u hu => ?_) (measure_iUnion_le _)
    obtain ⟨b, hb, hbu⟩ := hcov u
    exact mem_iUnion.2 ⟨(⟨b, hb⟩ : U₀)⁻¹, mem_inv_smul_set_iff.2 hbu, hu⟩
  have : ((m D)⁻¹ • m).IsHaarMeasure := IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
  exact ⟨(m D)⁻¹ • m, D, inferInstance, inferInstance, hD _, by
    rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

section Average

variable {G U : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]


omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableInv U] in
private theorem tsum_setLIntegral_eq_cosets (ι : U →* G) (hι : Function.Injective ι) (ν : Measure U) [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν) (φ : G → ℝ≥0∞) :
    ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν =
      ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' _k : Γ.comap ι ⧸ U₀.subgroupOf (Γ.comap ι),
        ∫⁻ u, φ ((q.out : Γ) * ι u) ∂ν := by
  rw [tsum_eq_tsum_quotient (ι.range.subgroupOf Γ)]
  refine tsum_congr fun q => ?_
  rw [← tsum_setLIntegral_eq_index ν U₀ _ hle hD (fun u => φ ((q.out : Γ) * ι u))]
  let e : Γ.comap ι → ι.range.subgroupOf Γ := fun l => ⟨⟨ι l, l.2⟩, ⟨l, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro l l' h
      exact Subtype.ext (hι (congrArg (fun s : ι.range.subgroupOf Γ => ((s : Γ) : G)) h))
    · rintro ⟨⟨γ, hγ⟩, ⟨l, hl⟩⟩
      have hl' : ι l = γ := hl
      subst hl'
      exact ⟨⟨l, hγ⟩, rfl⟩
  rw [← (Equiv.ofBijective e he).tsum_eq]
  refine tsum_congr fun l => lintegral_congr fun u => ?_
  simp [e, mul_assoc]

omit [MeasurableInv G] in
private theorem tsum_setLIntegral_inv (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι) (ν : Measure U)
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ : Subgroup G) (U₀ : Subgroup U) [Countable U₀] (hle : U₀ ≤ Γ.comap ι) {D : Set U}
    (hD : IsFundamentalDomain U₀ D ν)
    (hconj : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, φ (γ * ι u) ∂ν := by
  have : (ι.range.subgroupOf Γ).Normal := ⟨by
    rintro ⟨n, hn⟩ ⟨u, hu⟩ g
    obtain ⟨c, -, hc⟩ := hconj (g : G)⁻¹ (Γ.inv_mem g.2)
    have hu' : ι u = n := hu
    exact ⟨c u, by rw [hc, hu']; simp⟩⟩
  have h1 : ∑' γ : Γ, ∫⁻ u in D, φ ((ι u)⁻¹ * γ) ∂ν = ∑' γ : Γ, ∫⁻ u in D, (fun x => φ x⁻¹) (γ * ι u) ∂ν := by
    rw [← (Equiv.inv Γ).tsum_eq]
    simp
  rw [h1, tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD (fun x => φ x⁻¹),
    tsum_setLIntegral_eq_cosets ι hι ν Γ U₀ hle hD,
    ← (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ)).tsum_eq]
  refine tsum_congr fun q => tsum_congr fun _ => ?_
  set t : Γ := (Equiv.inv (Γ ⧸ ι.range.subgroupOf Γ) q).out with ht
  have hmem : t * q.out ∈ ι.range.subgroupOf Γ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ht]
    simp
  obtain ⟨v, hv⟩ := hmem
  have hv' : ι v = (t : G) * (q.out : Γ) := hv
  obtain ⟨c, hcm, hc⟩ := hconj (t : G)⁻¹ (Γ.inv_mem t.2)
  calc ∫⁻ u, φ ((t : G) * ι u)⁻¹ ∂ν = ∫⁻ u, φ (ι u * (t : G)⁻¹) ∂ν := by
        rw [← lintegral_inv_eq_self (μ := ν) (fun u => φ (ι u * (t : G)⁻¹))]
        simp
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (c u)) ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hc]; congr 1; group
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι u) ∂ν :=
        hcm.lintegral_comp (f := fun u => φ ((t : G)⁻¹ * ι u)) (hφ.comp (hιm.const_mul _))
    _ = ∫⁻ u, φ ((t : G)⁻¹ * ι (v * u)) ∂ν :=
        (lintegral_mul_left_eq_self (fun u => φ ((t : G)⁻¹ * ι u)) v).symm
    _ = _ := by
        refine lintegral_congr fun u => ?_
        rw [map_mul, hv']; congr 1; group


omit [MeasurableInv G] in
private theorem lintegral_mul_tsum_weight (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {β : G → ℝ≥0∞} (hβm : Measurable β)
    (hβ : ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ) (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (w : G) :
    ∫⁻ g, ρ g * ∑' γ : Γ, β (γ * w * g) ∂μ = ∫⁻ g, ρ g ∂μ := by
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun (γ : Γ) g => ρ g * β (γ * w * g))
      fun γ => (hρ.mul (hβm.comp (measurable_const_mul _))).aemeasurable,
    ← lintegral_mul_left_eq_self ρ w⁻¹, h𝓕.lintegral_eq_tsum']
  refine tsum_congr fun γ => ?_
  rw [hβ, ← lintegral_mul_left_eq_self _ ((γ : G) * w)⁻¹]
  refine lintegral_congr fun g => ?_
  rw [mul_comm, mul_inv_cancel_left]
  congr 2
  change _ = w⁻¹ * (((γ⁻¹ : Γ) : G) * g)
  simp [mul_assoc]

private theorem setLIntegral_average (ι : U →* G) (hι : Function.Injective ι) (hιm : Measurable ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] (U₀ : Subgroup U) [Countable U₀] (hle : ∀ b ∈ U₀, ι b ∈ Γ)
    (hconj : ∀ γ ∈ Γ, ∃ c : U → U, MeasurePreserving c ν ν ∧ ∀ u, ι (c u) = γ⁻¹ * ι u * γ)
    {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) :
    ∫⁻ g in 𝓕, F g ∂μ = ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ := by
  have := isInvInvariant_of_covolume_one ν U₀ hD hνD
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  obtain ⟨β, hβm, hβ⟩ : ∃ β : G → ℝ≥0∞, Measurable β ∧
      ∀ f : G → ℝ≥0∞, ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, β g * f g ∂μ := by
    refine ⟨(toMeasurable μ 𝓕).indicator 1, measurable_one.indicator (measurableSet_toMeasurable μ 𝓕), fun f => ?_⟩
    rw [← restrict_congr_set h𝓕.nullMeasurableSet.toMeasurable_ae_eq,
      ← lintegral_indicator (measurableSet_toMeasurable μ 𝓕)]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ toMeasurable μ 𝓕 <;> simp [hg]
  have hA : ∀ w : G, ∫⁻ g in 𝓕, F (w * g) ∂μ = ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (w⁻¹ * γ * g) ∂μ := by
    intro w
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum (f := fun (γ : Γ) g => F g * β (w⁻¹ * γ * g))
      fun γ => (hF.mul (hβm.comp (measurable_const_mul _))).aemeasurable, hβ,
      ← lintegral_mul_left_eq_self _ w⁻¹, h𝓕.lintegral_eq_tsum'']
    refine tsum_congr fun γ => lintegral_congr fun g => ?_
    change β (w⁻¹ * (γ * g)) * F (w * (w⁻¹ * (γ * g))) = _
    rw [mul_inv_cancel_left, hinv _ γ.2, mul_comm, mul_assoc]
  have hm1 : Measurable fun p : G × U => ∑' γ : Γ, β ((ι p.2)⁻¹ * γ * p.1) :=
    Measurable.tsum fun γ => hβm.comp (((hιm.comp measurable_snd).inv.mul_const _).mul measurable_fst)
  have hm2 : Measurable fun p : G × U => ∑' γ : Γ, β (γ * ι p.2 * p.1) :=
    Measurable.tsum fun γ => hβm.comp (((hιm.comp measurable_snd).const_mul _).mul measurable_fst)
  symm
  calc ∫⁻ g in 𝓕, ∫⁻ u in D, F (ι u * g) ∂ν ∂μ = ∫⁻ u in D, ∫⁻ g in 𝓕, F (ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap (hF.comp ((hιm.comp measurable_snd).mul measurable_fst)).aemeasurable
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂μ ∂ν := lintegral_congr fun u => hA _
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β ((ι u)⁻¹ * γ * g) ∂ν ∂μ :=
        (lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm1).aemeasurable).symm
    _ = ∫⁻ g in 𝓕, ∫⁻ u in D, F g * ∑' γ : Γ, β (γ * ι u * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        have hleft : ∀ γ : Γ, Measurable (fun u : U => β ((ι u)⁻¹ * γ * g)) := fun γ =>
          hβm.comp ((hιm.inv.mul_const (γ : G)).mul_const g)
        have hright : ∀ γ : Γ, Measurable (fun u : U => β (γ * ι u * g)) := fun γ =>
          hβm.comp ((hιm.const_mul (γ : G)).mul_const g)
        rw [lintegral_const_mul (F g) (Measurable.tsum hleft),
          lintegral_const_mul (F g) (Measurable.tsum hright),
          lintegral_tsum (f := fun (γ : Γ) u => β ((ι u)⁻¹ * γ * g))
            fun γ => (hleft γ).aemeasurable,
          lintegral_tsum (f := fun (γ : Γ) u => β (γ * ι u * g))
            fun γ => (hright γ).aemeasurable,
          tsum_setLIntegral_inv ι hι hιm ν Γ U₀ hle hD hconj (fun x => β (x * g))
            (hβm.comp (measurable_mul_const g))]
    _ = ∫⁻ u in D, ∫⁻ g in 𝓕, F g * ∑' γ : Γ, β (γ * ι u * g) ∂μ ∂ν :=
        lintegral_lintegral_swap ((hF.comp measurable_fst).mul hm2).aemeasurable
    _ = ∫⁻ _u in D, ∫⁻ g in 𝓕, F g ∂μ ∂ν := by
        refine lintegral_congr fun u => ?_
        rw [hβ, hβ F, ← lintegral_mul_tsum_weight μ Γ h𝓕 hβm hβ (fun g => β g * F g) (hβm.mul hF) (ι u)]
        simp_rw [mul_assoc]
    _ = ∫⁻ g in 𝓕, F g ∂μ := by simp [hνD]

end Average

theorem setLIntegral_average_abelian_quotient : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  intro G A _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ Γ U _ hU hnorm ⟨K, hK, hcov⟩ ι hadd hιm hιU ν _ _ A₀ _ hA₀ D hD hνD 𝓕 h𝓕
    Φ hΦ hinv hact
  have := countable_of_discrete_subgroup Γ
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  have : DiscreteTopology (Γ.subgroupOf U) :=
    DiscreteTopology.of_continuous_injective (f := fun b : Γ.subgroupOf U => (⟨(b : U), b.2⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun b b' h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h)))
  have := countable_of_discrete_subgroup (Γ.subgroupOf U)
  obtain ⟨m, E, _, _, hE, hmE⟩ := exists_covolume_one_of_cocompact (Γ.subgroupOf U)
    (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK) (fun u => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov u u.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  have hconj : ∀ a ∈ (Γ : Set G), ∃ c : U → U, MeasurePreserving c m m ∧
      ∀ u, U.subtype (c u) = a⁻¹ * U.subtype u * a := by
    intro a ha
    have ha' : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => by simpa using hnorm a⁻¹ (Γ.inv_mem ha) u hu
    let c : U ≃* U :=
      { toFun := fun u => ⟨a⁻¹ * u * a, hnorm a ha u u.2⟩
        invFun := fun u => ⟨a * u * a⁻¹, ha' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp only; group)
        right_inv := fun u => Subtype.ext (by simp only; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    exact ⟨c, measurePreserving_mulEquiv_of_covolume_one m _ hE hmE c
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (fun b hb => Γ.mul_mem (Γ.mul_mem (Γ.inv_mem ha) hb) ha)
      (fun b hb => Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)), fun _ => rfl⟩
  rw [setLIntegral_average U.subtype Subtype.val_injective measurable_subtype_coe μ m Γ (Γ.subgroupOf U)
    (fun b hb => hb) hconj hE hmE h𝓕 Φ hΦ hinv]
  refine lintegral_congr fun g => ?_
  calc ∫⁻ u in E, Φ (U.subtype u * g) ∂m = ∫⁻ _y in D, ∫⁻ u in E, Φ ((u : G) * g) ∂m ∂ν := by simp [hνD]
    _ = ∫⁻ y in D, ∫⁻ u in E, Φ ((u : G) * (ι y * g)) ∂m ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [← setLIntegral_mul_right_of_covolume_one m _ hE hmE (fun u => Φ ((u : G) * g))
          (fun b hb u => by rw [Subgroup.coe_mul, mul_assoc, hinv (b : G) hb]) ⟨ι y, hιU y⟩]
        simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ u in E, ∫⁻ y in D, Φ ((u : G) * (ι y * g)) ∂ν ∂m :=
        lintegral_lintegral_swap (hΦ.comp ((measurable_subtype_coe.comp measurable_snd).mul
          ((hιm.comp measurable_fst).mul_const g))).aemeasurable
    _ = ∫⁻ _u in E, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂m := by
        refine lintegral_congr fun u => ?_
        obtain ⟨t, ht⟩ := hact u u.2
        rw [← setLIntegral_add_left_of_periodic ν A₀ hD (fun y => Φ (ι y * g))
          (fun b hb y => by rw [hadd, mul_assoc, hinv _ (hA₀ b hb)]) t]
        simp only [ht, hadd, mul_assoc]
    _ = ∫⁻ y in D, Φ (ι y * g) ∂ν := by simp [hmE]

end GlobalTheory.UnipAvg
