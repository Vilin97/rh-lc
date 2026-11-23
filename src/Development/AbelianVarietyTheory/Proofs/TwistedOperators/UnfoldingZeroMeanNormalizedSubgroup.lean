module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AedisjointPairGroupSmulShearedDomainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapConjNormalizingLatticeEqSelfStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroupStatement
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeExistsPairGroupSmulMemShearedDomain

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem ae_exists_pairGroup_smul_mem_shear : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hconj 𝓕 h𝓕
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  have hgoodn : ∀ᵐ n : N ∂κ, ∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N) ∈ 𝓝 := by
    rw [ae_all_iff]
    intro v
    have hc : Continuous (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) :=
      Continuous.subtype_mk (by fun_prop) _
    have hmp : MeasurePreserving (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) κ κ :=
      ⟨hc.measurable, hconj v v.2⟩
    exact hmp.quasiMeasurePreserving.ae h𝓝.ae_covers
  have hboth : ∀ᵐ p ∂(κ.prod ν), (∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * p.1 * (v : H)⁻¹, hN v v.2 p.1 p.1.2⟩ : N) ∈ 𝓝) ∧
      ∃ v : Γ, v • p.2 ∈ 𝓕 :=
    (Measure.quasiMeasurePreserving_fst.ae hgoodn).and
      (Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers)
  rw [(measurableEmbedding_shear hNc).ae_map_iff]
  filter_upwards [hboth] with p hp
  obtain ⟨n, h⟩ := p
  obtain ⟨hn, v, hv⟩ := hp
  obtain ⟨δ, hδ⟩ := hn v
  have hδN : ((δ : N) : H) ∈ N := (δ : N).2
  have hδΓ : ((δ : N) : H) ∈ Γ := δ.2
  refine ⟨⟨(((δ : N) : H) * v, (v : H)), Γ.mul_mem hδΓ v.2, v.2, ?_⟩, ?_⟩
  · simpa using hδN
  · refine ⟨(_, v • h), ⟨hδ, hv⟩, ?_⟩
    ext
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def, mul_assoc]
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def]

end GlobalTheory.UnfoldNormal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeExistsPairGroupSmulMemShearedDomainStatement

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

theorem _root_.GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  first | exact @GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear | exact GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear | (intros; apply GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomainStatement

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

theorem _root_.GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by
  first | exact @GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | exact GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | (intros; apply GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodular

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem map_swap_map_shear (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI := hκ
  have hsh : Measurable (shear N) := (measurableEmbedding_shear hNc).measurable
  have hT : MeasurePreserving (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) (κ.prod ν) (κ.prod ν) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : H) => (n : H) * h)
      ⟨measurable_inv, hinv⟩ ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun n => (measurePreserving_mul_left ν (n : H)).map_eq
  have hcomm : Prod.swap ∘ shear N = shear N ∘ (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) := by
    funext p
    simp [shear]
  rw [Measure.map_map measurable_swap hsh, hcomm, ← Measure.map_map hsh hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodularStatement

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

theorem _root_.GlobalTheory.T.map_swap_sheared_product_measure_unimodular : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H), IsClosed (N : Set H) → ∀ (κ : Measure N), κ.IsHaarMeasure → κ.map (fun n => n⁻¹) = κ → ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  first | exact @GlobalTheory.UnfoldNormal.map_swap_map_shear | exact GlobalTheory.UnfoldNormal.map_swap_map_shear | (intros; apply GlobalTheory.UnfoldNormal.map_swap_map_shear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.UnfoldNormal

theorem unfold_zero_mean : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ K F : H → ℂ, Measurable K → Measurable F → (∀ n ∈ N, ∀ h, K (n * h) = K h) → (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ h, ∫ n in 𝓝, F ((n : H) * h) ∂κ = 0) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → IntegrableOn (fun h => K h * F h) 𝓕 ν → ∫ h in 𝓕, K h * F h ∂ν = 0 := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t K F hKm hFm hKN hKΓ hFΓ h0 𝓕 h𝓕 hint
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaCompactSpace N := inferInstance
  haveI : SigmaFinite κ := inferInstance
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun y : Γ => (y : H)) hab
  have hR : ∀ n₀ : N, κ.map (· * n₀) = κ := GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain H Γ N hΓ hNc κ 𝓝 hκ h𝓝 h𝓝t
  have hI : κ.map (fun n => n⁻¹) = κ := by
    haveI : κ.IsMulRightInvariant := ⟨hR⟩
    exact (GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant κ).inv_eq_self
  have hC : ∀ γ (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ :=
    GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self H Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t
  have hemb : MeasurableEmbedding (shear N) := measurableEmbedding_shear hNc
  set G := pairGroup Γ N hN with hG
  set μ := (κ.prod ν).map (shear N) with hμ
  haveI : Countable G := by
    refine Function.Injective.countable (f := fun g : G => ((⟨(g : H × H).1, g.2.1⟩ : Γ), (⟨(g : H × H).2, g.2.2.1⟩ : Γ))) ?_
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    exact Subtype.ext (Prod.ext hab.1 hab.2)
  haveI : MeasurableConstSMul G (H × H) := inferInstance
  haveI : SMulInvariantMeasure G (H × H) μ := GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup H ν Γ N hNc hN κ hκ hC
  have hS : IsFundamentalDomain G (shear N '' (𝓝 ×ˢ 𝓕)) μ :=
    ⟨nullMeasurableSet_shear_image hNc κ ν h𝓝.nullMeasurableSet h𝓕.nullMeasurableSet,
      GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕, GlobalTheory.T.aedisjoint_pairGroup_smul_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕⟩
  have hsw : μ.map Prod.swap = μ := GlobalTheory.T.map_swap_sheared_product_measure_unimodular H ν N hNc κ hκ hI
  set S := shear N '' (𝓝 ×ˢ 𝓕) with hSdef
  set f : H → ℂ := fun x => K x * F x with hf
  have hmp : MeasurePreserving (shear N) (κ.prod ν) μ := ⟨hemb.measurable, rfl⟩
  have hsp : MeasurePreserving (Prod.swap : H × H → H × H) μ μ := ⟨measurable_swap, hsw⟩
  have hswemb : MeasurableEmbedding (Prod.swap : H × H → H × H) := MeasurableEquiv.prodComm.measurableEmbedding
  let e : G → G := fun g => ⟨(g : H × H).swap, by
    obtain ⟨h1, h2, h3⟩ := g.2
    refine ⟨h2, h1, ?_⟩
    have : (g : H × H).2 * ((g : H × H).1)⁻¹ = ((g : H × H).1 * ((g : H × H).2)⁻¹)⁻¹ := by group
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [this]; exact N.inv_mem h3⟩
  have he : Function.Bijective e := by
    have : Function.Involutive e := fun g => Subtype.ext (Prod.swap_swap _)
    exact this.bijective
  have hS2 : IsFundamentalDomain G (Prod.swap ⁻¹' S) μ := by
    refine hS.preimage_of_equiv hsp.quasiMeasurePreserving he fun g x => ?_
    rfl
  have hΦ : ∀ (g : G) (p : H × H), f (g • p).1 = f p.1 := by
    intro g p
    have hu : (g : H × H).1 ∈ Γ := g.2.1
    change K ((g : H × H).1 * p.1) * F ((g : H × H).1 * p.1) = K p.1 * F p.1
    rw [hKΓ _ hu, hFΓ _ hu]
  have step1 : ∫ p in S, f p.1 ∂μ = ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ :=
    hS.setIntegral_eq hS2 (f := fun p => f p.1) hΦ
  have step2 : ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ = ∫ p in S, f p.2 ∂μ :=
    hsp.setIntegral_preimage_emb hswemb (fun p => f p.2) S
  have step3 : ∀ g : H × H → ℂ, ∫ p in S, g p ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, g (shear N q) ∂(κ.prod ν) :=
    fun g => hmp.setIntegral_image_emb hemb g _

  have hint2 : IntegrableOn (fun p : H × H => f p.1) S μ := by
    rw [hS.integrableOn_iff hS2 (f := fun p => f p.1) hΦ]
    have h2 : IntegrableOn (fun p : H × H => f p.2) S μ := by
      rw [hmp.integrableOn_image hemb]
      haveI : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.2 h𝓝t
      change Integrable (fun q : N × H => f q.2) ((κ.prod ν).restrict (𝓝 ×ˢ 𝓕))
      rw [← Measure.prod_restrict]
      exact hint.comp_snd (κ.restrict 𝓝)
    exact (hsp.integrableOn_comp_preimage hswemb).2 h2
  have hint3 : Integrable (fun q : N × H => f ((q.1 : H) * q.2)) ((κ.restrict 𝓝).prod (ν.restrict 𝓕)) := by
    rw [Measure.prod_restrict]
    exact (hmp.integrableOn_image hemb).1 hint2
  have lhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) = 0 := by
    rw [← Measure.prod_restrict]
    change ∫ q : N × H, f ((q.1 : H) * q.2) ∂((κ.restrict 𝓝).prod (ν.restrict 𝓕)) = 0
    rw [integral_prod_symm _ hint3]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [shear, hf, Pi.zero_apply]
    have : ∀ x : N, K ((x : H) * y) * F ((x : H) * y) = K y * F ((x : H) * y) := fun x => by rw [hKN _ x.2]
    simp_rw [this]
    rw [integral_const_mul, h0, mul_zero]
  have rhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) = (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν := by
    rw [← Measure.prod_restrict]
    simp only [shear]
    rw [integral_fun_snd, measureReal_restrict_apply_univ]
    rfl
  have key : (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν = 0 := by
    have e1 : ∫ p in S, f p.1 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) := step3 _
    have e2 : ∫ p in S, f p.2 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) := step3 _
    rw [← rhs, ← e2, ← step2, ← step1, e1, lhs]
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hpos : (κ 𝓝).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hne, h𝓝t⟩
  exact (smul_eq_zero.1 key).resolve_left hpos

end GlobalTheory.UnfoldNormal
end
end
