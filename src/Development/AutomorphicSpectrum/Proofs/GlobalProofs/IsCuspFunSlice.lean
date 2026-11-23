module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLieStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameRankLeWittIndexStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsotropicFrameWittBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPartStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatibleStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureProductGroups

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.Cusp.SemidirectConst

theorem map_restrict_isMulRightInvariant : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous π → (∀ u, π (s u) = u) →
    (∀ δ ∈ Δ, π δ = 1) → ((μ.restrict D).map π).IsMulRightInvariant := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ _ D hD s π hπ hπs hπΔ
  refine ⟨fun u₀ => ?_⟩
  ext B hB
  have hP : MeasurableSet (π ⁻¹' B) := hπ.measurable hB
  rw [Measure.map_apply (measurable_mul_const u₀) hB, Measure.map_apply hπ.measurable hB,
    Measure.map_apply hπ.measurable (measurable_mul_const u₀ hB), Measure.restrict_apply hP,
    Measure.restrict_apply (hπ.measurable (measurable_mul_const u₀ hB))]
  have e1 : π ⁻¹' ((· * u₀) ⁻¹' B) ∩ D = (· * s u₀) ⁻¹' (π ⁻¹' B ∩ (· * (s u₀)⁻¹) ⁻¹' D) := by
    ext v; simp [map_mul, hπs]
  have hD' : IsFundamentalDomain Δ ((· * (s u₀)⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ (s u₀)⁻¹).quasiMeasurePreserving Function.bijective_id
      fun γ x => mul_assoc _ _ _
  rw [e1, measure_preimage_mul_right]
  exact hD'.measure_set_eq hD hP fun δ => by
    ext v; simp [Subgroup.smul_def, map_mul, hπΔ δ δ.2]


open scoped Pointwise in
theorem map_restrict_isFiniteMeasureOnCompacts : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [T2Space N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) →
    (∃ K : Set N, IsCompact K ∧ ∀ v, π v = 1 → ∃ δ ∈ Δ, δ * v ∈ K) →
    IsFiniteMeasureOnCompacts ((μ.restrict D).map π) := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ D hD s π hs hπ hπs hK
  obtain ⟨K, hK, hKs⟩ := hK
  refine ⟨fun C hC => ?_⟩
  have hm : MeasurableSet (π ⁻¹' C) := hπ.measurable hC.measurableSet
  rw [Measure.map_apply hπ.measurable hC.measurableSet, Measure.restrict_apply hm]
  have hL : IsCompact ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hK.prod hC).image (by fun_prop)
  have hsub : π ⁻¹' C ∩ D ⊆ ⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := by
    rintro v ⟨hv, hvD⟩
    obtain ⟨δ, hδ, hδK⟩ := hKs (v * (s (π v))⁻¹) (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    refine Set.mem_iUnion.2 ⟨⟨δ, hδ⟩⁻¹, Set.mem_smul_set.2 ⟨δ * v, ⟨(δ * (v * (s (π v))⁻¹), π v), ⟨hδK, hv⟩, ?_⟩, ?_⟩, hvD⟩
    · simp [mul_assoc]
    · simp [Subgroup.smul_def]
  calc μ (π ⁻¹' C ∩ D) ≤ μ (⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D)) := measure_mono hsub
    _ ≤ ∑' g : Δ, μ (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := measure_iUnion_le _
    _ = μ ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := hL.measure_lt_top

theorem existsUnique_inter_preimage : ∀ (G G₁ : Type) [Group G] [Group G₁] (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) (s : N₁ →* N) (π : N →* N₁),
    (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ (A : Set N) (B : Set N₁), (∀ v : N, ∃! δ : (Γ ⊓ N').subgroupOf N, (δ : N) * v ∈ A) →
    (∀ u : N₁, ∃! γ : Γ₁.subgroupOf N₁, (γ : N₁) * u ∈ B) →
    ∀ v : N, ∃! γ : Γ.subgroupOf N, (γ : N) * v ∈ A ∩ π ⁻¹' B := by
  intro G G₁ _ _ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ A B hA hB v
  obtain ⟨γ₁, hγ₁, hγ₁u⟩ := hB (π v)
  obtain ⟨δ, hδ, hδu⟩ := hA (s γ₁ * v)
  have hδΓ : ((δ : N) : G) ∈ Γ := (Subgroup.mem_subgroupOf.1 δ.2).1
  have hδ1 : π δ = 1 := (hker _).2 (Subgroup.mem_subgroupOf.1 δ.2).2
  have hsγ : ((s γ₁ : N) : G) ∈ Γ := hsΓ _ (Subgroup.mem_subgroupOf.1 γ₁.2)
  refine ⟨⟨δ * s γ₁, Subgroup.mem_subgroupOf.2 (by simpa using mul_mem hδΓ hsγ)⟩, ⟨?_, ?_⟩, fun γ hγ => ?_⟩
  · simpa [mul_assoc] using hδ
  · change π (δ * s γ₁ * v) ∈ B
    rwa [map_mul, map_mul, hδ1, hπs, one_mul]
  · have hγΓ : (((γ : N)) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
    have hπγ : (⟨π γ, Subgroup.mem_subgroupOf.2 (hπΓ _ hγΓ)⟩ : Γ₁.subgroupOf N₁) = γ₁ :=
      hγ₁u _ (by simpa [map_mul] using hγ.2)
    have hπγ' : π γ = γ₁ := congrArg Subtype.val hπγ
    have hmem : (γ : N) * (s γ₁)⁻¹ ∈ (Γ ⊓ N').subgroupOf N := Subgroup.mem_subgroupOf.2
      ⟨by simpa using mul_mem hγΓ (inv_mem hsγ), (hker _).1 (by rw [map_mul, map_inv, hπs, hπγ', mul_inv_cancel])⟩
    have e : (⟨_, hmem⟩ : (Γ ⊓ N').subgroupOf N) = δ := hδu _ (by simpa [mul_assoc] using hγ.1)
    refine Subtype.ext ?_
    change (γ : N) = δ * s γ₁
    rw [← e]; simp

end GlobalTheory.Cusp.SemidirectConst

open GlobalTheory.Cusp.SemidirectConst


open GlobalTheory.AutomorphicL2Unitary in
theorem GlobalTheory.Cusp.constTermOn_eq_integral_semidirect : ∀ (G G₁ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) [DiscreteTopology Γ] [DiscreteTopology Γ₁] [LocallyCompactSpace N] [LocallyCompactSpace N₁],
    N' ≤ N → GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' → GlobalTheory.Cusp.Cocompact Γ₁ N₁ →
    ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ ψ : G → ℂ, Continuous ψ → (∀ a ∈ N', ∀ y, ψ (a * y) = ψ y) → (∀ γ ∈ Γ, γ ∈ N → ∀ y, ψ (γ * y) = ψ y) →
    ∀ (μ₁ : Measure N₁) (𝓕₁ : Set N₁), μ₁.IsHaarMeasure → IsFundamentalDomain (Γ₁.subgroupOf N₁) 𝓕₁ μ₁ → μ₁ 𝓕₁ = 1 →
    ∀ x : G, GlobalTheory.Cusp.constTermOn Γ N ψ x = ∫ u in 𝓕₁, ψ ((s u : G) * x) ∂μ₁ := by
  intro G G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ N N' Γ₁ N₁ _ _ _ _ hle hc hc' hc₁ s π hs hπ hπs hker hsΓ hπΓ ψ hψc hψN' hψΓ
    μ₁ 𝓕₁ hμ₁ h𝓕₁ h1 x
  haveI := hμ₁
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : DiscreteTopology (Γ ⊓ N' : Subgroup G) :=
    .of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Γ ⊓ N' ≤ Γ))
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Subgroup N, Δ = (Γ ⊓ N').subgroupOf N := ⟨_, rfl⟩
  subst hΔ
  have : Countable ((Γ ⊓ N').subgroupOf N) := Function.Injective.countable
    (f := fun δ : (Γ ⊓ N').subgroupOf N => (⟨δ.1.1, (Subgroup.mem_subgroupOf.1 δ.2).1⟩ : Γ))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))
  let μ : Measure N := Measure.haar
  have := hc.isMulRightInvariant μ
  have := hc₁.isMulRightInvariant μ₁
  have hD' := isFundamentalDomain_stdDom ((Γ ⊓ N').subgroupOf N) μ
  have hπΔ : ∀ δ ∈ (Γ ⊓ N').subgroupOf N, π δ = 1 := fun δ hδ => (hker δ).2 (Subgroup.mem_subgroupOf.1 hδ).2
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (stdDom ((Γ ⊓ N').subgroupOf N))).map π := ⟨_, rfl⟩
  have : ν.IsMulRightInvariant := hν ▸ map_restrict_isMulRightInvariant N N₁ _ μ _ hD' s π hπ hπs hπΔ
  have : IsFiniteMeasureOnCompacts ν := hν ▸ map_restrict_isFiniteMeasureOnCompacts N N₁ _ μ _ hD' s π hs hπ hπs (by
    obtain ⟨K, hK, hKs⟩ := hc'
    refine ⟨Subgroup.inclusion hle '' K, hK.image (continuous_subtype_val.subtype_mk _), fun v hv => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKs ⟨v, (hker v).1 hv⟩
    refine ⟨Subgroup.inclusion hle γ, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩, ⟨_, hγK, ?_⟩⟩
    exact Subtype.ext (by simp))
  obtain ⟨c, hνc⟩ : ∃ c : NNReal, ν = c • μ₁ := by
    obtain ⟨a, e1⟩ : ∃ a : NNReal, ν.inv = a • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul ν.inv μ₁⟩
    obtain ⟨b, e2⟩ : ∃ b : NNReal, μ₁.inv = b • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ₁.inv μ₁⟩
    refine ⟨a * b, ?_⟩
    rw [← Measure.inv_inv ν, e1, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, e2, smul_smul]
    exact measurable_inv.aemeasurable
  have hD₁ := isFundamentalDomain_stdDom (Γ₁.subgroupOf N₁) μ₁
  have hmD₁ := measurableSet_stdDom (Γ₁.subgroupOf N₁)
  have hm𝓕 : MeasurableSet (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) :=
    (measurableSet_stdDom _).inter (hπ.measurable hmD₁)
  have h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) μ :=
    .mk' hm𝓕.nullMeasurableSet (existsUnique_inter_preimage G G₁ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ _ _ (existsUnique_stdDom _) (existsUnique_stdDom _))
  have hg : ∀ v : N, ψ (v * x) = ψ (s (π v) * x) := fun v => by
    have hm : ((v * (s (π v))⁻¹ : N) : G) ∈ N' := (hker _).1 (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    have := hψN' _ hm ((s (π v) : G) * x)
    rw [← this, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  have hgc : Continuous fun u : N₁ => ψ (s u * x) := by fun_prop
  have hint : ∫ v in stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁), ψ (v * x) ∂μ =
      ∫ u in stdDom (Γ₁.subgroupOf N₁), ψ (s u * x) ∂ν := by
    rw [hν, setIntegral_map hmD₁ hgc.aestronglyMeasurable hπ.aemeasurable, Measure.restrict_restrict (hπ.measurable hmD₁),
      Set.inter_comm (π ⁻¹' _)]
    exact integral_congr_ae (.of_forall hg)
  have hmeas : μ (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) = ν (stdDom (Γ₁.subgroupOf N₁)) := by
    rw [hν, Measure.map_apply hπ.measurable hmD₁, Measure.restrict_apply (hπ.measurable hmD₁), Set.inter_comm]
  have hinv1 : ∀ (γ : Γ₁.subgroupOf N₁) (u : N₁), ψ (s (γ • u) * x) = ψ (s u * x) := fun γ u => by
    rw [Subgroup.smul_def, smul_eq_mul, map_mul]
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hψΓ _ (hsΓ _ (Subgroup.mem_subgroupOf.1 γ.2)) (s γ).2 _
  have hDe : μ₁ (stdDom (Γ₁.subgroupOf N₁)) = 1 := (hD₁.measure_eq h𝓕₁).trans h1
  rw [GlobalTheory.Cusp.Stages.constTermOn_eq' h𝓕 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψΓ _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _),
    hint, measureReal_def, hmeas, hνc, Measure.smul_apply, hDe, Measure.restrict_smul, integral_smul_nnreal_measure,
    hD₁.setIntegral_eq h𝓕₁ hinv1]
  have hc0 : c ≠ 0 := by
    have := h𝓕.measure_ne_zero (NeZero.ne μ)
    rw [hmeas, hνc, Measure.smul_apply, hDe] at this
    rintro rfl; simp at this
  first
  | (rw [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal, NNReal.smul_def, smul_smul,
      inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc0), one_smul]; done)
  | (simp [hc0, NNReal.smul_def, smul_smul]; done)
  | (field_simp; done)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanish

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

theorem isIsoFrame_initCols {D : D7} {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (k : Fin m) : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := by
  have hf := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hli := GlobalTheory.CompanionTheory.UnipCocompact.linearIndependent_of_isWittFrame (GlobalTheory.SiegelSet.sigma_sigma hf.1) (hf.2 V) hW
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · exact hli.comp (Fin.castLE k.2) (Fin.castLE_injective k.2)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE k.2 a)) (Fin.castLE k.2 b)
    simpa [GlobalTheory.StdPar.initCols, Matrix.mul_apply, Formalism.UG.cT] using this

theorem isCuspFun_of_isConstAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  intro D V m X Y hW hmax f hl hc
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f := hl
  refine (GlobalTheory.Cusp.isCuspFun_iff hl').2 fun W hW' => ?_
  obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V W).1 hW'
  have hrm := hmax r C hC
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hC.1; omega⟩
  let k : Fin m := ⟨r', by omega⟩
  have hC0 : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := isIsoFrame_initCols hW k
  have hcc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := by
    rw [GlobalTheory.Cusp.NA_frameFlag hC0]
    exact (GlobalTheory.CuspDecay.Model.isClosed_NI V hC0).locallyCompactSpace
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram (GlobalTheory.StdPar.initCols X k) :=
    GlobalTheory.Cusp.NA_frameFlag hC0
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f 0 := by
    rw [e]
    exact GlobalTheory.UAut.isConstTerm_iff.1 ((GlobalTheory.StdPar.isConstAlong_singleton hW k).1 (hc k))
  have h2 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hl' g, MeasureTheory.Measure.real, b3]
    simp
  have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f = 0 := h2.unique hcc h1
  exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V (r' + 1) _ C hC0 hC f hl h0

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanishStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet


theorem _root_.GlobalTheory.T.cusp_function_of_constant_terms_vanish : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCuspFunSlice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

theorem unip_split : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      ∀ p ∈ unip D.sp.cm.sig V.gram X T, ∃ u ∈ unip D.sp.cm.sig V.gram X S, ∃ l ∈ levi D.sp.cm.sig V.gram X Y S, p = u * l := by
  intro D V m X Y hW S T hST p hpT
  obtain ⟨hcm, hherm⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hherm V
  by_cases hS : S = ∅
  · subst hS
    exact ⟨1, one_mem _, p, by simp, by simp⟩
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ S, ∀ k ∈ S, k ≤ a := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hP := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T S a hST ha ha' hpT
  have hdec := (GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hcm _ V.gram hJ (a.val + 1) (initCols X a) (initCols Y a)
    (fun i => (S.filter fun k => k.val < i.val).card)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [initCols, initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]
        exact Matrix.submatrix_one _ (Fin.castLE_injective a.2))).1
  obtain ⟨u, hu, l, hl, rfl, -⟩ := hdec p hP
  have hflag := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW S (a.val + 1) a.2
    (fun i => ⟨fun h => ⟨a, ha, Nat.lt_succ_iff.1 h⟩, fun ⟨k, hk, hik⟩ =>
      Nat.lt_succ_iff.2 (le_trans hik (ha' k hk))⟩)
    (fun i => (S.filter fun k => k.val < i.val).card) (fun i => rfl)
  exact ⟨u, hflag.1 ▸ hu, l, hflag.2.1 ▸ hl, rfl⟩

theorem isCuspFun_slice : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → IsCuspFun V' fun h => ψ (s h * y) := by
  intro D θ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs ψ hψ y hy hyc
  obtain ⟨hcm, hJall⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJall V
  have hJ' := hJall V'
  obtain ⟨s₀, hs₀c, hs₀, hs₀Q⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have es : ∀ h, s h = s₀ h := fun h => (hs₀ h (s h)).1 (hs h)
  have hsc : Continuous s := by
    have : (s : GA D V' → GA D V) = s₀ := funext es
    rw [this]; exact hs₀c
  have hsQ : ∀ γ ∈ GQ V', s γ ∈ GQ V := fun γ hγ => es γ ▸ hs₀Q γ hγ
  obtain ⟨hup, hsurj, -⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hW T V' ι hι hr s hs
  have hψl : ∀ γ ∈ leftSub V X Y T, ∀ g, ψ (γ * g) = ψ g := hψ.1.1.left
  have hψc : Continuous ψ := hψ.1.1.cont
  have hfl : ∀ γ ∈ GQ V', ∀ g, (fun h => ψ (s h * y)) (γ * g) = (fun h => ψ (s h * y)) g := fun γ hγ g => by
    have h1 : s γ ∈ leftSub V X Y T := Subgroup.mem_sup_right ⟨hsQ γ hγ,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hup γ)⟩
    change ψ (s (γ * g) * y) = ψ (s g * y)
    rw [map_mul, mul_assoc, hψl _ h1]
  obtain ⟨m', e, X', Y', hsl, hW'⟩ := GlobalTheory.T.orthogonal_subspace_witt_frame_extension D V m X Y hW T V' ι hι hr
  refine GlobalTheory.T.cusp_function_of_constant_terms_vanish D V' m' X' Y' hW' (GlobalTheory.T.isotropic_frame_rank_le_witt_index D V' m' X' Y' hW') _ hfl fun k => ?_
  have hκ : e k ∉ upTo T := (hsl.2.1 _).2 ⟨k, rfl⟩
  have hκT : e k ∉ T := fun h => hκ ⟨_, h, le_rfl⟩
  have hTT' : T ⊂ insert (e k) T := Finset.ssubset_insert hκT
  have hψ0 := hψ.2 _ hTT'
  haveI := locallyCompact_unip hcm hJ' hW' {k}
  haveI := locallyCompact_unip hcm hJ hW (insert (e k) T)
  have hle := GlobalTheory.StdPar.unip_mono_of_subset _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW (insert (e k) T) T hTT'.1
  have hs1 := GlobalTheory.T.restricted_cusp_constant_term_vanish D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdown := GlobalTheory.T.restricted_constant_term_compatible D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdec : ∀ v ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∃ u ∈ unip D.sp.cm.sig V'.gram X' {k},
      v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun v hv => by
    obtain ⟨u, hu, l, hl, rfl⟩ := unip_split D V m X Y hW T _ hTT'.1 v hv
    have hl' : l ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
      simpa using mul_mem (inv_mem (hle hu)) hv
    obtain ⟨b, rfl⟩ := hsurj l (GlobalTheory.T.levi_inf_unipotent_le_hermitian_part D V m X Y hW T _ hκ ⟨hl, hl'⟩)
    exact ⟨b, hdown b hl', by simpa using hu⟩
  have hnorm : ∀ p ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∀ a ∈ unip D.sp.cm.sig V.gram X T,
      p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun p hp a ha =>
    conj_mem_unip_of_subset hcm hJ hW hTT'.1 hp ha
  obtain ⟨π, hπc, hπ, hπQ⟩ := GlobalTheory.T.restricted_automorphic_invariance D V m X Y hW T V' ι hι hr s hs _ _ hnorm hdec
  let s₁ : unip D.sp.cm.sig V'.gram X' {k} →* unip D.sp.cm.sig V.gram X (insert (e k) T) :=
    (s.comp (unip D.sp.cm.sig V'.gram X' {k}).subtype).codRestrict _ fun u => hs1 _ u.2
  have hs₁c : Continuous s₁ := (hsc.comp continuous_subtype_val).subtype_mk _
  have hπs : ∀ u, π (s₁ u) = u := fun u => (hπ _ _).2 (by
    change s u * (s u)⁻¹ ∈ _
    simp [one_mem])
  have hker : ∀ v, π v = 1 ↔ (v : GA D V) ∈ unip D.sp.cm.sig V.gram X T := fun v => by
    rw [hπ v 1]
    simp
  intro μ 𝓕 hμ h𝓕 h1 g
  have cN : GlobalTheory.Cusp.Cocompact (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) := cocompact_unip_std hcm hJ hW _
  have key := GlobalTheory.Cusp.constTermOn_eq_integral_semidirect (GA D V) (GA D V') (GQ V) _ _ (GQ V') _ hle cN
    (cocompact_unip_std hcm hJ hW T) (cocompact_unip_std hcm hJ' hW' {k}) s₁ π hs₁c hπc hπs hker
    (fun u hu => hsQ _ hu) (fun v hv => hπQ v hv) ψ hψc
    (fun a ha y => hψl a (Subgroup.mem_sup_left ha) y)
    (fun γ hγ hγ' y => hψl γ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, hγ'⟩) y) μ 𝓕 hμ h𝓕 h1 (s g * y)
  obtain ⟨μ₀, 𝓕₀, a1, a2, a3⟩ := exists_mass_one cN
  have hz := hψ0 μ₀ 𝓕₀ a1 a2 a3 (s g * y)
  have hct : GlobalTheory.Cusp.constTermOn (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) ψ (s g * y) = 0 := by
    haveI := a1
    have e1 := GlobalTheory.Cusp.Stages.constTermOn_eq' (Γ := GQ V) (φ := ψ) (x := s g * y) a2 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψl _ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, (γ : unip _ _ _ _).2⟩) _)
    rw [e1, ← hz]
    simp
  rw [hct] at key
  refine key.trans (MeasureTheory.integral_congr_ae (.of_forall fun u => ?_))
  change ψ (s u * (s g * y)) = ψ (s (u * g) * y)
  rw [map_mul, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end
end
