module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
public import Mathlib.MeasureTheory.Measure.Prod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMapMulRightEqSmul
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolicStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstantStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMeasureModulus

section

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.ParabModulus

section General

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

noncomputable def prodMul (μM μN : Measure G) : Measure G := (μM.prod μN).map (fun z => z.1 * z.2)

theorem lintegral_prodMul (μM μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂prodMul μM μN = ∫⁻ m, ∫⁻ u, f (m * u) ∂μN ∂μM := by
  rw [prodMul, lintegral_map hf measurable_mul]
  exact lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable

theorem measurable_inner (μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    Measurable fun m => ∫⁻ u, f (m * u) ∂μN :=
  Measurable.lintegral_prod_right' (f := fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul)

theorem prodMul_left_fst (M : Subgroup G) (μM μN : Measure G) [SFinite μN]
    (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM) (s : G) (hs : s ∈ M) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iM s hs) _ (measurable_inner μN f hf)
  simpa only [mul_assoc] using this

theorem prodMul_left_snd (M N : Subgroup G) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m⁻¹ * u * m ∈ N)
    (μM μN : Measure G) [SFinite μN] (h1 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (s : G) (hs : s ∈ N) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  refine lintegral_congr_ae (aM.mono fun m hm => ?_)
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iN _ (hnorm m hm s hs)) (fun u => f (m * u))
    (hf.comp (measurable_const_mul m))
  show ∫⁻ u, f (s * (m * u)) ∂μN = ∫⁻ u, f (m * u) ∂μN
  rw [← this]
  refine lintegral_congr fun u => ?_
  rw [show m * (m⁻¹ * s * m * u) = s * (m * u) by group]

theorem prodMul_facts (M N P : Subgroup G) (hM : IsClosed (M : Set G)) (hN : IsClosed (N : Set G))
    (hPm : MeasurableSet (P : Set G)) (hMN : ∀ m ∈ M, m ∈ N → m = 1)
    (hMP : ∀ m ∈ M, ∀ u ∈ N, m * u ∈ P) (hdec : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ N, p = m * u)
    (μM μN : Measure G) [SigmaFinite μN] [IsFiniteMeasureOnCompacts μM] [IsFiniteMeasureOnCompacts μN]
    (hM0 : μM ≠ 0) (hN0 : μN ≠ 0) (h1 : μM (M : Set G)ᶜ = 0) (h2 : μN (N : Set G)ᶜ = 0) :
    prodMul μM μN (P : Set G)ᶜ = 0 ∧ SigmaFinite (prodMul μM μN) ∧
      ∃ T : Set G, MeasurableSet T ∧ prodMul μM μN T ≠ 0 ∧ prodMul μM μN T ≠ ⊤ := by
  set ρ₀ := prodMul μM μN with hρ₀
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h2
  have hP0 : ρ₀ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ₀, lintegral_prodMul _ _ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    rw [Set.indicator_of_notMem (show m * u ∉ (P : Set G)ᶜ from fun h => h (hMP m hm u hu))]
    simp
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ M) * (compactCovering G i ∩ N) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hM).mul ((isCompact_compactCovering G i).inter_right hN)
  have uniq : ∀ i, ∀ m ∈ M, ∀ u ∈ N, m * u ∈ Q i → m ∈ compactCovering G i ∧ u ∈ compactCovering G i := by
    rintro i m hm u hu ⟨m', ⟨hm'C, hm'M⟩, u', ⟨hu'C, hu'N⟩, e⟩
    have e : m' * u' = m * u := e
    have e' : m'⁻¹ * m = u' * u⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * u) * u⁻¹ := by group
        _ = m'⁻¹ * (m' * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group
    have h := hMN _ (M.mul_mem (M.inv_mem hm'M) hm) (by rw [e']; exact N.mul_mem hu'N (N.inv_mem hu))
    have hm' : m = m' := (inv_mul_eq_one.1 h).symm
    rw [h] at e'
    have hu' : u = u' := (mul_inv_eq_one.1 e'.symm).symm
    exact ⟨hm' ▸ hm'C, hu' ▸ hu'C⟩
  have hQ1 : ∀ i, ρ₀ (Q i) < ⊤ := by
    intro i
    have hC := isCompact_compactCovering G i
    rw [← lintegral_indicator_one (hQc i).measurableSet, hρ₀,
      lintegral_prodMul _ _ _ (measurable_one.indicator (hQc i).measurableSet)]
    calc _ ≤ ∫⁻ m, (compactCovering G i).indicator (fun _ => μN (compactCovering G i)) m ∂μM := by
          refine lintegral_mono_ae ?_
          filter_upwards [aM] with m hm
          by_cases hmC : m ∈ compactCovering G i
          · rw [Set.indicator_of_mem hmC, ← lintegral_indicator_one hC.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aN] with u hu
            by_cases hq : m * u ∈ Q i
            · simp [Set.indicator_of_mem hq, Set.indicator_of_mem (uniq i m hm u hu hq).2]
            · simp [Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem hmC]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aN] with u hu
            rw [Set.indicator_of_notMem (fun h => hmC (uniq i m hm u hu h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hC.measurableSet]
          exact ENNReal.mul_lt_top hC.measure_lt_top hC.measure_lt_top
  have hS : ⋃ i, (Q i ∪ (P : Set G)ᶜ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    by_cases hg : g ∈ P
    · obtain ⟨m, hm, u, hu, rfl⟩ := hdec g hg
      obtain ⟨i, hi⟩ := exists_mem_compactCovering m
      obtain ⟨k, hk⟩ := exists_mem_compactCovering u
      exact ⟨max i k, Or.inl (Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hm⟩
        ⟨compactCovering_subset G (le_max_right _ _) hk, hu⟩)⟩
    · exact ⟨0, Or.inr hg⟩
  have hS1 : ∀ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_union_le _ _) (by rw [hP0, add_zero]; exact hQ1 i)
  have sf : SigmaFinite ρ₀ := ⟨⟨⟨fun i => Q i ∪ (P : Set G)ᶜ, fun _ => trivial, hS1, hS⟩⟩⟩
  have huniv : ρ₀ Set.univ ≠ 0 := by
    rw [hρ₀, prodMul, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (fun h => hM0 (Measure.measure_univ_eq_zero.1 h))
      (fun h => hN0 (Measure.measure_univ_eq_zero.1 h))
  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact huniv (by rw [← hS]; exact measure_iUnion_null h)
  refine ⟨hP0, sf, Q i, (hQc i).measurableSet, fun h => hi ?_, (hQ1 i).ne⟩
  exact measure_union_null h hP0

theorem eq_smul_of_left_inv (P : Subgroup G) (hPm : MeasurableSet (P : Set G)) (ρ ρ₀ : Measure G)
    [SigmaFinite ρ] [SigmaFinite ρ₀] (h0 : ρ (P : Set G)ᶜ = 0) (h0' : ρ₀ (P : Set G)ᶜ = 0)
    (hi : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ) (hi' : ∀ s ∈ P, ρ₀.map (fun g => s * g) = ρ₀)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ₀ T ≠ 0) (hT1 : ρ₀ T ≠ ⊤) :
    ∃ c : ENNReal, ρ = c • ρ₀ := by
  have hemb : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hPm
  haveI : MeasurableMul₂ P := ⟨Measurable.subtype_mk
    ((hemb.measurable.comp measurable_fst).mul (hemb.measurable.comp measurable_snd))⟩
  haveI : MeasurableInv P := ⟨Measurable.subtype_mk hemb.measurable.inv⟩
  have hmap : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (τ.comap Subtype.val).map (Subtype.val : P → G) = τ := by
    intro τ h
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem h
  have hinv : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (∀ s ∈ P, τ.map (fun g => s * g) = τ) →
      (τ.comap (Subtype.val : P → G)).IsMulLeftInvariant := by
    intro τ h hτ
    refine ⟨fun s => ?_⟩
    rw [← hemb.comap_map ((τ.comap Subtype.val).map (fun g => s * g)),
      Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : P → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap τ h, hτ s s.2]
  haveI := hinv ρ h0 hi
  haveI := hinv ρ₀ h0' hi'
  haveI : SigmaFinite (ρ.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ h0]; infer_instance)
  haveI : SigmaFinite (ρ₀.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ₀ h0']; infer_instance)
  have hT' : ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) = ρ₀ T := by
    rw [← hmap ρ₀ h0', Measure.map_apply hemb.measurable hT, hmap ρ₀ h0']
  set c : ENNReal := ρ.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) /
    ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) with hc
  have key : ρ.comap (Subtype.val : P → G) = c • ρ₀.comap (Subtype.val : P → G) :=
    measure_eq_div_smul (ρ.comap (Subtype.val : P → G)) (ρ₀.comap (Subtype.val : P → G))
      (s := Subtype.val ⁻¹' T) (by rw [hT']; exact hT0) (by rw [hT']; exact hT1)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← hmap ρ h0, key]
  rw [Measure.map_smul, hmap ρ₀ h0']
  exact hemb.measurable.aemeasurable

end General

end GlobalTheory.ParabModulus
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultiple

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FubNM

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_prodMul_eq (M : Set G) (μM μN : Measure G) [SFinite μM] [SFinite μN] (hM : μM Mᶜ = 0)
    (δ : G → ℝ≥0∞) (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN)
    (C : Set G) (hCm : MeasurableSet C) (hC0 : μN C ≠ 0) (hC1 : μN C ≠ ⊤)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(GlobalTheory.ParabModulus.prodMul μM μN) = ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN := by
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 hM
  have cm : ∀ m : G, Measurable fun u : G => m * u * m⁻¹ := fun m => (measurable_const_mul m).mul_const _
  set δ' : G → ℝ≥0∞ := fun m => μN ((fun u => m * u * m⁻¹) ⁻¹' C) / μN C with hδ'
  have hm' : Measurable δ' := by
    refine Measurable.div_const ?_ _
    exact measurable_measure_prodMk_left (s := (fun z : G × G => z.1 * z.2 * z.1⁻¹) ⁻¹' C)
      ((measurable_mul.mul measurable_fst.inv) hCm)
  have he : ∀ m ∈ M, δ' m = δ m := by
    intro m hm
    simp only [hδ']
    rw [← Measure.map_apply (cm m) hCm, hmod m hm, Measure.smul_apply, smul_eq_mul, mul_div_assoc,
      ENNReal.div_self hC0 hC1, mul_one]
  have hFm : Measurable fun z : G × G => δ' z.1 * F (z.2 * z.1) :=
    (hm'.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))
  rw [GlobalTheory.ParabModulus.lintegral_prodMul _ _ _ hF]
  have step : ∀ᵐ m ∂μM, ∫⁻ u, F (m * u) ∂μN = ∫⁻ u, δ' m * F (u * m) ∂μN := by
    filter_upwards [aM] with m hm
    have h := lintegral_map (μ := μN) (hF.comp (measurable_mul_const m)) (cm m)
    rw [hmod m hm, lintegral_smul_measure, smul_eq_mul] at h
    have h2 : ∫⁻ u, δ' m * F (u * m) ∂μN = δ' m * ∫⁻ u, F (u * m) ∂μN :=
      lintegral_const_mul _ (hF.comp (measurable_mul_const m))
    rw [h2, he m hm]
    simp only [Function.comp_apply, inv_mul_cancel_right] at h
    exact h.symm
  rw [lintegral_congr_ae step,
    lintegral_lintegral_swap (f := fun m u => δ' m * F (u * m)) hFm.aemeasurable]
  refine lintegral_congr fun u => lintegral_congr_ae ?_
  filter_upwards [aM] with m hm
  rw [he m hm]

end General

variable {n : ℕ} {ε : Fin n → Bool}

theorem muPar_facts (A : Matrix (Fin n) (Fin n) ℂ) (ν : Measure (PSub ε A)) [ν.IsHaarMeasure] :
    SigmaFinite (muPar ε A ν) ∧ muPar ε A ν (PSub ε A : Set (S7.UJ ε))ᶜ = 0 ∧
      (∀ s ∈ PSub ε A, (muPar ε A ν).map (fun g => s * g) = muPar ε A ν) ∧ muPar ε A ν ≠ 0 := by
  have hcl := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
  have hv : Measurable (Subtype.val : PSub ε A → S7.UJ ε) := measurable_subtype_coe
  have hσ : SigmaFinite (muPar ε A ν) :=
    (MeasurableEmbedding.subtype_coe hcl.measurableSet).sigmaFinite_map (μ := ν)
  refine ⟨hσ, ?_, ?_, ?_⟩
  · rw [muPar, Measure.map_apply hv hcl.measurableSet.compl]
    have : (Subtype.val : PSub ε A → S7.UJ ε) ⁻¹' (PSub ε A : Set (S7.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [this, measure_empty]
  · intro s hs
    have e : (fun g : S7.UJ ε => s * g) ∘ (Subtype.val : PSub ε A → S7.UJ ε) =
        Subtype.val ∘ (fun g : PSub ε A => (⟨s, hs⟩ : PSub ε A) * g) := rfl
    rw [muPar, Measure.map_map (measurable_const_mul s) hv, e,
      ← Measure.map_map hv (measurable_const_mul _), map_mul_left_eq_self]
  · exact (Measure.map_ne_zero_iff (μ := ν) hv.aemeasurable).2
      (fun h => isOpen_univ.measure_ne_zero ν Set.univ_nonempty (by simp [h]))

theorem fub2 : Fub2 := by
  intro n ε A hA
  have hW : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := GlobalTheory.CompanionTheory.PSubFlag.isoFlag hA
  have hj : ∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => rk A) i := fun _ => (GlobalTheory.CompanionTheory.GradFlag.flagFacts n ε A hA).1
  obtain ⟨⟨μN, sN, hN⟩, ⟨μM, sM, hM⟩, μK, hK0, hK1, hKi⟩ := GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic n ε 1 _ (W A) hj hW
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε 1 _ (W A) hj hW μN hN
  refine ⟨μN, μM, inferInstance, inferInstance, hM.1, ?_, ?_, ?_⟩
  · intro a ha hc
    have e : μM.map (· * a) = μM.map (a * ·) :=
      Measure.map_congr (Filter.Eventually.mono (mem_ae_iff.2 hM.1 : ∀ᵐ m ∂μM, m ∈ flagM ε (W A)) fun m hm => hc m hm)
    rw [e]
    exact hM.2.1 a ha
  · obtain ⟨κ, k0, k1, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε _ _ rfl rfl 1 _ hj (W A) hW μN μM μK hN hM hK0 hK1 hKi
    refine ⟨κ, k0, k1, fun F hF hinv => ?_⟩
    rw [hκ F hF]
    congr 1
    refine lintegral_congr fun u => lintegral_congr fun m => ?_
    have aK : ∀ᵐ k ∂μK, k ∈ maxK ε := mem_ae_iff.2 hK0
    have e : ∫⁻ k, F (u * m * k) ∂μK = F (u * m) := by
      rw [lintegral_congr_ae (g := fun _ => F (u * m)) (aK.mono fun k hk => hinv _ k (by
        rw [← SetLike.mem_coe, GlobalTheory.IwasawaShape.coe_KG]; exact hk))]
      simp [lintegral_const, hK1]
    rw [e]
    rfl
  · intro ν hν
    obtain ⟨⟨N, eN⟩, cN, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε 1 _ (W A) hW
    obtain ⟨⟨M, eM⟩, cM, -, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
    have huniq := (GlobalTheory.RealIwasawa.iwasawa n ε 1 _ (W A) hW).2
    have mN : ∀ v, v ∈ N ↔ v ∈ flagN ε (W A) := fun v => by rw [← SetLike.mem_coe, eN]
    have mM : ∀ v, v ∈ M ↔ v ∈ flagM ε (W A) := fun v => by rw [← SetLike.mem_coe, eM]
    have cN' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := eN ▸ cN
    have cM' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := eM ▸ cM
    have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) _ μN := eN ▸ hN
    have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) _ μM := eM ▸ hM
    obtain ⟨hN0, iN⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite N _ μN cN' hN'
    obtain ⟨hM0, iM⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite M _ μM cM' hM'
    haveI := iN
    haveI := iM
    let P : Subgroup (Formalism.REAL.UJ ε) := PSub ε A
    have hcl : IsClosed (P : Set (Formalism.REAL.UJ ε)) := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
    have hPeq : ∀ g : Formalism.REAL.UJ ε, g ∈ P ↔ ∃ u ∈ flagN ε (W A), ∃ m ∈ flagM ε (W A), g = u * m :=
      GlobalTheory.CompanionTheory.PSubFlag.psubEq n ε A hA
    have hnorm1 : ∀ m ∈ M, ∀ v ∈ N, m * v * m⁻¹ ∈ N := fun m hm v hv =>
      (mN _).2 (hnorm m ((mM m).1 hm) v ((mN v).1 hv))
    have hnorm' : ∀ l ∈ M, ∀ v ∈ N, l⁻¹ * v * l ∈ N := fun l hl v hv => by
      simpa using hnorm1 l⁻¹ (M.inv_mem hl) v hv
    have hMN : ∀ l ∈ M, l ∈ N → l = 1 := fun l hl hlN =>
      huniq l ((mN l).1 hlN) l⁻¹ ((mM _).1 (M.inv_mem hl)) (by
        rw [mul_inv_cancel, ← GlobalTheory.IwasawaShape.coe_KG]; exact (Formalism.REAL.KG ε).one_mem)
    have hMP : ∀ l ∈ M, ∀ v ∈ N, l * v ∈ P := fun l hl v hv =>
      (hPeq _).2 ⟨l * v * l⁻¹, (mN _).1 (hnorm1 l hl v hv), l, (mM l).1 hl, by group⟩
    have hdec : ∀ p ∈ P, ∃ l ∈ M, ∃ v ∈ N, p = l * v := by
      intro p hp
      obtain ⟨u, hu, m, hm, rfl⟩ := (hPeq p).1 hp
      exact ⟨m, (mM m).2 hm, m⁻¹ * u * m, hnorm' m ((mM m).2 hm) u ((mN u).2 hu), by group⟩
    obtain ⟨hP0, sf, T, hTm, hT0, hT1⟩ := GlobalTheory.ParabModulus.prodMul_facts M N P cM' cN' hcl.measurableSet hMN hMP hdec
      μM μN hM0 hN0 hM'.1 hN'.1
    haveI := sf
    have lP : ∀ s ∈ P, (GlobalTheory.ParabModulus.prodMul μM μN).map (fun g => s * g) = GlobalTheory.ParabModulus.prodMul μM μN := by
      intro s hs
      obtain ⟨l, hl, v, hv, rfl⟩ := hdec s hs
      have : (fun g => l * v * g) = (fun g => l * g) ∘ (fun g => v * g) := by
        funext g; simp [mul_assoc]
      rw [this, ← Measure.map_map (measurable_const_mul l) (measurable_const_mul v),
        GlobalTheory.ParabModulus.prodMul_left_snd M N hnorm' μM μN hM'.1 hN'.2.1 v hv,
        GlobalTheory.ParabModulus.prodMul_left_fst M μM μN hM'.2.1 l hl]
    have key : ∀ ρ : Measure (Formalism.REAL.UJ ε), SigmaFinite ρ → ρ (P : Set (Formalism.REAL.UJ ε))ᶜ = 0 →
        (∀ s ∈ P, ρ.map (fun g => s * g) = ρ) → ρ ≠ 0 → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
            ∫⁻ x, F x ∂ρ = c * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN := by
      intro ρ sρ hρ0 hρi hρne
      haveI := sρ
      obtain ⟨c, hc⟩ := GlobalTheory.ParabModulus.eq_smul_of_left_inv P hcl.measurableSet (ρ)
        (GlobalTheory.ParabModulus.prodMul μM μN) hρ0 hP0 hρi lP T hTm hT0 hT1
      have c0 : c ≠ 0 := by
        rintro rfl
        exact hρne (by rw [hc, zero_smul])
      have c1 : c ≠ ⊤ := by
        rintro rfl
        have hS := iUnion_spanningSets (ρ)
        have hz : ∀ i, GlobalTheory.ParabModulus.prodMul μM μN (T ∩ spanningSets (ρ) i) = 0 := by
          intro i
          by_contra h
          have h1 : ρ (T ∩ spanningSets (ρ) i) = ⊤ := by
            generalize T ∩ spanningSets ρ i = X at h ⊢
            rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul h]
          have h2 : ρ (T ∩ spanningSets ρ i) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right)
            (measure_spanningSets_lt_top (ρ) i)
          rw [h1] at h2
          exact lt_irrefl _ h2
        refine hT0 (measure_mono_null (t := ⋃ i, T ∩ spanningSets (ρ) i) ?_ (measure_iUnion_null hz))
        rw [← Set.inter_iUnion, hS, Set.inter_univ]
      obtain ⟨i, hi⟩ : ∃ i, μN (compactCovering (Formalism.REAL.UJ ε) i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hN0 (Measure.measure_univ_eq_zero.1 (by
          rw [← iUnion_compactCovering]; exact measure_iUnion_null h))
      have hC := isCompact_compactCovering (Formalism.REAL.UJ ε) i
      refine ⟨c, c0, c1, fun F hF => ?_⟩
      rw [hc, lintegral_smul_measure, smul_eq_mul,
        lintegral_prodMul_eq (flagM ε (W A)) μM μN hM.1 (modA A) hmod _ hC.measurableSet hi hC.measure_lt_top.ne F hF]
    obtain ⟨sρ, hρ0, hρi, hρne⟩ := muPar_facts (ε := ε) A ν
    exact key (muPar ε A ν) sρ hρ0 hρi hρne

end GlobalTheory.CompanionTheory.FubNM
end
end
end
