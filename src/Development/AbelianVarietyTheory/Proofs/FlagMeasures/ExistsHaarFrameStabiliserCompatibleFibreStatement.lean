module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulLocalWittFreeTupleGramStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.ProperAction.Basic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFiniteStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  first | exact @GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | exact GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | (intros; apply GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFactsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.localUnitaryGroup_tuples_topological_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  first | exact @GlobalTheory.LocalUnitaryTop.top_facts | exact GlobalTheory.LocalUnitaryTop.top_facts | (intros; apply GlobalTheory.LocalUnitaryTop.top_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbit

section

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.WeilOrbit

theorem measurableEmbedding_of_sigmaCompact {Y X : Type} [TopologicalSpace Y] [T2Space Y]
    [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {φ : Y → X} (hc : Continuous φ)
    (hi : Function.Injective φ) : MeasurableEmbedding φ := by
  refine ⟨hi, hc.measurable, fun s hs => ?_⟩
  have h : φ '' s = ⋃ n, (fun y : compactCovering Y n => φ y) '' (Subtype.val ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, ⟨y, hn⟩, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  refine MeasurableSet.iUnion fun n => ?_
  haveI : CompactSpace (compactCovering Y n) :=
    isCompact_iff_compactSpace.mp (isCompact_compactCovering Y n)
  have hce : Topology.IsClosedEmbedding (fun y : compactCovering Y n => φ y) :=
    (hc.comp continuous_subtype_val).isClosedEmbedding (hi.comp Subtype.val_injective)
  exact hce.measurableEmbedding.measurableSet_image.mpr (measurable_subtype_coe hs)

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) {C : Set (G ⧸ H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K := by
  refine hC.induction_on (p := fun C => ∃ K : Set G, IsCompact K ∧
    C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK, h⟩
    exact ⟨K, hK, hst.trans h⟩
  · rintro s t ⟨K, hK, h⟩ ⟨L, hL, h'⟩
    exact ⟨K ∪ L, hK.union hL, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg),
        K, hK, subset_rfl⟩

def orbitMap (G : Type) {X : Type} [Group G] [MulAction G X] (x0 : X) :
    G ⧸ MulAction.stabilizer G x0 → X :=
  MulAction.ofQuotientStabilizer G x0

theorem orbitMap_mk {G X : Type} [Group G] [MulAction G X] (x0 : X) (g : G) :
    orbitMap G x0 (g : G ⧸ MulAction.stabilizer G x0) = g • x0 := rfl

theorem orbitMap_injective {G X : Type} [Group G] [MulAction G X] (x0 : X) :
    Function.Injective (orbitMap G x0) :=
  MulAction.injective_ofQuotientStabilizer G x0

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ x0 hcont μ hμ ν hν0 hinv hfin hne
  set H := MulAction.stabilizer G x0 with hHdef
  have hc0 : Continuous (fun g : G => g • x0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hH : IsClosed (H : Set G) := isClosed_eq hc0 continuous_const
  haveI := hH
  letI : MeasurableSpace (G ⧸ H) := borel _
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (G ⧸ H) := inferInstance
  let φ : G ⧸ H → X := orbitMap G x0
  have hφc : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr hc0
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_of_sigmaCompact hφc (orbitMap_injective x0)
  have hrange : Set.range φ = {y | ∃ g : G, g • x0 = y} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ H), rfl⟩
  have hae : ∀ᵐ y ∂ν, y ∈ Set.range φ := by
    rw [hrange]
    exact hν0
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hφ.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have hrad : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H (ν.comap φ) := by
    refine ⟨fun h0 => hne ?_, ⟨fun C hC => ?_⟩, ⟨fun g s hs => ?_⟩⟩
    · rw [← hmap, h0, Measure.map_zero]
    · obtain ⟨K, hK, hCK⟩ := exists_compact_cover H hC
      rw [hφ.comap_apply]
      refine (measure_mono ?_).trans_lt (hfin K hK)
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hCK hq
      exact ⟨g, hg, rfl⟩
    · rw [hφ.comap_apply, hφ.comap_apply, ← hinv g (φ '' s) (hφ.measurableSet_image.mpr hs)]
      congr 1
      have heq : ∀ (a : G) (q : G ⧸ H), φ (a • q) = a • φ q := by
        intro a q
        induction q using QuotientGroup.induction_on with
        | H b => exact mul_smul a b x0
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, heq g q⟩
      · rintro ⟨q, hq, h⟩
        refine ⟨g⁻¹ • q, by simpa using hq, ?_⟩
        rw [heq, h, inv_smul_smul]
  let ν0 : Measure H := Measure.haar
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ :=
    GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν0 _ hrad
  let c := Measure.haarScalarFactor μ dg
  have hc : μ = c • dg := Measure.isMulLeftInvariant_eq_smul μ dg
  have hcpos : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ dg).ne'
  refine ⟨c • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hcpos, fun f hf s hs => ?_⟩
  have h1 : ∫⁻ y, ∫⁻ h' : H, f (s y * (h' : G)) ∂ν0 ∂ν = ∫⁻ g, f g ∂dg := by
    rw [(hq f hf).2]
    conv_lhs => rw [← hmap]
    rw [hφ.lintegral_map]
    refine lintegral_congr fun q => ?_
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk H ν0 f]
    congr 1
    apply orbitMap_injective x0
    rw [orbitMap_mk]
    exact hs _ (by
      have : φ q ∈ Set.range φ := ⟨q, rfl⟩
      rwa [hrange] at this)
  rw [hc]
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end GlobalTheory.WeilOrbit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbitStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.weil_integration_formula_orbit : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.WeilOrbit.weil_formula | exact GlobalTheory.WeilOrbit.weil_formula | (intros; apply GlobalTheory.WeilOrbit.weil_formula <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibre

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserHaar

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem linearIndependent_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type)
    [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : HA R σ J) {X : Fin a → Fin n → R ⊗[F] E} (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (g • X) := by
  have hker : LinearMap.ker (lin R σ J g) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
    rw [← lin_inv_lin R σ J g x, hxy, lin_inv_lin]
  exact hX.map' (lin R σ J g) hker

theorem exists_haar_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.localUnitaryGroup_tuples_topological_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨-, -, -, -, hfree⟩ := GlobalTheory.T.standardFrame_gram_det_ne_zero F E σ hCM n J hJ r P T hP
  have hx0 := hfree v
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨hne, hfin⟩ := GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib x0 S hx0 hgram
  have hinv := GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S
  have hcont := (h9 (r + 1)).2
  have hnull : (fib S) {y | ¬ ∃ g : HA (Fv F v) σ J, g • x0 = y} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (hfib.1 S)
    intro hmem
    exact hy (GlobalTheory.T.exists_smul_localWitt_free_tuple_gram F E σ hCM n J hJ v r P T hP y hmem.2 hmem.1)
  have hsmul : ∀ g : HA (Fv F v) σ J, Continuous
      (fun y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E => g • y) := fun g =>
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hinv' : ∀ (g : HA (Fv F v) σ J) (s : Set (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)),
      MeasurableSet s → (fib S) ((fun y => g • y) ⁻¹' s) = (fib S) s := by
    intro g s hs
    rw [← Measure.map_apply (hsmul g).measurable hs, hinv g]
  have hcpt : ∀ K : Set (HA (Fv F v) σ J), IsCompact K →
      (fib S) ((fun g => g • x0) '' K) < ⊤ := by
    intro K hK
    refine hfin _ (hK.image ?_) ?_
    · exact hcont.comp (Continuous.prodMk continuous_id continuous_const)
    · rintro _ ⟨g, -, rfl⟩
      exact linearIndependent_smul (Fv F v) σ J g hx0
  obtain ⟨μ0, hμ0, hw⟩ := GlobalTheory.T.weil_integration_formula_orbit (HA (Fv F v) σ J) (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) x0
    hcont μG hμG (fib S) hnull hinv' hcpt hne
  exact ⟨μ0, hμ0, hnull, hw⟩

end GlobalTheory.LocalStabiliserHaar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibreStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  first | exact @GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | exact GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | (intros; apply GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser <;> assumption)
end
end
