module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfold
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOneStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFold
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIffStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatible

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Unfold1F

open GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}

theorem measurableSet_usetF (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, hbor, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hg (M + 1) _ hJ'
  have hq : Continuous fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) v) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc (n + 1) (M + 1) _).matrix_elem 0 0))
  have hset : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) =
      (fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
        s0 R (gramR R σ (blockOne (algebraMap F E t) J) v)) ⁻¹' B₀ := by
    ext v
    constructor
    · rintro ⟨S, hS, hSe⟩
      simpa [BsetF, hSe] using hS
    · intro hv
      refine ⟨g v, ?_, (hg v).symm⟩
      simpa [BsetF, ← hg v] using hv
  have hfree := GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR (n + 1) (M + 1)
  unfold UsetF
  rw [hset]
  exact (D.hB₀.preimage hq).measurableSet.inter hfree.measurableSet

theorem chi_eq_zero_F
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀) :
    chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) y = 0 := by
  unfold chi
  have hz : ∀ Z : Fin n → Fin (M + 1) → R ⊗[F] E,
      (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ (Fin.cons (y 0) Z) = 0 := by
    intro Z
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨⟨S, hS, hSe⟩, -⟩
    apply hy
    rw [← corner_half_trace_gram_cons R σ _ y Z, ← hSe]
    exact hS
  simp [hz]

end Main

theorem first_step_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  have hUm : MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurableSet_usetF D
  have hφ' := hφ.indicator hUm
  have hchi := measurable_chi D₀ hφ'

  obtain ⟨-, -, -, hbor1, hg1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g₁, hg₁c, hg₁⟩ := hg1 (M + 1) _ hJ'
  obtain ⟨hUo, -, -, -, -, hae⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  have hU₁ : MeasurableSet {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
      IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} := by
    have : {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} = g₁ ⁻¹' Unt σ R 1 := by
      ext X
      simp [Unt, hg₁ X]
    rw [this]
    exact (hUo.preimage hg₁c).measurableSet
  obtain ⟨hh, hh2, hh3⟩ := hermScal_main F E σ D.hCM R d b
  have hemb : MeasurableEmbedding (hermScal R σ) := (hh.homeomorph _).measurableEmbedding
  have hs0 : ∀ x : R, s0 R ((hermScal R σ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = x :=
    fun x => hh.injective (hh2 (hermScal R σ x))
  set χ := chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) with hχ
  have hzero : ∀ y, s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀ → χ y = 0 :=
    fun y hy => chi_eq_zero_F φ hy

  have e1 : ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hUm]
    exact GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section F E σ D.hCM M _ hJ' R D.hR d b lam D.hlam n (sTil σ J t s a) (measurable_sTil D₀) _ hφ'
  have e2 : ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) =
      ∫⁻ y in {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hU₁]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}
    · exact (Set.indicator_of_mem hy χ).symm
    · rw [Set.indicator_of_notMem hy, hzero y fun h => hy (isUnit_gram D₀ h)]
  have e3 := D.hm₁.2.1 χ hchi
  rw [← hh3 lam D.hlam, hemb.lintegral_map] at e3
  have e4 : ∫⁻ x, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam = ∫⁻ x in B₀, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam := by
    rw [← lintegral_indicator D.hB₀.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hae (hermScal R σ x)] with y hy
      refine hzero y ?_
      rw [hy, hs0]
      exact hx
  rw [e1, e2, e3, e4]
  refine setLIntegral_congr_fun D.hB₀.measurableSet fun x hx => ?_
  have hm : m₁ (hermScal R σ x) =
      κ₁ (a x) • (m₁ (hermScal R σ (algebraMap F R t))).map (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) := by
    have := D.hscale (a x)
    rwa [← D.hsq x hx] at this
  have hsm : Measurable (scl (N := M + 1) (n := 1) (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) :=
    measurable_scl.comp (measurable_const.prodMk measurable_id)
  simp only [hm]
  rw [lintegral_smul_measure, lintegral_map hchi hsm]
  rfl

end GlobalTheory.CompanionTheory.SW.StageF.Unfold1F
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatibleStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | exact GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurable

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Fibre

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem chi_at_fibreF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hJt := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, -, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu
  have huE : IsUnit (u ⊗ₜ[F] (1 : E)) :=
    (Units.isUnit (a x)).map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hfree : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      LinearIndependent (R ⊗[F] E)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) ↔
      LinearIndependent (R ⊗[F] E) X := fun c X =>
    (GlobalTheory.T.linearIndependent_unitary_action_iff F E R σ (M + 1) (n + 1) _ (s y₀) _).trans
      (GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n _ huE c X)
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    constructor
    · rintro ⟨-, h⟩
      exact (hfree c X).1 h
    · intro hX
      refine ⟨?_, (hfree c X).2 hX⟩
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      simp only [Set.mem_preimage, hinv]
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ?_, (hg _).symm⟩
      change s0 R _ ∈ B₀
      rw [h3.1]; exact hx
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    (GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR n M).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = _ := D.hm'.2.1 _ (hψ c)

end GlobalTheory.CompanionTheory.SW.StageF.Fibre
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurableStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | exact GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionIntegral

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_UsetF_eq_MidF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hm, -, -, -⟩ := GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [GlobalTheory.T.fibre_measure_extension_compatible F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold MidF
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  have key := Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | LinearIndependent (R ⊗[F] E) X} Set.univ MeasurableSet.univ m' hm (fun S hS => absurd (Set.mem_univ S) hS)
    D.hm'.2.1 f hf
  simp only [Measure.restrict_univ] at key
  exact key

end GlobalTheory.CompanionTheory.SW.StageF
end
end
