module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforward
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubini
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOneStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneIntegral

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_fibSF_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.StageF
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneIntegralStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_by_one_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | exact GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetric

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem measurable_PintF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, ⟨κ, hκs, hκm⟩, -, -⟩ :=
    GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  haveI : IsSFiniteKernel κ := hκs
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  have hfin := Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner
  have hm'κ : m' = fun S => κ S := funext fun S => (hκm S).symm
  rw [hm'κ]
  exact hfin

end GlobalTheory.CompanionTheory.SW.StageF
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetricStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_symmetric : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | exact GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionUnique

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.FoldF

theorem foldF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hs0c, hacS, hcvc, hschc, -⟩ :=
    GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hBopen : IsOpen (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := D.hB₀.preimage hs0c
  have hGon0 := GlobalTheory.T.fibre_measure_extension_by_one_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.fibre_measure_extension_symmetric F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hGoff0 : ∀ S, S ∉ BsetF R σ B₀ →
      ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibSF
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ BsetF R σ B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (BsetF R σ B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => Fold.corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ := h
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S', Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨Fold.qM R σ t (cr r), Fold.qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      Pint σ J t m₁ m' s φ (u : R) z.1 z.2
    have hf : Measurable f :=
      hmeas.comp (measurable_const.prodMk measurable_id)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [Fold.schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨Fold.qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            Fold.qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (Fold.qM R σ t) h1)
        rw [h3]
      have hB : e (x, r, S'') ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := by
        show s0 R _ ∈ B₀
        rw [h0]
        exact hx
      rw [hGon _ hB, h0, h1, h2, ← hu]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := rfl
  rw [hL]
  unfold MidF
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.StageF.FoldF
end
end
end
