module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Aesop.Main
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUniqueness
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
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
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIffStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import GroundTheory.AutomorphicForms.ReductionMeasure
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Compactness.Paracompact

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameter

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibreJointOpen

theorem continuousOn_fibre_integral_of_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ μ ν f ι U hU B hB fib hF P _ W Φ hΦ hW C hC hCU hsupp
  obtain ⟨-, -, h3⟩ := hF

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hts : ∀ p ∈ W, tsupport (Φ p) ⊆ U := fun p hp => by
    refine (closure_minimal ?_ hC.isClosed).trans hCU
    intro v hv
    by_contra hvC
    exact hv (hsupp p hp v hvC)
  have hint : ∀ p ∈ W, ∀ b ∈ B, Integrable (Φ p) (fib b) := fun p hp b hb =>
    (h3 (Φ p) (hslice p hp) (hcs p hp) (hts p hp)).1 b hb

  have hbd : ∀ D : Set X, IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
    intro D hD hDB
    obtain ⟨φ, hc, hcs', hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs' hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono hDB)
    refine ⟨M.toNNReal, fun b hb => ?_⟩
    calc fib b C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi b (hDB hb))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM b hb))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd D hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := (((h3 (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀) (hts p₀ hp₀)).2).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hbB : b ∈ B := hDB hqD
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b hbB) (hint p₀ hp₀ b hbB)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

end GlobalTheory.CompanionTheory.SW.FibreJointOpen
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameterStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix


theorem _root_.GlobalTheory.T.fibre_integral_continuous_in_parameter : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | exact GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | (intros; apply GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSigmaFinite

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ContTwoF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open scoped TensorProduct ENNReal NNReal Matrix

theorem cont_double_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc hfree
  haveI iTR : IsTopologicalRing R := D.hR.1
  haveI iLC : LocallyCompactSpace R := D.hR.2.1
  haveI iSC : SecondCountableTopology R := D.hR.2.2.1
  haveI iT2 : T2Space R := D.hR.2.2.2.1
  have hval : IsOpenEmbedding (Units.val : Rˣ → R) := D.hR.2.2.2.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR
  haveI := kLC
  haveI := kSC
  haveI := kT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨eLC, eSC, eT2, eB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  haveI := eLC
  haveI := eSC
  haveI := eT2
  haveI := eB
  obtain ⟨gTG, gLC, gSC, gT2, gB, hactall⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := gTG
  haveI := gLC
  haveI := gSC
  haveI := gT2
  haveI := gB
  obtain ⟨hact, hact1, hactm, -⟩ := hactall (n + 1)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨-, -, hbd', -⟩ := GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -, -, -, hgram₁⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := kB n M
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := kB 1 (M + 1)
  have hUo : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR n M

  have hCt : ∀ L : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact L →
      ∃ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C ∧
        C ⊆ {X | LinearIndependent (R ⊗[F] E) X} ∧ ∀ h ∈ L, ∀ A c X,
        φ (actW R σ _ h (vec A c X)) ≠ 0 → X ∈ C := by
    intro L hL
    have hQc : IsCompact ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)) := by
      refine (hL.prod hφc).image ?_
      exact hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    have hQf : ∀ Y ∈ ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)),
        LinearIndependent (R ⊗[F] E) Y := by
      rintro _ ⟨⟨h, z⟩, ⟨-, hz⟩, rfl⟩
      exact (GlobalTheory.T.linearIndependent_unitary_action_iff F E R σ (M + 1) (n + 1) _ h⁻¹ z).2 (hfree hz)
    obtain ⟨C, hC, hCf, hCv⟩ := GlobalTheory.T.compact_free_set_projects_compact (R ⊗[F] E) M n _ hQc hQf
    refine ⟨C, hC, hCf, fun h hh A c X hne => hCv A c X ?_⟩
    refine ⟨(h, actW R σ _ h (vec A c X)), ⟨hh, subset_tsupport _ hne⟩, ?_⟩
    simp only
    rw [← hactm, inv_mul_cancel, hact1]
  have cT := continuous_tmul_one (F := F) (E := E) R

  let G : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) × HermR R σ n → ℝ :=
    fun q => ∫ X, φ (actW R σ _ q.1.1 (vec (q.1.2.1 ⊗ₜ[F] (1 : E)) q.1.2.2 X)) ∂(m' q.2)
  have hG : ∀ q, ContinuousAt G q := by
    intro q
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds q.1.1
    obtain ⟨C, hC, hCf, hCv⟩ := hCt L hLc
    have hWo : IsOpen (interior L ×ˢ (Set.univ : Set (R × (Fin n → R ⊗[F] E)))) :=
      isOpen_interior.prod isOpen_univ
    have hcΦ : Continuous (fun p : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) ×
        (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ _ p.1.1 (vec (p.1.2.1 ⊗ₜ[F] (1 : E)) p.1.2.2 p.2))) := by
      refine hφ.comp (hact.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
      exact continuous_vec.comp ((cT.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
    have hj := GlobalTheory.T.fibre_integral_continuous_in_parameter (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) _ (coordW R b lam n M)
      (coordHerm R σ b lam n) (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} hUo
      Set.univ isOpen_univ m' D.hm'
      (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E))
      (interior L ×ˢ Set.univ)
      (fun p X => φ (actW R σ _ p.1 (vec (p.2.1 ⊗ₜ[F] (1 : E)) p.2.2 X))) hcΦ.continuousOn hWo C hC hCf
      (by
        intro p hp v hv
        by_contra hne
        exact hv (hCv p.1 (interior_subset hp.1) _ _ _ hne))
    have hmem : ((interior L ×ˢ Set.univ) ×ˢ (Set.univ : Set (HermR R σ n))) ∈ 𝓝 q :=
      (hWo.prod isOpen_univ).mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hLn, trivial⟩, trivial⟩
    exact hj.continuousAt hmem
  rintro ⟨α₀, c₀, S₀⟩ ⟨hα₀, -, -⟩
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨N, hNn, hNs, hNc⟩ := local_compact_nhds (hval.isOpen_range.mem_nhds hα₀)
  have hUc : IsCompact ((Units.val : Rˣ → R) ⁻¹' N) := by
    rw [hval.isInducing.isCompact_iff, Set.image_preimage_eq_of_subset hNs]
    exact hNc
  have hNi : IsCompact ((Units.val : Rˣ → R) '' ((fun u : Rˣ => u⁻¹) '' ((Units.val : Rˣ → R) ⁻¹' N))) :=
    (hUc.image continuous_inv).image Units.continuous_val
  obtain ⟨Dc, hDc, hDn⟩ := exists_compact_mem_nhds S₀
  let C₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) :=
    (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      scl (p.1 ⊗ₜ[F] (1 : E)) (fun _ : Fin 1 => p.2 0)) ''
        (((Units.val : Rˣ → R) '' ((fun u : Rˣ => u⁻¹) '' ((Units.val : Rˣ → R) ⁻¹' N))) ×ˢ tsupport φ)
  have hC₁c : IsCompact C₁ := by
    refine (hNi.prod hφc).image ?_
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    have h1 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.2 0 i) :=
      (continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)
    have h2 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.1 ⊗ₜ[F] (1 : E)) :=
      cT.comp continuous_fst
    exact h1.mul h2
  obtain ⟨C', hC'c, hC'⟩ := D.hcpt C₁ hC₁c
  obtain ⟨C₂, hC₂c, hC₂f, hC₂⟩ := hCt C' hC'c
  obtain ⟨cD, hcD⟩ := hbd' C₂ Dc hC₂c hC₂f hDc
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hφc
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have eD : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Dc :=
    (continuous_snd.comp continuous_snd).continuousAt hDn
  have eN : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.1 ∈ N :=
    continuous_fst.continuousAt hNn
  have hmeas : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      AEStronglyMeasurable (fun y₀ => G ((s y₀, z.1, z.2.1), z.2.2))
        (m₁ (hermScal R σ (algebraMap F R t))) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous (fun h : HA R σ (blockOne (algebraMap F E t) J) => G ((h, z.1, z.2.1), z.2.2)) := by
      refine continuous_iff_continuousAt.2 fun h => ?_
      refine ContinuousAt.comp (g := G) (f := fun h => ((h, z.1, z.2.1), z.2.2)) (hG _) ?_
      exact (((continuous_id.prodMk continuous_const)).prodMk continuous_const).continuousAt
    exact (hc.measurable.comp D.hs).aestronglyMeasurable
  have hcont : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      ContinuousAt (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => G ((s y₀, z.1, z.2.1), z.2.2))
        (α₀, c₀, S₀) := by
    refine Filter.Eventually.of_forall fun y₀ => ?_
    refine ContinuousAt.comp (g := G)
      (f := fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => ((s y₀, z.1, z.2.1), z.2.2)) (hG _) ?_
    exact ((continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)).continuousAt
  have hbound : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
        ‖G ((s y₀, z.1, z.2.1), z.2.2)‖ ≤ C₁.indicator (fun _ => Bd * (cD : ℝ)) y₀ := by
    filter_upwards [eN, eD] with z hzN hzD
    filter_upwards [hgram₁ (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    obtain ⟨u, hu⟩ := hNs hzN
    have hsec := D.hsec y₀ hy₀
    have hvan : ∀ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ≠ 0 → y₀ ∈ C₁ := by
      intro X hne
      refine ⟨(((u⁻¹ : Rˣ) : R), actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)),
        ⟨⟨u⁻¹, ?_, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
      · simpa [Set.mem_inv, hu] using hzN
      · funext a i
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        simp only [scl]
        rw [actW_vec_zero, hsec, ← hu, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv,
          mul_one, ← Algebra.TensorProduct.one_def, mul_one]
    by_cases hy : y₀ ∈ C₁
    · have h2 : s y₀ ∈ C' := hC' y₀ hy hy₀
      have hvanX : ∀ X, X ∉ C₂ → φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) = 0 :=
        fun X hX => by_contra fun hne => hX (hC₂ _ h2 _ _ _ hne)
      rw [Set.indicator_of_mem hy]
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanX]
      have hfin : m' z.2.2 C₂ < ∞ := (hcD _ hzD).trans_lt ENNReal.coe_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hfin (fun X _ => hBd _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hBd0
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hcD _ hzD)
      simpa [Measure.real] using this
    · rw [Set.indicator_of_notMem hy]
      have h0 : (fun X => φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X))) = 0 :=
        funext fun X => by_contra fun hne => hy (hvan X hne)
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [h0]
      simp
  have hint : Integrable (C₁.indicator (fun _ => Bd * (cD : ℝ)))
      (m₁ (hermScal R σ (algebraMap F R t))) :=
    (integrable_indicator_iff hC₁c.isClosed.measurableSet).2 (integrableOn_const hC₁c.measure_lt_top.ne)
  exact continuousAt_of_dominated hmeas hbound hint hcont

end GlobalTheory.CompanionTheory.SW.StageF.ContTwoF
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSigmaFiniteStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_sigma_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | exact GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free <;> assumption)
end
end
