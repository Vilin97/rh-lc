module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactLowerBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCoverCountableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCompactCoverByUnitScalingsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDependentSetNullStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalCompactCoverByUnitsStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBound

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound

theorem compactOpen_mass_le : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ h P hPc hPo hPZ
  have hPm : MeasurableSet P := hPo.measurableSet
  let φ : V → ℝ := P.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hPo.frontier_eq, hPc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hPc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ Z := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hPc.isClosed) hPZ
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(m s) = (m s P).toReal := fun s => by
    simp [φ, integral_indicator hPm, Measure.real]
  have hfin : ∀ s, m s P ≠ ⊤ := fun s => by
    have h := hI s (Set.mem_univ s)
    rw [integrable_indicator_iff hPm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : ContinuousOn (fun s => (m s P).toReal) (Q '' P) := by
    have h' : ContinuousOn (fun s => (m s P).toReal) Set.univ := by
      simpa only [hint] using hC
    exact h'.mono (Set.subset_univ _)
  obtain ⟨C, hCb⟩ := (hPc.image hQ).exists_bound_of_continuousOn hcont
  have hoff : ∀ s, s ∉ Q '' P → m s P = 0 := fun s hs => by
    have hae := GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.ae_lift_eq h (g := Q) (fun _ => rfl) Function.injective_id s
    refine measure_mono_null (t := {x | ¬ Q x = s}) ?_ hae
    intro x hx hxs
    exact hs ⟨x, hx, hxs⟩
  have hbd : ∀ s, m s P ≤ (C.toNNReal : ℝ≥0∞) := fun s => by
    by_cases hs : s ∈ Q '' P
    · have h1 : (m s P).toReal ≤ C := le_trans (le_abs_self _) (by simpa using hCb s hs)
      rw [← ENNReal.ofReal_toReal (hfin s)]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [hoff s hs]
      exact bot_le
  refine ⟨C.toNNReal, fun S hS => ?_⟩
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.fibre_mass_on h (g := Q) (fun _ => rfl) Function.injective_id hQ.measurable hPm hS
    (fun x hx => hPZ hx.1)]
  calc ∫⁻ s in S, m s P ∂lam ≤ ∫⁻ _ in S, (C.toNNReal : ℝ≥0∞) ∂lam := lintegral_mono hbd
    _ = (C.toNNReal : ℝ≥0∞) * lam S := by rw [setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBoundStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.fibre_volume_compact_bound : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFreeFibreLocal

section

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

open GlobalTheory.CompanionTheory.SW.FibreRatio

theorem isFibreFamily_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) (h : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam 1 M)
      (fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) id
      {X : Fin 1 → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} lam Set.univ
      (fun s => m (hermScal R σ s)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hc1, hc2, hc3⟩ := hm
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have hcq : Continuous (qS R σ (F := F) (E := E)) := continuous_qS R htr
  have hmap : coordHerm R σ b lam 1 = lam.map (hermScal R σ) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hcs.measurable hA, ← coordHerm_qS R h htr b lam (hcs.measurable hA)]
    congr 1
    ext S
    show S ∈ A ↔ hermScal R σ (qS R σ S) ∈ A
    rw [hermScal_qS R h S]
  have hemb : MeasurableEmbedding (hermScal R σ (F := F) (E := E)) :=
    (Homeomorph.mk ⟨hermScal R σ, qS R σ, qS_hermScal R h, hermScal_qS R h⟩ hcs hcq).measurableEmbedding
  refine ⟨fun s => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hc1 (hermScal R σ s))
    rintro X ⟨hX, hXU⟩
    refine ⟨?_, hXU⟩
    have e : gramR R σ J X = ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  · rw [hc2 φ hφ, hmap, hemb.lintegral_map]
  · obtain ⟨ha, hb⟩ := hc3 φ hφc hφs hφU
    exact ⟨fun s _ => ha _ (Set.mem_univ _),
      (hb.comp hcs.continuousOn (fun _ _ => Set.mem_univ _))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact LengthFibre.isFibreFamily_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ b lam hlam.1 m hm

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFreeFibreLocalStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.rank_one_free_fibre_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSet

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil

def dilHomeo {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (M : ℕ) (u : Aˣ) :
    (Fin 1 → Fin M → A) ≃ₜ (Fin 1 → Fin M → A) where
  toFun X p k := (u : A) * X p k
  invFun X p k := ((u⁻¹ : Aˣ) : A) * X p k
  left_inv X := by
    funext p k
    simp
  right_inv X := by
    funext p k
    simp
  continuous_toFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))

theorem linearIndependent_dil {A : Type} [CommRing A] {M : ℕ} (u : Aˣ) (X : Fin 1 → Fin M → A)
    (hX : LinearIndependent A X) :
    LinearIndependent A (fun (p : Fin 1) (k : Fin M) => (u : A) * X p k) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  have h0 : ∑ i, (g i * (u : A)) • X i = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := hX (fun i => g i * (u : A)) h0 i
  exact (Units.mul_left_eq_zero u).1 h1

theorem dil_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ M v u P hc ho hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := TopK.isTopRing (Fv F v)
  refine ⟨hc.image (dilHomeo M u).continuous, (dilHomeo M u).isOpenMap _ ho, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact linearIndependent_dil u X (hP hX)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSetStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.unit_scaling_compact_free_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropic

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AvgZero

theorem avg_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b v lam hlam m hm A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, htr, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI : lam.IsAddHaarMeasure := hlam.1
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hQ : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((a10 1 M J).matrix_elem 0 0))
  have hfam := GlobalTheory.T.rank_one_free_fibre_local F E σ hCM M J hJ d b v lam hlam m hm
  have hnull := GlobalTheory.T.local_dependent_set_null F E σ hCM M J hJ hM1 d b v lam hlam
  obtain ⟨ι, hι, P, u, hPc, hPo, hPZ, hsum, hcov⟩ :
      ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
        IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧
        Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
        A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
          ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
            (u i : Fv F v ⊗[F] E) * X p k) '' P := by
    by_cases hs : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨τ⟩ := hs
      exact GlobalTheory.T.split_local_compact_cover_by_units F E σ hCM M hM2 v τ A hAc
    · exact GlobalTheory.T.local_compact_cover_by_unit_scalings F E σ hCM M hM2 v
        (GlobalTheory.CompanionTheory.DictLoc.isField_tensor_of_no_algHom hCM.2.2.1 (not_nonempty_iff.1 hs)) A hAc
  obtain ⟨c, hc⟩ := GlobalTheory.T.fibre_volume_compact_bound _ _ _ lam _ _ _ hQ hfam P hPc hPo hPZ
  have hset := fun i => GlobalTheory.T.unit_scaling_compact_free_set F E σ hCM M v (u i) P hPc hPo hPZ
  have hb := fun i S hS => GlobalTheory.T.local_rank_one_volume_bound F E σ hCM M J hJ hM1 d b v lam hlam P c hPo.measurableSet hc (u i) S hS
  have hmass := fun i => GlobalTheory.T.fibre_volume_compact_open_le_of_measure_le _ _ _ lam _ _ _ hQ hfam _ (hset i).1 (hset i).2.1 (hset i).2.2 _ (hb i)
  have key := GlobalTheory.T.fibre_volume_cover_countable _ _ ι _ lam _ _ _ hQ hfam hnull A hAc hAo _ _ hset hcov (hsum.mul_left c) hb hmass 0
  have e0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = hermScal (Fv F v) σ 0 :=
    Subtype.ext (funext fun _ => funext fun _ => by
      show (1 : Fv F v) ⊗ₜ[F] (0 : E) = (0 : Fv F v) ⊗ₜ[F] (1 : E)
      simp)
  rw [e0]
  exact key

end GlobalTheory.CompanionTheory.SW.AvgZero
end
end
end
