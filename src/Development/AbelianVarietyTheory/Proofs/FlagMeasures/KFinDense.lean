module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.UpqRep
import Mathlib.Tactic
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeakStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePoStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverage

section

@[expose] public section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem hasDerivAt_exp_integral_dsigW (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H)
    (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : GlobalTheory.KFinAvg.IsHaarKH k r μ)
    (hφ : Continuous φ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
      (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := hσ'
  obtain ⟨hprob, hK0, -, -⟩ := hμ
  have hKc := isCompact_KH k r
  have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := mem_ae_iff.2 hK0
  have hres : μ.restrict (GlobalTheory.ThA.KH k r) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ D' : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D', Formalism.MainNotions.S.InLieHpk k r Y) →
      Integrable (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) μ := by
    intro D' hD'
    have h1 : ContinuousOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) :=
      hφ.continuousOn.smul ((Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hσ hv D' hD').mono Set.inter_subset_left)
    have h2 : IntegrableOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) μ :=
      h1.integrableOn_compact hKc
    rwa [IntegrableOn, hres] at h2
  have hXD : ∀ Y ∈ X :: D, Formalism.MainNotions.S.InLieHpk k r Y := by
    intro Y hY
    rcases List.mem_cons.1 hY with h | h
    · rw [h]; exact hX
    · exact hD Y h
  have hexp := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v)))
    (F' := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)))
    (bound := fun g => ‖φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)‖) (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((σ (NormedSpace.exp ((t : ℂ) • X))).integrable_comp (hint D hD)).aestronglyMeasurable)
    ((σ _).integrable_comp (hint D hD))
    ((σ _).integrable_comp (hint _ hXD)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g t _ => (hσ.2.1 _ (hexp t) _).le)
    (hint _ hXD).norm
    (by
      filter_upwards [hae] with g hg t _
      have hsm := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg.1
      have h0 := (Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hsm D hD hX).const_smul (φ g)
      have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
      rw [← sub_self t] at h1
      have h2 := h1.comp_sub_const t t
      simp only [map_smul]
      convert (preTransparency := .reducible) h2 using 1
      · funext s
        have e : NormedSpace.exp ((s : ℂ) • X) =
            NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X) := by
          rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
          congr 2
          push_cast; ring
        rw [e, hσ.1.2 _ (hexp t) _ (hexp (s - t))]
        simp only [Function.comp, Pi.smul_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]
        rfl
      · simp)
  have h3 := key.2
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, one_apply_eq_self] at h3
  convert h3 using 1
  funext t
  exact ((σ _).integral_comp_comm (hint D hD)).symm

end GlobalTheory.KFinAvg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverageStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.hasDerivAt_derived_action_max_compact_average : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H) (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → Continuous φ → Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v → (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X → HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  first | exact @GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | exact GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | (intros; apply GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitian

section

@[expose] public section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem integrable_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hf : Continuous f) (v : H) :
    Integrable (fun g => f g • σ g v) μ := by
  haveI := hμ.1
  have hK := isCompact_KH k r
  have hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r) := fun g hg => hg.1
  have hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) :=
    hf.continuousOn.smul ((hσ.2.2 v).mono hsub)
  have hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ := hc.integrableOn_compact hK
  have hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  rw [IntegrableOn, hr] at hI
  exact hI

theorem integral_sum_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {N : ℕ} {b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hb : ∀ j, Continuous (b j))
    (c : Fin N → ℂ) (v : H) :
    ∫ g, (∑ j, c j * b j g) • σ g v ∂μ = ∑ j, c j • ∫ g, b j g • σ g v ∂μ := by
  simp_rw [Finset.sum_smul, mul_smul]
  rw [integral_finsetSum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) :
      Integrable (fun g => c j • (b j g • σ g v)) μ))]
  simp_rw [integral_smul]

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg

theorem isKFinHpk_integral_translates : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  intro k r H _ _ _ σ μ hσ hμ N b hb hinv c v
  obtain ⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ := ⟨_, fun _ => rfl⟩
  have key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j := by
    intro c'
    rw [integral_sum_smul_orbit hσ hμ hb c' v]
    simp_rw [hw]
  have hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w) := fun c' =>
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩
  · rw [key]; exact hmem c
  · intro a ha x hx
    have hu : star a * a = 1 := ha.2.1
    have haa : a⁻¹ * a = 1 := by rw [Matrix.inv_eq_left_inv hu]; exact hu
    have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := by rw [ae_iff]; exact hμ.2.1
    have hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w) := by
      intro j
      obtain ⟨d, hd⟩ := hinv a⁻¹ j
      have h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ := by
        rw [hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with g hg
        rw [map_smul, hσ.1.2 a ha.1 g hg.1]
        rfl
      have hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g) :=
        continuous_const.matrix_mul continuous_id
      have h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ := by
        conv_rhs => rw [← hμ.2.2.1 a ha]
        rw [integral_map hcm.aemeasurable]
        · simp only [← Matrix.mul_assoc, haa, Matrix.one_mul]
        · rw [hμ.2.2.1 a ha]
          exact (integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable
      rw [h1, h2]
      simp_rw [hd]
      rw [key]
      exact hmem d
    have hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    exact hle hx

end GlobalTheory.KFinAvg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitianStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.integral_translate_family_isKFinite_hermitian : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  first | exact @GlobalTheory.KFinAvg.isKFinHpk_integral_translates | exact GlobalTheory.KFinAvg.isKFinHpk_integral_translates | (intros; apply GlobalTheory.KFinAvg.isKFinHpk_integral_translates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DsigWSubAvg

section

@[expose] public section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_sub_avg {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} {v : H}
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD' : ∀ (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0) :
    ∀ D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) →
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (v - ∫ g, φ g • σ g v ∂μ) =
        Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D v - ∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hD X List.mem_cons_self
    have hD1 : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D _)) 0 = _
    rw [ih hD1]
    simp only [map_sub]
    exact ((Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hv D hD1 hX).sub (hD' D X hD1 hX)).deriv

theorem kDense : Formalism.MainNotions.S.Pv.AmpDD.KDense := by
  intro k r ε lam H _ _ _ σ _ hDS v hv Ws hWs e he
  obtain ⟨-, hU, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hDS
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian k r
  have hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v := hv
  obtain ⟨hpc, hp1, hp01, hpδ⟩ := GlobalTheory.T.unitaryRealTraceBump_peak_properties (2 * r + k + 1) (Nat.succ_pos _)
  have hKc : IsCompact (GlobalTheory.ThA.KH k r) := isCompact_KH k r
  have hK1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r :=
    ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      one_mem _⟩
  have hpK : ∀ x ∈ GlobalTheory.ThA.KH k r, 0 ≤ peak (2 * r + k + 1) x ∧ peak (2 * r + k + 1) x ≤ 1 :=
    fun x hx => hp01 x hx.2
  have hpU : ∀ U ∈ 𝓝 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∃ δ < 1,
      ∀ x ∈ GlobalTheory.ThA.KH k r, x ∉ U → peak (2 * r + k + 1) x ≤ δ := fun U hU' => by
    obtain ⟨δ, hδ, h⟩ := hpδ U hU'
    exact ⟨δ, hδ, fun x hx hxU => h x hx.2 hxU⟩
  have hσ1 : σ 1 = 1 := hU.1.1
  have hconv : ∀ w ∈ Ws, Tendsto (fun m : ℕ => ∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
      atTop (𝓝 (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)) := by
    intro w hw
    have hc := (Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hU hv' w (hWs w hw)).mono
      (Set.inter_subset_left : GlobalTheory.ThA.KH k r ⊆ _)
    have := GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak _ μ hμ.1 _ 1 _ hKc hμ.2.1 hK1 hμ.2.2.2 hpc hp1 hpK hpU H _ hc
    rw [hσ1, one_apply_eq_self] at this
    exact this
  set L := Ws.length
  have hε : 0 < e / (L + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, ∀ w ∈ {w | w ∈ Ws},
      dist (∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
        (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) < e / (L + 1) :=
    (Filter.eventually_all_finite Ws.finite_toSet).2 fun w hw => Metric.tendsto_nhds.1 (hconv w hw) _ hε
  obtain ⟨m, hm⟩ := hev.exists
  obtain ⟨N, b, c, hbc, hpoly, htr⟩ := GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys (2 * r + k + 1) m
  set Z : ℝ := ∫ h, peak (2 * r + k + 1) h ^ m ∂μ
  have e1 : ∀ g, peakN μ m g = ∑ j, (c j / (Z : ℂ)) * b j g := fun g => by
    show ((peak (2 * r + k + 1) g ^ m / Z : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, hpoly g, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∫ g, peakN μ m g • σ g v ∂μ, ?_, ?_⟩
  · have := GlobalTheory.T.integral_translate_family_isKFinite_hermitian k r H σ μ hU hμ N b hbc htr (fun j => c j / (Z : ℂ)) v
    simpa only [← e1] using this
  · have hD' := fun D X hD hX => GlobalTheory.T.hasDerivAt_derived_action_max_compact_average k r H σ μ (peakN μ m) v D X hU hμ
      (by rw [show peakN μ m = fun g => ∑ j, (c j / (Z : ℂ)) * b j g from funext e1]
          exact continuous_finsetSum _ fun j _ => continuous_const.mul (hbc j)) hv' hD hX
    have hterm : ∀ w ∈ Ws, ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖ ≤ e / (L + 1) := by
      intro w hw
      rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq, dsigW_sub_avg hU hv' hD' w (hWs w hw), norm_sub_rev, ← dist_eq_norm]
      exact (hm w hw).le
    calc (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖).sum
        ≤ (Ws.map fun _ => e / (L + 1)).sum := List.sum_le_sum (fun w hw => hterm w hw)
      _ = L * (e / (L + 1)) := by simp [L, List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KFinAvg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense

section

@[expose] public section

open Formalism.MainNotions.S

namespace GlobalTheory.KFinDenseDS

theorem kFin_dense : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ := by
  intro k r ε lam H _ _ _ σ hl hds v hv Ws hWs δ hδ
  obtain ⟨a, ha, hs⟩ := GlobalTheory.KFinAvg.kDense k r ε lam H σ hl hds v hv Ws hWs δ hδ
  refine ⟨a, ha, ?_⟩
  simpa only [Formalism.MainNotions.BridgeCS3d.dsigW_eq] using hs

end GlobalTheory.KFinDenseDS
end
end
