module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwich
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionalsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwichStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  first | exact @GlobalTheory.ThetaCoefCont.continuous_coef | exact GlobalTheory.ThetaCoefCont.continuous_coef | (intros; apply GlobalTheory.ThetaCoefCont.continuous_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilatorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  first | exact @GlobalTheory.IsoMeanAnnih.finPart_mem_compact | exact GlobalTheory.IsoMeanAnnih.finPart_mem_compact | (intros; apply GlobalTheory.IsoMeanAnnih.finPart_mem_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicIntegrable

theorem integrable_of_rapid_decay : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  intro D a b μ hμ θ hθ f hf K hK hKf hdec
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ

  let π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ) := fun y i j τ => θ τ (infPart D (y i j))
  have hπc : Continuous π := continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))
  have hπm : Measurable π := hπc.measurable

  let s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b := fun c => Matrix.of fun i j => σ (c i j)
  have hπs : ∀ c y, π (s c + y) = c + π y := by
    intro c y; funext i j τ
    show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp]
  have hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D) := by
    intro c y; ext i j
    show finPart D (σ (c i j) + y i j) = finPart D (y i j)
    rw [RingHom.map_add (f := _), hσ.fin, zero_add]
  let S : Set (Mx D a b) := {y | y.map (finPart D) ∈ K}
  let ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ) := (μ.restrict S).map π
  have hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]
    have e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]
    rw [e, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun A hA => ?_⟩
    obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
    choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R
      ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K)
      (hK.image ((continuous_apply j).comp (continuous_apply i)))
    have hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j
    rw [hνA _ hA.isClosed.measurableSet]
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    refine lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)
    rintro y ⟨hyA, hyS⟩ i - j -
    refine hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)
    exact (norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))
  have hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar

  set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN
  obtain ⟨C, hC⟩ := hdec N
  let G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ := fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))
  have hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C
  have hGν : Integrable G ν := by
    rw [hνe]; exact hGv.smul_measure ENNReal.coe_ne_top
  have hGπ : Integrable (G ∘ π) (μ.restrict S) :=
    (integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν
  have hbound : ∀ y, ‖f y‖ ≤ G (π y) := by
    intro y
    have hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2
        fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h1 : 0 < 1 + ‖π y‖ := by positivity
    have h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N :=
      pow_le_pow_left₀ h1.le (by linarith) N
    have h3 := hC y
    have h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C := le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3
    show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))
    rw [Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]
    exact h4
  have hfS : IntegrableOn f S μ :=
    hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)
  exact hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy

end GlobalTheory.AdelicIntegrable

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFiniteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  first | exact @GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | exact GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | (intros; apply GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivial

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivialStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  first | exact @GlobalTheory.CoeffVanish.matrixCoeff_eq_zero | exact GlobalTheory.CoeffVanish.matrixCoeff_eq_zero | (intros; apply GlobalTheory.CoeffVanish.matrixCoeff_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctionalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ ξ : WO V W, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ ξ)| ^ m * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  first | exact @GlobalTheory.ThetaDecay.coef_decay | exact GlobalTheory.ThetaDecay.coef_decay | (intros; apply GlobalTheory.ThetaDecay.coef_decay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem integrable_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  intro D V W a b P Q hP hQ _hiso ψ hψ μ hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨U, hU, hvan⟩ := GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨K, hK, hKmem⟩ := GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator D V W a b P Q hP hQ ψ hψ U hU
  refine GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite D a b μ hμ θ hθ _ (GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG') K hK ?_ ?_
  · intro y hy
    by_contra hne
    apply hy
    refine hKmem y fun u hu hu0 => ?_
    by_contra h1
    exact hne (hvan _ u hu hu0 h1)
  · refine GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals D V W a b P Q hP hQ θ hθ _ fun τ z m => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
    exact ⟨C, fun y => hC _⟩

end GlobalTheory.IsoMean

end
end
end
