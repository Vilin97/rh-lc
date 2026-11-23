module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffHeisenbergTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecay
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffPolynomialDecayRealDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLe

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem integrable_of_tsum_translate_norm_le
    (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] (μ : Measure G) (hμ : μ.IsAddLeftInvariant) (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h𝓕μ : μ 𝓕 < ⊤) (c : G → ℂ) (hc : Continuous c)
    (C : ℝ) (hC : ∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧
      ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) : Integrable c μ := by
  haveI : VAddInvariantMeasure Γ G μ := ⟨fun g s _ => measure_preimage_add μ (g : G) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [h𝓕.lintegral_eq_tsum'' (fun x => ‖c x‖ₑ)]
  rw [← lintegral_tsum (f := fun (γ : Γ) x => ‖c (γ +ᵥ x)‖ₑ) fun γ : Γ =>
    ((hc.comp (continuous_const_vadd (γ : G))).measurable.enorm).aemeasurable]
  have hpt : ∀ x, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ≤ ENNReal.ofReal C := by
    intro x
    have h1 : ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ = ENNReal.ofReal (∑' γ : Γ, ‖c ((γ : G) + x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hC x).1]
      refine tsum_congr fun γ => ?_
      rw [ofReal_norm_eq_enorm]
      rfl
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC x).2
  calc ∫⁻ x in 𝓕, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal C ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * μ 𝓕 := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h𝓕μ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLeStatement

section

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.integrable_of_tsum_norm_translate_le : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ := by
  first | exact @GlobalTheory.integrable_of_tsum_translate_norm_le | exact GlobalTheory.integrable_of_tsum_translate_norm_le | (intros; apply GlobalTheory.integrable_of_tsum_translate_norm_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.rationalTranslateSum_bounded_rapidDecay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  first | exact @GlobalTheory.LatticeTranslateSum.sum_translates_bounded | exact GlobalTheory.LatticeTranslateSum.sum_translates_bounded | (intros; apply GlobalTheory.LatticeTranslateSum.sum_translates_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessOrthogonalLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.MatCoefLevel

theorem matCoef_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  intro D ψ hψ S T μ 𝓕 hcov f f₀ hf hf₀
  obtain ⟨U₁, hU₁, hl₁⟩ := hf.level
  obtain ⟨U₂, hU₂, hl₂⟩ := hf₀.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro w hw u hu hinf
  obtain ⟨hμ, h𝓕, -⟩ := hcov
  have hu₁ : heisO ψ S T u f = f := hl₁ u (AddSubgroup.mem_inf.1 hu).1 hinf
  have hu₂ : heisO ψ S T u f₀ = f₀ := hl₂ u (AddSubgroup.mem_inf.1 hu).2 hinf
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ w
  have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf hg u
  rw [hu₁, heisO_comm, hu₂] at e1
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
      starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) := by
    unfold GlobalTheory.Ker.ipO
    rw [← integral_const_mul]
    congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  rw [e2] at e1
  have hw' : GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 := hw
  have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) = 0 := by
    linear_combination e1
  have h4 : starRingEnd ℂ (ψ (symplO S T u w)) = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hw')
  have h5 : ψ (symplO S T u w) = 1 := by
    have h6 := congrArg (starRingEnd ℂ) h4
    rwa [Complex.conj_conj, map_one] at h6
  exact (psi_symplO_swap ψ _ _).1 h5

end GlobalTheory.MatCoefLevel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessOrthogonalLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_orthogonal_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  first | exact @GlobalTheory.MatCoefLevel.matCoef_level | exact GlobalTheory.MatCoefLevel.matCoef_level | (intros; apply GlobalTheory.MatCoefLevel.matCoef_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomain

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem unfold_integral_fundamentalDomain (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) : μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  intro hμ 𝓕 h𝓕 c g hc hg hB
  obtain ⟨B, hB⟩ := hB
  have hcg : Integrable (fun w => c w * g w) μ :=
    hc.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  rw [h𝓕.integral_eq_tsum'' _ hcg]
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun w => c ((γ : G) + w) * g ((γ : G) + w)) (μ.restrict 𝓕) := by
    intro γ
    exact (hcg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_left μ (γ : G))).restrict
  have hfin : ∑' γ : Γ, ∫⁻ w in 𝓕, ‖c ((γ : G) + w) * g ((γ : G) + w)‖ₑ ∂μ ≠ ⊤ := by
    have := h𝓕.lintegral_eq_tsum'' (fun w => ‖c w * g w‖ₑ)
    simp only [AddSubgroup.vadd_def, vadd_eq_add] at this
    rw [← this]
    exact hcg.2.ne
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  exact (integral_tsum hmeas hfin).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomainStatement

section

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  first | exact @GlobalTheory.unfold_integral_fundamentalDomain | exact GlobalTheory.unfold_integral_fundamentalDomain | (intros; apply GlobalTheory.unfold_integral_fundamentalDomain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MoyalOrthogonalityHeisenbergThetaFunctions

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.MoyalTheta

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  intro D ψ hψ S T v f f₀ hf hf₀
  have hv : IsCovolOne (ratL T S) v.μ v.𝓕 := v.covol
  obtain ⟨hμ, h𝓕, h1⟩ := hv
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : IsTopologicalAddGroup (WO S T) := i1
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : DiscreteTopology (ratL T S) := i5
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨-, -, -, -, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hcc := GlobalTheory.T.continuous_thetaMatrixCoeff_heisenbergTranslate D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀
  obtain ⟨C, hC⟩ := GlobalTheory.T.rationalTranslateSum_bounded_rapidDecay D ψ hψ θ hθ S T _ (GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_orthogonal_level D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
    (GlobalTheory.T.thetaMatrixCoeff_polynomialDecay_realDirections D ψ hψ θ hθ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
  have hint : Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ :=
    GlobalTheory.T.integrable_of_tsum_norm_translate_le (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 (by rw [h1]; exact ENNReal.one_lt_top) _ hcc C hC
  refine ⟨hint, fun x => ?_⟩
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hgc : Continuous fun w => heisO ψ S T w f₀ x := by
    unfold heisO
    exact (hψ.1.1.comp (hcont.comp (continuous_const.prodMk continuous_id))).mul
      (hf₀.cont.comp (continuous_const.add continuous_id))
  obtain ⟨-, ⟨B, hB⟩, -⟩ := GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀
  have hgb : ∃ B : ℝ, ∀ w, ‖heisO ψ S T w f₀ x‖ ≤ B :=
    ⟨B, fun w => by rw [GlobalTheory.ThetaSquare.norm_heisO hψ]; exact hB _⟩
  rw [GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 _ _ hint hgc hgb]
  simp_rw [GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀ _ x (hC _).1]
  have e : ∀ w, f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x = f x * (f₀ (w + x) * star (f₀ (w + x))) := by
    intro w
    have hu : star (ψ (symplOH S T x w)) * ψ (symplOH S T x w) = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    unfold heisO
    rw [star_mul, add_comm x w]
    linear_combination (f x * f₀ (w + x) * star (f₀ (w + x))) * hu
  simp_rw [e]
  rw [integral_const_mul]
  have hper : ∀ γ ∈ ratL T S, ∀ w : WO S T, f₀ (γ + w) * star (f₀ (γ + w)) = f₀ w * star (f₀ w) := by
    rintro _ ⟨γ, rfl⟩ w
    have hq := hf₀.quasi γ w
    have hu : ψ (-(symplOH S T (ratW T S γ) w)) * star (ψ (-(symplOH S T (ratW T S γ) w))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    change f₀ (ratW T S γ + w) * star (f₀ (ratW T S γ + w)) = _
    rw [hq, star_mul]
    linear_combination (f₀ w * star (f₀ w)) * hu
  rw [GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) v.μ v.𝓕 h𝓕 (fun w => f₀ w * star (f₀ w)) hper x]
  unfold thPair
  ring

end GlobalTheory.MoyalTheta

end
end
end
