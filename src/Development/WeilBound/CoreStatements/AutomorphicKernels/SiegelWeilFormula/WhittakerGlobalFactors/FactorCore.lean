module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetLatHLoc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SelfDualMeasureLatticeOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TendstoUH

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (ν : Measure (HermR (AF F) σ n)) (f : HermR (AF F) σ n → ℂ) (hf : Integrable f ν) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∫ b in UH σ bs n S, f b ∂ν) atTop (nhds (∫ b, f b ∂ν)) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have he : ∀ S, ∫ b in UH σ bs n S, f b ∂ν = ∫ b, (UH σ bs n S).indicator f b ∂ν := fun S =>
    (integral_indicator (measurableSet_UH σ hCM bs n S)).symm
  simp_rw [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun S => hf.aestronglyMeasurable.indicator (measurableSet_UH σ hCM bs n S)
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    by_cases h : y ∈ UH σ bs n S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ bs v n}.Finite :=
      Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_latH σ bs y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : y ∈ UH σ bs n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [Set.indicator_of_mem hmem]

end PositivityTheory.SiegelWeilFormula.GFac

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.FactorCore

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem factor_core (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n))
    (haar : ∀ v, (lam v).IsAddHaarMeasure) (co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v))
    (std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (sdH : SdHerm F E σ (AF F) ψ n ν)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v))
    (z : ℂ) (hI : Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν)
    (hIv : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z)
        (νv v)) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
        (∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi) *
        ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b
          ∂(νv v))
      atTop (nhds (∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)) := by
  classical
  obtain ⟨S₀, hS₀⟩ := herm_split σ hCM ψ hψ n d bs ν sdH νi hνi νv hνv
  obtain ⟨S₁, hS₁⟩ := whI_split σ hCM M n d J hJ T bs ψ hψ θ l fr g P lam L₁ L₂ Φ Φf Φv μ haar co std pure prod sdW
    μi hμi μv hμv z
  refine (tendsto_UH σ hCM bs n ν _ hI).congr' ?_
  filter_upwards [eventually_ge_atTop (S₀ ∪ S₁)] with S hS
  have h0 : S₀ ⊆ S := fun v hv => hS (Finset.mem_union_left _ hv)
  have h1 : S₁ ⊆ S := fun v hv => hS (Finset.mem_union_right _ hv)
  rw [setIntegral_congr_fun (measurableSet_UH σ hCM bs n S) (fun b hb => hS₁ S h1 b hb)]
  exact hS₀ S h0 _ _ (fun v _ => (hIv v).aestronglyMeasurable)

theorem factorX : FactorX := by
  intro F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν h μi νi μv νv hμi hνi hμv hνv z hI _ hIv
  exact factor_core σ h.cm M n d J h.herm T bs ψ h.chr θ l fr g P lam L₁ L₂ Φ Φf Φv μ ν h.haar h.co h.std h.pure h.prod
    h.sdW h.sdH μi νi μv νv hμi hνi hμv hνv z hI hIv

end PositivityTheory.SiegelWeilFormula.GFac

end
end
end
