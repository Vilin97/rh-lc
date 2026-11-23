module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuousStatement
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinates
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
public import Mathlib.MeasureTheory.Integral.Pi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBoundStatement

section

@[expose] public section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.archimedean_orbital_integral_hua_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.core_bound <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinatesStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField


theorem _root_.GlobalTheory.T.hermitian_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLtStatement

section

@[expose] public section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable

section

@[expose] public section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrableStatement

section

@[expose] public section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentity

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem core_integrable {W : Type} [Fintype W] {n M : ℕ} (hnM : 2 * n < M) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (hJ : ∀ w, (J w).IsHermitian) (hJd : ∀ w, (J w).det ≠ 0) {N : ℕ}
    (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (W → hermC n)) (hν : ν.IsAddHaarMeasure) :
    Integrable (coreC J μ (fun X => f (e X))) ν := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ
  have hcont := GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ
  have hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2 := by
    have : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hint := (GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have := hC b
  simpa [neg_div] using this

theorem integrable_starLoc_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ
  obtain ⟨Ψ, hΨ, hΨν⟩ := GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩ := GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M
  obtain ⟨N, e₀, he₀, he₀s, f, hP⟩ := hP
  obtain ⟨hνH, hνI⟩ := hΨν ν hν
  obtain ⟨hμH, hμI⟩ := hΦμ μ hμ
  let Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ := fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)
  have hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0 := fun w => by
    simpa using (map_ne_zero (ρ w)).2 ha
  have hJc : ∀ w, (Jc w).IsHermitian := fun w => by
    ext i j
    have h1 := hJ.1 i j
    have h2 := hcm.2.2.2 (τ w) (J j i)
    simp only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [h1] at h2
    rw [h2]
    rfl
  have hJd : ∀ w, (Jc w).det ≠ 0 := fun w => by
    simp only [Jc, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (hρa w)) ?_
    have : (J.map (τ w)).det = τ w J.det := by
      simpa using (RingHom.map_det (τ w) J).symm
    rw [this]
    exact (map_ne_zero (τ w)).2 hJ.2
  let e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ) := Φ.symm.trans e₀
  have he₂ : Continuous e₂ := he₀.comp hΦs
  have he₂s : Continuous e₂.symm := hΦc.comp he₀s
  have hcore := core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH
  have := hνI _ hcore
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b
  rw [coreC, ← hμI]
  unfold starLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show f (e₂ (Φ X)) * _ = P X * _
  have hph := GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X
  rw [hph, hP X]
  have h1 : e₂ (Φ X) = e₀ X := by simp [e₂]
  have h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w := funext (hΨ b)
  rw [h1, h2, hΦ X]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end
