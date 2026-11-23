module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import GroundTheory.AutomorphicForms.ReductionMeasure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
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
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTopStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransformStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.exists_bump_shintani_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  first
  | exact @GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | exact GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | (intros; apply GlobalTheory.JSW.BumpShintani.exists_bump_shintani <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPosStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittakerStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
open GlobalTheory.MirTower GlobalTheory.CuspGeneric GlobalTheory.RSJ GlobalTheory.ZUnf in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  have := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    have : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOutsideOfConductor

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul


open GlobalTheory.CuspRep.CuspidalL2GL in
theorem exists_fundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ 𝓕₀ : Set (GA E n), IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕₀ μ := by
  intro E _ _ n μ _
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hsub : (GlobalTheory.CellDec.NE E n : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E n) := DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E n).range : Set (GA E n))) hsub
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E n)
  exact ⟨𝓕, h𝓕 _⟩

end GlobalTheory.ZEul
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul.Smooth

theorem zint_eq_mul_partialL_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro E _ _ _ a σ σ' ha hσ hσ' T hTs hψ hT hT'
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ ha hσ T hT
  obtain ⟨α', _ℓ', _Φ', _J', _η', π', ω', _φ', hα', hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ' ha hσ' T hT'
  subst hπ hπ'
  obtain ⟨μ₀, hμ₀, 𝓕₁, h𝓕₁⟩ : ∃ (μ : Measure (GA E (m + 1))) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E (m + 1))),
      IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
    haveI : DiscreteTopology (ratGL E (m + 1)).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E (m + 1)
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E (m + 1)).range
    exact ⟨Measure.haar, inferInstance, 𝓕, h𝓕 _⟩
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α' w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let αe' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α' ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hαe' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe' w.1 = α' w := fun w => dif_pos w.2
  have hsatσ : ∀ (ρ : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hs : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe w.1) = sat (CG.mk π) w.1 := fun w => by
    rw [hαe w]; exact hα w
  have hs' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe' w.1) = sat (CG.mk π') w.1 := fun w => by
    rw [hαe' w]; exact hα' w
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hs ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (αe' w)) := fun w hw => by
    rw [hs' ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨b, hb1, hbN, hbC, hbF⟩ := GlobalTheory.T.exists_bump_shintani_alt E m T hψ
  obtain ⟨φ, hφR, hU, hK, hW⟩ := hbF π αe hsat
  obtain ⟨φ', hφR', hU', hK', hW'⟩ := hbF π' αe' hsat'
  obtain ⟨hφ0, hφ0', N, Φ, hN, hΦc, hΦs, hΦr, hΦp, hC2⟩ := GlobalTheory.ZEul.unfolded_bump_eq E m T hTs hψ b hb1 hbN hbC π π' ω ω' hω hω' hωc hωc' αe αe'
    hsat hsat' φ φ' hφR hφR' hU hK hU' hK' hW hW'
  refine ⟨N, Φ, π, π', φ, φ', rfl, rfl, hφR, hφR', hφ0, hφ0', hN, hΦc, hΦs, ?_, ?_⟩
  · intro ℓ hℓ
    have hl : ℓ = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    exact hΦr
  intro μ hμ 𝓕 h𝓕
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.ZEul.exists_fundamentalDomain_NE E (m + 1) μ
  obtain ⟨c, hc, hC1⟩ := GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker E m μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC2 μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.T.exp_integral_differentiable_real_re_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  refine ⟨fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe' w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α' w i : ℂˣ) : ℂ) := by funext w i; rw [hαe' w]
    have hf1 : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1]; exact hfin x hx
    have hf1' : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe' w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1']; exact hfin' x hx
    obtain ⟨hd, hd', e12, e11, e22⟩ := hid x hx hf1 hf1'
    have z12 := (hC1 π π' ω ω' hω hω' hωc hωc' φ φ' hφR hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd').2
    have z11 := (hC1 π π ω ω hω hω hωc hωc φ φ hφR hφR N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd).2
    have z22 := (hC1 π' π' ω' ω' hω' hω' hωc' hωc' φ' φ' hφR' hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd' hd').2
    have A12 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe' w.1) x hx hq hf1 hf1').tsum_eq
    have A11 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe w.1) x hx hq hf1 hf1).tsum_eq
    have A22 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe' w.1) (fun w => αe' w.1) x hx hq hf1' hf1').tsum_eq
    simp only [hs, hs'] at A12 A11 A22
    refine ⟨?_, ?_, ?_⟩
    · rw [z12, e12, A12]; ring
    · rw [z11, e11, A11]; ring
    · rw [z22, e22, A22]; ring

end GlobalTheory.ZEul.Smooth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergLStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ Filter Topology Formalism.UG

theorem _root_.GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | exact GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | (intros; apply GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth <;> assumption)
end
end
