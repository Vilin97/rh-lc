module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolic
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeriesStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolicStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧ ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ), φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)), ∀ 𝓕 𝓕₀ : Set (GA E (m + 1)),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤ → ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) 𝓕₀ μ ∧
      ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) h ∂μ =
        (c : ℂ) * ∫ h in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x h ∂μ := by
  first | (exact @GlobalTheory.RSnmUnfold.rs_unfold) | (exact GlobalTheory.RSnmUnfold.rs_unfold) | (intros; apply GlobalTheory.RSnmUnfold.rs_unfold  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectorsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  first | (exact @GlobalTheory.RSnmCells.unfolded_cells_eq) | (exact GlobalTheory.RSnmCells.unfolded_cells_eq) | (intros; apply GlobalTheory.RSnmCells.unfolded_cells_eq  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmUnf

theorem rs_nm_partialL_eq_div : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  intro E _ _ _ n m σ σ' hm hmn hσ hσ' T hψ hT hT'
  obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = m₀ + r + 1 + 1 := ⟨n - m₀ - 2, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, _ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + r + 1 + 1) σ (by omega) hσ T hT
  obtain ⟨β, _ℓ', _Φ', _J', _η', π', _ω', _φ', hβ, hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + 1) σ' (by omega) hσ' T hT'
  subst hπ hπ'
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 hσ
  have hu' : π'.IsUnitary := (CG.isUnitary_mk π').1 hσ'
  have hfd : ∀ a : ℕ, ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E a)) (𝓕₀ : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
    intro a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hsub : (GlobalTheory.CellDec.NE E a : Set (GA E a)) ⊆ ((ratGL E a).range : Set (GA E a)) := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E a).range : Set (GA E a))) hsub
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
    obtain ⟨𝓕₀, -, -, h𝓕₀⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E a)
    exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕₀, h𝓕 _, h𝓕₀ _⟩
  obtain ⟨μ₁, hμ₁, 𝓕₁, -, h𝓕₁, -⟩ := hfd (m₀ + r + 1 + 1)
  obtain ⟨μ, hμ, 𝓕, 𝓕₀, h𝓕, h𝓕₀⟩ := hfd (m₀ + 1)
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₁ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((β w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ 𝓕 h𝓕
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + r + 1 + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let βe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + 1) → ℂˣ := fun w => if h : w ∉ T then β ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hβe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, βe w.1 = β w := fun w => dif_pos w.2
  have hsatσ : ∀ {a : ℕ} (ρ : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hαe ⟨w, hw⟩, hα ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (βe w)) := fun w hw => by
    rw [hβe ⟨w, hw⟩, hβ ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨φ, φ', κ, hφ, hφ', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ :=
    GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations E m₀ r T hψ π π' hu hu' αe βe hsat hsat'
  obtain ⟨F, hF, hC⟩ := GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors E m₀ r T hψ π π' hu hu' αe βe φ φ' κ hφ hφ' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  letI : μ.IsHaarMeasure := hμ
  obtain ⟨c, hc, hU⟩ := GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic E m₀ r μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.exp_integral_entire_real_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  have hlt : m₀ + 1 < m₀ + r + 1 + 1 := by omega
  have hent := GlobalTheory.RSnmGood.rsIntegral_entire_good (by omega) hlt
    (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu hφ) (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu' hφ') hF μ h𝓕
  refine ⟨fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' s h ∂μ,
    fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, fun s => (hent.2 s).differentiableAt,
    (differentiable_const _).mul hdiff, ?_, ?_⟩
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
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + r + 1 + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + 1)) => ((βe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((β w i : ℂˣ) : ℂ) := by funext w i; rw [hβe w]
    have hf1 := hfin x hx
    have hf1' := hfin' x hx
    rw [← e1] at hf1
    rw [← e1'] at hf1'
    obtain ⟨dd1, dd2, eq⟩ := hid x hx hf1 hf1'
    obtain ⟨-, eU⟩ := hU π π' hu hu' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x dd1 dd2
    rw [e1] at hf1
    rw [e1'] at hf1'
    obtain ⟨P, hP, hS⟩ := GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (by omega : m₀ + 1 ≤ m₀ + r + 1 + 1) α β x hx hq hf1 hf1'
    have hsum : (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin (m₀ + 1) → ℤ),
        l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (αe w.1 i : ℂ))
          (fun i => (βe w.1 i : ℂ)) x v) = P := by
      simp only [hαe, hβe]
      exact hS.tsum_eq
    have hJ : (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) ≠ 0 := by
      intro h0
      have := (hreal x).2 hfpos
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hval : (∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' (x : ℂ) h ∂μ) /
        ((c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) = P := by
      rw [eU, eq, hsum]
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      field_simp
    have hP' : HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal)
        (sat (CG.mk π) w.1) ((sat (CG.mk π') w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P := by
      simp only [← hα, ← hβ]
      exact hP
    simpa only [hval] using hP'

end GlobalTheory.RSnmUnf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntireStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
end
end
