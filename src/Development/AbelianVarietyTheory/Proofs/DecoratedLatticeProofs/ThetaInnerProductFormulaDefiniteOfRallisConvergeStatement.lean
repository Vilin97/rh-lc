module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegrStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartanStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftCoefCont

theorem continuous_l2_weil_action_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hc Q₁ Q₂
  obtain ⟨-, -, -, -, -, hom, -, -, hpt, -, -⟩ := h
  have e : ∀ g : GA D (Wc D i), l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) =
      GlobalTheory.RawLift.thetaIP μ 𝓧 (ptAt R i σ BW f Q₂) (ω (1, g) (ptAt R i σ BW f Q₁)) := fun g => by
    rw [← GlobalTheory.RawLift.FockCoef.thetaInner_star, GlobalTheory.RawLift.GoodModulus.thetaInner_eq_star_l2, star_star]
  simp only [e]
  exact GlobalTheory.RawLift.FockCoef.continuous_coef hom hc (hpt Q₂) (hpt Q₁)

end GlobalTheory.LiftCoefCont

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_weilCoefficient_fockVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  first | exact @GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | exact GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | (intros; apply GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  first | exact @GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | exact GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | (intros; apply GlobalTheory.PrincipalLevelFock.levW_fix_ptAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftFockVec

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem ptAt_isFockVec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h'
  obtain ⟨⟨hψ, hv⟩, -⟩ := hlv
  have hθ : IsInfFam R.θ := hv.inf
  obtain ⟨⟨p, hp⟩, -⟩ := hv.norm
  obtain ⟨-, hθf, hS, hvac⟩ := GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h p.1 p.2 hp
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ)
  set Ap := aPlusAll (heisO R.ψ (Vc D i) (Wc D i)) R.θ (fun τ => cplxO ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) (cart (R.MW i σ) τ)) (R.BV i) BW with hAdef
  have hadd : ∀ g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (g + g') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (a • g) :=
    fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (Ap k g) :=
    fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i' j g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (Ap j g) = Ap j (Ap i' g) :=
    fun i' j _ h => aPlus_comm' hψ hθ i'.1 _ hS hT j.1 _ h
  have Aadd : ∀ i' g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      Ap i' (g + g') = Ap i' g + Ap i' g' :=
    fun i' _ _ h h' => aPlus_add hψ hθ i'.1 _ _ h h'
  have Asm : ∀ i' (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (a • g) = a • Ap i' g :=
    fun i' a _ h => aPlus_smul hψ hθ i'.1 _ _ a h
  have hpt' : ∀ Q', ptAt R i σ BW f Q' = pureTensorL Ap f Q' := fun _ => rfl
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ c' : FVar D (Wc D i).rank (Vc D i).rank → ℂ, ∀ Q',
      annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) z (pureTensorL Ap f Q') =
        pureTensorL Ap f (∑ k, c' k • MvPolynomial.pderiv k Q') := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir (Vc D i) (Wc D i) τ z k.1 (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir (Vc D i) (Wc D i) τ (cplxO 1 (cart (R.MW i σ) τ) z) k.1
          (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ))), fun Q' => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hθf (hvac τ z) Q'
  refine ⟨hpt Q, Q.totalDegree + 1, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ Q' : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ,
      l.foldr (fun p g => annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ p.1 (cplxO 1 (cart (R.MW i σ) p.1)) p.2 g)
          (pureTensorL Ap f Q) = pureTensorL Ap f Q' ∧
        ∀ n : FVar D (Wc D i).rank (Vc D i).rank →₀ ℕ, Q.totalDegree < n.degree + l.length → Q'.coeff n = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨Q, rfl, fun n hn => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h2 : Q.totalDegree < n.degree := by simpa using hn
      exact h2
    | cons q l ih =>
      obtain ⟨Q', hQ', hQc⟩ := ih
      obtain ⟨c', hc'⟩ := hder q.1 q.2
      refine ⟨∑ k, c' k • MvPolynomial.pderiv k Q', ?_, fun n hn => ?_⟩
      · rw [List.foldr_cons, hQ', hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c' Q' (Q.totalDegree - l.length)
          (fun n' hn' => hQc n' (by omega)) n ?_
        simp only [List.length_cons] at hn
        omega
  obtain ⟨Q', hQ', hQc⟩ := key l
  have hQ0 : Q' = 0 := MvPolynomial.ext _ _ fun n => by
    simpa using hQc n (by rw [hl]; omega)
  show l.foldr _ (ptAt R i σ BW f Q) = 0
  rw [hpt', hQ', hQ0, map_zero]

end GlobalTheory.LiftFockVec

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaDatum_fockVectors_areFockVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  first | exact @GlobalTheory.LiftFockVec.ptAt_isFockVec | exact GlobalTheory.LiftFockVec.ptAt_isFockVec | (intros; apply GlobalTheory.LiftFockVec.ptAt_isFockVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConverge

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IPFConv

theorem integrableOn_of_quot {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsMulLeftInvariant]
    {𝓕 : Set (GA D V)} (hFD : IsFundamentalDomain (GQ V) 𝓕 μ) {φ : GA D V → ℂ}
    (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ)
    (h : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ)) : IntegrableOn φ 𝓕 μ := by
  have h1 := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hFD).1 (memLp_one_iff_integrable.2 h)
  rw [hφ.lift_descend] at h1
  exact memLp_one_iff_integrable.1 h1

theorem thetaKO_left_snd {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    {φ : WO V W → ℂ} (hf : IsThetaFunO ψ V W φ) (h : GA D V) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ W) (fun g => thetaKO ω h g φ) := fun γ hγ g => by
  have e : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
  show thetaKO ω h (γ * g) φ = thetaKO ω h g φ
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ φ hf)

theorem innerProductFormulaC_of_convergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hConv hpar
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  intro ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v₁ v₂ Q₁ Q₂
  intro φ₁ φ₂ F₁ F₂ Z pt
  have hCore : GlobalTheory.Hk3.Core R F := hL.1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω := hL.2.2.2.2.2.1
  obtain ⟨hwitt, hrank, cA, hSet, hA0⟩ := GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan R F hCore hpar i σ
  have hFo₁ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁
  have hFo₂ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₂
  have hW := hCore.models.νW i
  haveI : (R.νW i).IsHaarMeasure := hW.1.1
  have hFDW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := hW.2
  haveI : ν.IsHaarMeasure := hν.1.1
  have hFDV : IsFundamentalDomain (GQ (Vc D i)) 𝓕 ν := hν.2
  have hF₁ : F₁ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₁ hU₁ v₁
  have hF₂ : F₂ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₂ hU₂ v₂
  have hL₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₁ := (Submodule.mem_inf.1 hF₁).2.2.1
  have hL₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₂ := (Submodule.mem_inf.1 hF₂).2.2.1
  have hKP : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1)
      true (fun _ => True) (fun _ => True) (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂)
      (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂) :=
    ⟨ω, φ₁, φ₂, hω, hFo₁, hFo₂, trivial, trivial, fun _ _ => rfl, fun _ _ => rfl, μ, 𝓧, hμ, fun _ => rfl⟩
  obtain ⟨hC₁, hC₂, hInt, hEq⟩ := hConv R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1) D.R.t
    cA true (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂) (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂)
    (R.νW i) ν F₁ F₂ hSet (Or.inl hwitt) hrank hKP inferInstance inferInstance hF₁ hF₂
  have hpetW : ∀ u₁ u₂ : GA D (Wc D i) → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₁ →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₂ → GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) u₁ u₂ = petW R i u₁ u₂ :=
    fun u₁ u₂ h₁ h₂ => GlobalTheory.AutomorphicL2Unitary.pet_eq hFDW h₁ h₂
  have hlift₁ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₁) F₁ = upLift R i ω φ₁ F₁ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₁.1 h) hL₁
  have hlift₂ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₂) F₂ = upLift R i ω φ₂ F₂ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₂.1 h) hL₂
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv at hC₁ hC₂
  rw [hlift₁] at hC₁ hEq
  rw [hlift₂] at hC₂ hEq
  have hZeq : ∀ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
      conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) = Z g := fun g => by
    rw [hpetW (rTr (Wc D i) g F₁) F₂ (hL₁.mul_right g) hL₂]
  have hpc := GlobalTheory.T.petersson_principal_level_continuous_right_invariant hP R F hCore i σ
  have hZc : Continuous Z :=
    (GlobalTheory.T.continuous_weilCoefficient_fockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hμ Q₁ Q₂).mul
      (Complex.continuous_conj.comp (hpc.2 U₁ hU₁ U₂ hU₂ _ _).1)
  have hZi : Integrable Z (R.νW i) := hInt.congr (ae_of_all _ hZeq)
  have hZr : ∀ g, ∀ k ∈ levW R i, Z (g * k) = Z g := fun g k hk => by
    have hk1 := GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁ k hk
    have e : (((1 : GA D (Vc D i)), g * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, g) * (1, k) := by simp
    show l2 μ 𝓧 (ω (1, g * k) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) (g * k) F₁) F₂) =
      l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
    rw [e, map_mul, Module.End.mul_apply, hk1, (hpc.2 U₁ hU₁ U₂ hU₂ _ _).2 g k hk]
  obtain ⟨hfin, hdis⟩ := GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals D R.θ hSet.2.2.2.1 (Wc D i) hSet.2.2.2.2.1 _ (R.νW i) hW.1 hpc.1 Fr hFr mR
    hmR Z hZc hZi hZr
  refine ⟨fun h => ?_, ?_, hfin, ?_⟩
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) :=
      fun γ hγ g => by
        have e1 : thetaKO ω h (γ * g) φ₁ = thetaKO ω h g φ₁ := thetaKO_left_snd hω hFo₁.1 h γ hγ g
        have e2 : F₁ (γ * g) = F₁ g := hL₁ γ hγ g
        show thetaKO ω h (γ * g) φ₁ * starRingEnd ℂ (F₁ (γ * g)) = _
        rw [e1, e2]
    exact integrableOn_of_quot hFDW hLp (hC₁.1 h)
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Vc D i))
        (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) := fun γ hγ g => by
      have e1 : upLift R i ω φ₁ F₁ (γ * g) = upLift R i ω φ₁ F₁ g := hC₁.2.1 γ hγ g
      have e2 : upLift R i ω φ₂ F₂ (γ * g) = upLift R i ω φ₂ F₂ g := hC₂.2.1 γ hγ g
      show upLift R i ω φ₁ F₁ (γ * g) * starRingEnd ℂ (upLift R i ω φ₂ F₂ (γ * g)) = _
      rw [e1, e2]
    exact integrableOn_of_quot hFDV hLp (hC₁.2.integrable_mul_conj hC₂.2)
  · have hvol : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Vc D i) ν = (ν 𝓕).toReal := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hFDV]
    have hpV : GlobalTheory.Cusp.petersson (Vc D i) ν (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) =
        l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) := GlobalTheory.AutomorphicL2Unitary.pet_eq hFDV hC₁.2.1 hC₂.2.1
    have hI : ∫ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
        conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) ∂(R.νW i) = ∫ g, Z g ∂(R.νW i) :=
      integral_congr_ae (ae_of_all _ hZeq)
    rw [hpV, hvol, hI, hdis] at hEq
    exact hEq

end GlobalTheory.IPFConv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConvergeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaInnerProductFormulaDefinite_of_rallisConvergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  first | exact @GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | exact GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | (intros; apply GlobalTheory.IPFConv.innerProductFormulaC_of_convergent <;> assumption)
end
end
