module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorForm
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDeformationLiftSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecond

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open scoped ContDiff ComplexOrder

namespace GlobalTheory.ColLiftAut

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}

theorem isThetaFunO_smul (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem kernel_left (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ) (g : GA D S) {γ : GA D T}
    (hγ : γ ∈ GQ T) (h : GA D T) : thetaKO om g (γ * h) Φ = thetaKO om g h Φ := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hΦ)

theorem kernel_right (g : GA D S) (h k : GA D T) : thetaKO om g (h * k) Φ = thetaKO om g h (om (1, k) Φ) := by
  have e : ((g, h * k) : GA D S × GA D T) = (g, h) * (1, k) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]

theorem lift_continuous (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    Continuous fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  have := GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector ψ S T χS χT om hW hS ν 𝓕 hν h𝓕 ℂ
    (LinearMap.toSpanSingleton ℂ _ Φ) (fun x => isThetaFunO_smul hΦ x) φ hφ.cont hφ.left
  refine this.congr fun h => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [LinearMap.toSpanSingleton_apply, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end GlobalTheory.ColLiftAut

namespace GlobalTheory.ColLiftAut

theorem posDef_of_nodeIs {D : D7} {N : GlobalTheory.Grid.Node D} {ν q : ℕ} {Sp : D.what₂.Tau → SPar} (h : N.Is ν q Sp) (hq : q = 0) :
    ∀ τ, (gramAt D N.V τ).PosDef := fun τ =>
  GlobalTheory.RepsObj.gramAt_posDef (fun σ => by rw [h.sig σ, h.rank, hq]; simp) h.sigOK τ

end GlobalTheory.ColLiftAut
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteLiftZfin

open Matrix

theorem isCuspFun_of_posDef {D : D7} {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) (φ : GA D V → ℂ) :
    IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hτ : ∀ a, tauE D τ0 (star a) = starRingEnd ℂ (tauE D τ0 a) := D.sp.cm.cmUnram.2.1 (tauE D τ0)
  have h1 := congrArg (tauE D τ0) (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have hx : star (fun i => tauE D τ0 (C i ⟨0, hr⟩)) ⬝ᵥ (gramAt D V τ0 *ᵥ fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]

    simp only [gramAt, Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm
  have h2 : (fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    by_contra hne
    have := (hV τ0).dotProduct_mulVec_pos hne
    rw [hx] at this
    exact lt_irrefl _ this
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact (tauE D τ0).injective ((congrFun h2 i).trans (map_zero (tauE D τ0)).symm)

end GlobalTheory.DefiniteLiftZfin
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteUnitaryLiftFiniteAdeles

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefiniteLiftZfin
open Matrix
theorem definite_unitary_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ →
    (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
    IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧
      (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 hP hω hθ hΦ hS _ hH hF hφ
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  exact (hK.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ ⟨hφ, isCuspFun_of_posDef hS φ⟩ ⟨Φ, hΦ⟩).2.zfin
end GlobalTheory.DefiniteLiftZfin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_definite_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧ (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  first | exact @_root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | exact _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | (intros; apply _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistLiftModerateGrowth

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftGrowthDef
theorem lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'
end GlobalTheory.LiftGrowthDef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  first | exact @_root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | exact _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | (intros; apply _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationLevelEqConductor

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeilLevel
theorem weil_representation_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]
end GlobalTheory.WeilLevel
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_weil_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  first | exact @_root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | exact _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | (intros; apply _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ContDiff ComplexOrder
namespace GlobalTheory.ColLiftAut
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}
theorem thetaLift_isAutomorphicFunction (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    IsAutFun T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  refine ⟨fun γ hγ h => ?_, ?_, lift_continuous hW hΦ hS hν h𝓕 hφ⟩
  · simp only [kernel_left hW hΦ _ hγ]
  · obtain ⟨U, hU, hk⟩ := _root_.GlobalTheory.T.twist_weil_level_eq_conductor ψ S T χS χT om Φ hP hW hΦ
    refine ⟨U, hU, fun k hkU hkf h => ?_⟩
    simp only [kernel_right, hk k hkU hkf]
theorem thetaLift_isSmoothAutomorphicFunction (θ : InfFam D) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (hΦ : IsThetaFunO ψ S T Φ) (hS : ∀ τ, (gramAt D S τ).PosDef) (hT : ∀ τ, (gramAt D T τ).PosDef)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) :
    IsAutFunSm θ T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν :=
  { toIsAutFun := _root_.GlobalTheory.ColLiftAut.thetaLift_isAutomorphicFunction hP hW hΦ hS hν h𝓕 hφ.toIsAutFun
    smooth := _root_.GlobalTheory.T.twist_deformation_lift_smooth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    zfin := _root_.GlobalTheory.T.twist_definite_lift_finite_adeles ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    growth := _root_.GlobalTheory.T.twist_lift_moderate_growth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ }
end GlobalTheory.ColLiftAut
namespace GlobalTheory.ColLiftAut
theorem columnLift_isSmoothAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ φ hφ _
  have hW : IsWeilDatumO R.ψ (G.Xp j).V (G.Xp (j + 1)).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) (G.col t j).ω :=
    (hG.arrows.col t j hj).weil
  have hT : ∀ τ, (gramAt D (G.Xp (j + 1)).V τ).PosDef := posDef_of_nodeIs (hG.spaces.X j (by omega)) rfl
  have hSm : (∀ τ, (gramAt D (G.Xp j).V τ).PosDef) ∧ (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
    cases j with
    | zero =>
      exact ⟨posDef_of_nodeIs (hG.spaces.P D.R.m le_rfl) (by simp), ((hG.meas.P D.R.m le_rfl).1 rfl).1.1, ((hG.meas.P D.R.m le_rfl).1 rfl).2⟩
    | succ j' =>
      exact ⟨posDef_of_nodeIs (hG.spaces.X j' (by omega)) rfl, ((hG.meas.X j' (by omega)).1 trivial).1.1, ((hG.meas.X j' (by omega)).1 trivial).2⟩
  exact _root_.GlobalTheory.ColLiftAut.thetaLift_isSmoothAutomorphicFunction R.θ hPr hW hRB.inf hΦ hSm.1 hT hSm.2.1 hSm.2.2 hφ.1
end GlobalTheory.ColLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnLift_isAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | exact _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | (intros; apply _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction <;> assumption)
end
end
end
