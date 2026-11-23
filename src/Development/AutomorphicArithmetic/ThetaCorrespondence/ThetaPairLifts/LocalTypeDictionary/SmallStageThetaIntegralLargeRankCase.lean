module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelIntegrableOnFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Order.Star.Rat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtLargeParameterThetaIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageNonzeroAtFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageKernelIntegrablePolynomialBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageSmallBig

theorem tmul_ne_zero {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem nontrivial_left {Pr Pf Pi : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra hP0
  rw [not_nontrivial_iff_subsingleton] at hP0
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, v, huv⟩ := exists_pair_ne Pi
  exact huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])

end GlobalTheory.StageSmallBig

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelIntegrableOnFundamentalDomainStatement

section

namespace I195MixedCoordinates_74ccb184947b854a25a0cacd

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_74ccb184947b854a25a0cacd

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm


theorem _root_.GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain : GlobalTheory.Published.SiegelSetUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → p < M.rank →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ∀ τ₀ : D.what₂.Tau,
    (∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r) (μ' : Measure (Mx D X.rank r))
      (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → (_root_.I195MixedCoordinates_74ccb184947b854a25a0cacd.source d) X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0) →
    ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  first | exact @GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO | exact GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO | (intros; apply GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockModelAdmissiblePolynomialExists

section

@[expose] public section

section
noncomputable section
namespace GlobalTheory.GoodFock
section Ring
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset
variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}
end Ring
section Poly
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
end Poly
section Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
end Theta
section Quot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {M X : HSp D}
end Quot
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem exists_admissible_fock_polynomial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]
end Main
end GlobalTheory.GoodFock
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

theorem _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @_root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | exact _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | (intros; apply _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallStageThetaIntegralLargeRankCase

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallBig
theorem smallStage_thetaIntegral_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q0 A A' WW X hX _ => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, -, -, hD⟩ := hd W i j p q0 A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨P0, hP0⟩ := _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, (∀ h, IntegrableOn (X.ker' W.ψ W.θ t P0 h) X.fd' X.m') ∧ X.I' W.ψ W.θ t P0 ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, hk'⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p q0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    haveI : Nontrivial Pr := nontrivial_left e
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P1, rfl⟩ := hq' x
    obtain ⟨hint, hker⟩ := hP0 _ _ hTr hInf _ _ _ _ _ _ _ hm _ hf'
    have hint' := hint X.m' X.fd' hIs.meas'
    have hne : pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) ≠ 0 := fun h0 => by
      have h1 := hker h0 P1
      rw [hr' _ hf'] at h1
      exact e.map_ne_zero_iff.2 (tmul_ne_zero hx hy) h1
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 := hint' h
      simp only [hk'] at h1
      exact h1
    · rw [← eI']
      exact _root_.GlobalTheory.ConvThetaNe.convergent_theta_integral_ne_zero hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hTr X.m' X.fd' hIs.meas'
        _ _ _ _ _ _ _ hm _ (Submodule.subset_span ⟨_, P0, hf', rfl⟩) hint' hne
  exact ⟨P0, fun t => (key t).1, fun t => (key t).2⟩
end GlobalTheory.StageSmallBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | exact _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | (intros; apply _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank <;> assumption)
end
end
end
