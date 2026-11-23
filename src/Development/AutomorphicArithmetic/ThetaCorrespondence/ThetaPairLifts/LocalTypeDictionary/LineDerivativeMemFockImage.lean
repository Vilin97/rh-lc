module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaIntegralInterchange

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionTransfer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.Twist.RestrictionTransfer

theorem rest_transfer : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → (∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r x ≠ 0) →
    ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f r ⟨hinv, hsch⟩ ⟨x₀, hx₀⟩ f₁
  refine ⟨hinv, ?_⟩
  set a₀ : κ → mixedEmbedding.mixedSpace F := fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) with ha₀
  have hc : f a₀ ≠ 0 := by
    intro h; apply hx₀; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]; rw [← ha₀, h, zero_mul]
  let zz : (κ → AF F) → (κ → AF F) := fun x i =>
    (((x₀ i).1 - (x i).1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have hz1 : ∀ x i, (x i + zz x i).1 = (x₀ i).1 := by
    intro x i; show (x i).1 + ((x₀ i).1 - (x i).1) = _; ring
  have hz2 : ∀ x i, (x i + zz x i).2 = (x i).2 := by
    intro x i; show (x i).2 + 0 = _; simp
  have hev : ∀ x, (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + zz x) i)) = a₀ := by
    intro x; funext i; simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, ha₀]; rw [hz1]
  have hAt : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (zz x) := by
    intro x u hu
    have hu1 : u.1 = 0 := by
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
    funext i
    show ((u.1 * ((x₀ i).1 - (x i).1), u.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
    rw [hu1]; simp
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * Φ (x + zz x)
      map_add' := by intro Φ Ψ; funext x; simp [mul_add]
      map_smul' := by intro c Φ; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, L Φ ∈ GlobalTheory.WeilM.schA F κ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, h, hh, rfl⟩ := hΦ
      have : L (GlobalTheory.WeilM.pureA F g h) = g a₀ • GlobalTheory.WeilM.pureA F f₁ h := by
        funext x
        have e := hev x
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI] at e ⊢
        rw [e]
        have : (fun i => (x i + zz x i).2) = fun i => (x i).2 := funext fun i => hz2 x i
        rw [this]; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₁, h, hh, rfl⟩)
    | zero => simp
    | add Φ Ψ _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
    | smul c Φ _ h1 => rw [map_smul]; exact Submodule.smul_mem _ c h1
  have hLt : L (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
      f a₀ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
    funext x
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul]
    rw [hev x, hinv x (zz x) (hAt x)]; ring
  have hm := key _ hsch
  rw [hLt] at hm
  have := Submodule.smul_mem _ (f a₀)⁻¹ hm
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.Twist.RestrictionTransfer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivativeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


theorem _root_.GlobalTheory.T.skewSpaceLine_oneParam_fockDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  first | exact @GlobalTheory.LieLines.line_deriv | exact GlobalTheory.LieLines.line_deriv | (intros; apply GlobalTheory.LieLines.line_deriv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThOInjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem thO_injective : ∀ (D : D7) {n k : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → Mo.IsGood ψ' →
    ∀ {d : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (e : Fin k ≃ Fin d), G.det ≠ 0 →
    ∀ F₁ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k), ∀ F₂ ∈ GlobalTheory.WeilM.schA D.host.F (Fin n × Fin k),
      GlobalTheory.TripleRead.thO Mo ψ' G e F₁ = GlobalTheory.TripleRead.thO Mo ψ' G e F₂ → F₁ = F₂ := by
  intro D n k Xs Ws Mo ψ' χX χW om τ hH hG d G e hdet F₁ hF₁ F₂ hF₂ h
  obtain ⟨-, hstd, -, hdX, -, hdW, -⟩ := hH
  obtain ⟨T, hT, hTi⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Mo ψ' G e hG hstd hdX hdW hdet
  rw [← hT F₁ hF₁, ← hT F₂ hF₂, ← sub_eq_zero, ← map_sub] at h
  exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ hF₁ hF₂) h)

end GlobalTheory.ThetaTransformInj

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.LineStab
theorem ptF_one' {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := by
  have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [h1]
  simp only [ptF, pureTensorO, pureTensorL]
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem thO_zero' {m k d : ℕ} {D : D7} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    GlobalTheory.TripleRead.thO Mo ψ G e 0 = 0 := by
  funext x
  simp only [GlobalTheory.TripleRead.thO, GlobalTheory.WeilM.thetaSum, Pi.zero_apply]
  refine (tsum_congr fun ξ => ?_).trans tsum_zero
  exact mul_zero _

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem det_sgn_gram {D : D7} (ε : Bool) (M : HSp D) (h : (GlobalTheory.RealDict.sgE (D := D) ε • M.gram).det ≠ 0) :
    ((sgn ε M).gram).det ≠ 0 := by
  have hg : (sgn ε M).gram = -(GlobalTheory.RealDict.sgE (D := D) ε • M.gram) := by
    cases ε <;> ext i j <;> simp [GlobalTheory.RealDict.sgE, sgn, HSpace.gram]
  rw [hg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

end GlobalTheory.RealDict.LineStab

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeMemFockImage

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.RealDict.LineStab
theorem line_derivative_mem_fock_image : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ := by
  intro hPr D ψ θ hstd hθ ε M X A B χS χT ω eS eT hW hExp Xs Ws Mo ψ' χX χW om τ hPH hPR Φ hinj hrange hFock N hN γ hγ f hf f₁ hD
  have hψ := hPR.psi.symm
  subst hψ
  obtain ⟨P, hPN, rfl⟩ := Submodule.mem_map.1 hf
  obtain ⟨f₀, r, hvac, hf0, hΦ⟩ := hFock
  obtain ⟨h, Y, hY, hγh, hder⟩ := GlobalTheory.T.skewSpaceLine_oneParam_fockDerivative D ψ θ ε M X A B χS χT ω eS eT hθ hW hExp Ws hPR.JW γ hγ
  set Q := ∑ t, GlobalTheory.RealQuot.actT ε A B eS t (Y t) P with hQ
  have hQN : Q ∈ N := Submodule.sum_mem _ fun t _ => hN ⟨(t, Y t), hY t⟩ P hPN
  have hne : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext hc
    have h1 := (hΦ 1).2
    rw [h0, thO_zero', ptF_one'] at h1
    exact hf0 h1.symm
  have hr : ∃ x, r x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, fun h0 => hx (by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, h0])⟩
  have hR1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r := GlobalTheory.Twist.RestrictionTransfer.rest_transfer _ (Φ 1) r (hΦ 1).1 hne f₁
  have hT : ∀ t : ℝ, GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r)) =
      ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) := by
    intro t
    have e1 := hPR.transp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) (hΦ P).1.2 1 (h t)
    rw [conjU_one', ← hγh t] at e1
    rw [e1, (hΦ P).2]
  have key : GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) =
      GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r) := by
    funext x
    have a := _root_.GlobalTheory.T.theta_interchange_derivative_pure hPr D Xs Ws Mo ψ χX χW om τ hPH hPR.good γ hγ (Φ P) f₁ r (hΦ P).1 hR1 hD (sgn ε M).gram
      (Equiv.refl (Fin X.rank)) x
    have e2 : (fun t : ℝ => GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r)) x) =
        fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) x := funext fun t => by rw [hT t]
    rw [e2] at a
    rw [a.unique (hder f₀ hvac P x), (hΦ Q).2]
  have hdet : ((sgn ε M).gram).det ≠ 0 := det_sgn_gram ε M (hPR.JX ▸ hPH.2.2.2.1)
  have heq := GlobalTheory.ThetaTransformInj.thO_injective D Xs Ws Mo ψ χX χW om τ hPH hPR.good (sgn ε M).gram (Equiv.refl (Fin X.rank)) hdet
    _ hR1.2 _ (hΦ Q).1.2 key
  exact ⟨Q, hQN, (GlobalTheory.ArchCancel.eq_of_tens_eq _ r (hΦ P).1.1 hr f₁ (Φ Q) heq).symm⟩
end GlobalTheory.RealDict.LineStab
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.fock_image_line_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.LineStab.line_derivative_mem_fock_image | exact _root_.GlobalTheory.RealDict.LineStab.line_derivative_mem_fock_image | (intros; apply _root_.GlobalTheory.RealDict.LineStab.line_derivative_mem_fock_image <;> assumption)
end
end
end
