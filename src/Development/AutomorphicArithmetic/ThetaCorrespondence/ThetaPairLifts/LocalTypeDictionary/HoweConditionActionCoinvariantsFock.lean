module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsDarbouxBasisOfSymplecticPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeMemFockImage
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealLieDerivativeMemCoinvariants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceStableMaximalCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFockModelIntertwiner

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
namespace GlobalTheory.RealDict.FockMap
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section Gauss
open scoped Classical
open GlobalTheory.VacLn
end Gauss
variable {D : D7}
variable {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
  {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
section Main
variable (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (hX : Xs.J = sgE (D := D) ε • M.gram)
  (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
  (hM : Mo.IsGood ψ)
include hψ hθ hX hW hM
variable {Dr : Matrix (Fin M.rank) (Fin X.rank) (AE D) →
    (SInf D.host.F (Fin M.rank × Fin X.rank) →L[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank))}
  (hD : ∀ u, At (evI D.host.F) u → ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank),
    ActsD (evI D.host.F) (Mo.heisLine ψ u) f (Dr u f))
include hD
end Main
theorem exists_fock_model_map : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧ GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT _ _ Xs Ws Mo ψ' χX χW om τ hP hR
  obtain ⟨hCM, hStd, -, -, -, -, -, -, -, -, -, hcX, hcW⟩ := hP
  obtain rfl := hR.psi
  exact exists_fockMap_of Mo hψ hθ A B hCM hStd hR.JX hR.JW hR.good (fun w => (hcX w).1) (fun w => (hcW w).1) hR.cart
end GlobalTheory.RealDict.FockMap
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

theorem _root_.GlobalTheory.T.exists_fock_model_intertwiner : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧ GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ := by
  first | exact @_root_.GlobalTheory.RealDict.FockMap.exists_fock_model_map | exact _root_.GlobalTheory.RealDict.FockMap.exists_fock_model_map | (intros; apply _root_.GlobalTheory.RealDict.FockMap.exists_fock_model_map <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilModelRationalStructure

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
namespace GlobalTheory.RealDict.CompactCoinv
section Oriented
variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
end Oriented
section Theta
end Theta
section Reading
variable {D : D7}
end Reading
end GlobalTheory.RealDict.CompactCoinv
namespace GlobalTheory.RealDict
open GlobalTheory.RealDict.CompactCoinv
theorem sub_mem_map_coinv_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT hω he Xs Ws Mo ψ' χX χW om τ hP hR Φ _ hrange hΦ k hk f hf f₁ hA
  obtain ⟨f₀, r, hvac, h0, hr⟩ := hΦ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, hW, -⟩ := hP
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  have hc : sgE (D := D) ε ≠ 0 := by cases ε <;> simp [sgE]
  obtain ⟨g, hgk, hg⟩ := exists_conjU M hc hR.JX k
  obtain ⟨P', hP', hm⟩ := moves_sgn hθ A B hω he hvac h0 g (mem_GinfC_of_conj g _ hg hk.1) (fun t => by
    obtain ⟨t', h1, h2, -⟩ := hR.cart (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E)))
    obtain rfl := eq_of_conj_over t t' _ h1
    rw [infMat_of_conj hθ hCM g _ hg _ _ h1, ← h2]
    exact hk.2 _) P
  have h1 : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := Subtype.ext (Units.ext rfl)
  have h2 := hR.transp _ (hr P).1.2 g 1
  rw [hgk, h1, (hr P).2] at h2
  have h3 := thO_inj Mo hψ (Formalism.L2.Theta.gram_det_ne (sgn ε M))
    (om_mem_schA hW (k, 1) (hr P).1.2) (hr P').1.2 (h2.trans (Eq.trans hP' (hr P').2.symm))
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply h0
    rw [← GlobalTheory.LieScalar.ptF_one (ψ := ψ) (θ := θ) (frSgn ε A) B f₀, ← (hr 1).2]
    funext x
    simp [GlobalTheory.TripleRead.thO, thetaSum, Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  have h4 : (f₁ : _ → ℂ) = Φ P' := eq_of_tens (hr P).1.1 hr0 ((hA r (hr P).1).symm.trans h3)
  rw [DFunLike.coe_injective h4, ← map_sub]
  exact ⟨_, hm, rfl⟩
end GlobalTheory.RealDict
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

theorem _root_.GlobalTheory.T.weil_model_rational_structure_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | exact _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | (intros; apply _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRealPlaceCorrespondence

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
namespace GlobalTheory.RealDict
theorem real_place_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ' ∧
    (∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j) ∧ Xs.J.det ≠ 0 ∧
    (∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j) ∧ Ws.J.det ≠ 0 ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX M.rank ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW X.rank ∧
    IsHecke D.host.F D.host.E χX ∧ IsHecke D.host.F D.host.E χW ∧ Mo.IsWeil ψ' χX χW om ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Xs.J.map (τ w).1) (Xs.θ w)) ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • Ws.J.map (τ w).1) (Ws.θ w)) ∧
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧
      (∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ) ∧
      (∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ) ∧
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ) := by
  intro hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨Xs, Ws, Mo, ψ', χX, χW, om, τ, hH, hR⟩ := _root_.GlobalTheory.T.exists_darboux_basis_of_symplectic_pair hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨Φ, hi, hr, hF⟩ := _root_.GlobalTheory.T.exists_fock_model_intertwiner hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hH
  have hH : PublishedHyps D Xs Ws Mo ψ' χX χW om τ := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact ⟨Xs, Ws, Mo, ψ', χX, χW, om, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, Φ, hi, hr,
    _root_.GlobalTheory.T.fock_image_line_stable hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hi hr hF,
    _root_.GlobalTheory.T.theta_subspace_stable_maximal_compact hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hi hr hF,
    _root_.GlobalTheory.T.real_lie_derivative_mem_coinvariants hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hi hr hF,
    _root_.GlobalTheory.T.weil_model_rational_structure_alt hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hi hr hF⟩
end GlobalTheory.RealDict
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

theorem _root_.GlobalTheory.T.twist_real_place_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ' ∧
    (∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j) ∧ Xs.J.det ≠ 0 ∧
    (∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j) ∧ Ws.J.det ≠ 0 ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX M.rank ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW X.rank ∧
    IsHecke D.host.F D.host.E χX ∧ IsHecke D.host.F D.host.E χW ∧ Mo.IsWeil ψ' χX χW om ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Xs.J.map (τ w).1) (Xs.θ w)) ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • Ws.J.map (τ w).1) (Ws.θ w)) ∧
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
      Function.Injective Φ ∧ LinearMap.range Φ = Mo.Pol ψ' τ ∧
      (∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
          f₁ ∈ N.map Φ) ∧
      (∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ) ∧
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ) := by
  first | exact @_root_.GlobalTheory.RealDict.real_place_correspondence | exact _root_.GlobalTheory.RealDict.real_place_correspondence | (intros; apply _root_.GlobalTheory.RealDict.real_place_correspondence <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweConditionActionCoinvariantsFock

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
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
namespace GlobalTheory.HoweFockReal
theorem howe_condition_action_coinvariants_fock : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  intro hH hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨Xs, Ws, Mo, ψ', χX, χW, om, τ, hcm, hstd, hX, hXd, hWs, hWd, hrX, hrW, hhX, hhW, hwe, hcX, hcW,
    Φ, hinj, hran, hLT, hKT, hLS, hKS⟩ := _root_.GlobalTheory.T.twist_real_place_correspondence hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH D.host.F D.host.E D.sp.cm.sig hcm M.rank X.rank Xs Ws Mo ψ' χX χW om hstd hX hXd hWs hWd
    hrX hrW hhX hhW hwe τ hcX hcW
  have key : ∀ N : Submodule ℂ (PolF D X.rank M.rank),
      GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
      GlobalTheory.RealQuot.coinv ε A B eT ≤ N → GlobalTheory.Published.ThetaSubInf Mo ψ' τ om (N.map Φ) := by
    intro N hs hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hran]
      exact LinearMap.map_le_range
    · intro γ hγ f hf f₁ h
      exact Submodule.map_mono hc (hLS γ hγ f hf f₁ h)
    · intro k hk f hf f₁ h
      exact Submodule.map_mono hc (hKS k hk f hf f₁ h)
    · intro γ hγ f hf f₁ h
      exact hLT N hs γ hγ f hf f₁ h
    · intro k hk f hf f₁ h
      exact hKT N hs k hk f hf f₁ h
  have hne : ∀ N : Submodule ℂ (PolF D X.rank M.rank), N ≠ ⊤ → N.map Φ ≠ Mo.Pol ψ' τ := by
    intro N hN h
    apply hN
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, hran]
  refine ⟨⟨L, fun m N hN hk => hL m (fun i => (N i).map Φ) ?_ fun i => key _ (hk i).1 (hk i).2⟩, ?_⟩
  · intro i j hij
    exact (Submodule.map_strictMono_of_injective hinj) (hN hij)
  · intro N N' hs hc hN hs' hc' hN' hsup
    apply hsum _ _ (key N hs hc) (key N' hs' hc') (hne N hN) (hne N' hN')
    rw [← Submodule.map_sup, hsup, Submodule.map_top, hran]
end GlobalTheory.HoweFockReal
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  first | exact @_root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | exact _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | (intros; apply _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock <;> assumption)
end
end
end
