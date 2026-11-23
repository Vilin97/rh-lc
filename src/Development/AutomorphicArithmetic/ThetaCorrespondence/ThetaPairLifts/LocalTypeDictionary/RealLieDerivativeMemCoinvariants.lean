module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaSumAlongLineYDirection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace

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

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    change f' (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a i)) * g' y = f' x₀ * g' y
    congr 1
    apply congrArg f'
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x₀ i)
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplaceStatement

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

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  first | exact @GlobalTheory.TwistRest.restTr | exact GlobalTheory.TwistRest.restTr | (intros; apply GlobalTheory.TwistRest.restTr <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLineDerivVanishesOnCoinvariants

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
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.OmegaDer
section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Mat
variable {D : D7}
theorem line_deriv_theta_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω he Xs hJ f₀ hf γ hγ
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_line M hc Xs hJ γ hγ
  refine ⟨g, h1, fun P => ?_⟩
  obtain ⟨Z, hZ, hd⟩ := der_line (V := sgn ε M) (ω := ω.toSgn ε) hθ hω (frSgn ε A) B he hf
    (fun t => (ofSgn ε M).symm (g t)) ((continuous_ofSgn_symm ε M).comp h2)
    (fun s t => by rw [h3, map_mul]) h4
  refine ⟨_, ?_, hd P⟩
  refine Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, Z τ, ?_, P, ?_⟩
  · rw [← GlobalTheory.SgnIdent.lieAt_sgn ε M τ]
    exact hZ τ
  · rw [neg_smul, ← sub_eq_add_neg]
    rfl
end GlobalTheory.OmegaDer
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
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.theta_lineDeriv_vanishes_on_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  first | exact @_root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | exact _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | (intros; apply _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealLieDerivativeMemCoinvariants

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
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.RealDict
theorem lie_derivative_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro hPr D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs Ws Mo ψ' χX χW om τ hP hR Φ hinj hrange hF γ hγ f hf f₁ hact
  obtain ⟨hcm, hstd, hherm, hdetX, hskew, hdetW, -, -, -, -, hweil, -, -⟩ := hP
  have hpsi := hR.psi
  subst hpsi
  obtain ⟨f₀, r, hvac, hne, hFr⟩ := hF
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  obtain ⟨g, hg, hder⟩ := _root_.GlobalTheory.T.theta_lineDeriv_vanishes_on_coinvariants hPr D ψ' θ hψ hθ ε M X A B χS χT ω eS eT hW hE Xs hR.JX f₀ hvac γ hγ
  obtain ⟨Q, hQ, hQd⟩ := hder P
  have hGM : M.gram.det ≠ 0 := by
    intro h0
    apply hdetX
    rw [hR.JX, Matrix.det_smul, h0, mul_zero]
  have hG : (sgn ε M).gram.det ≠ 0 := by
    cases ε
    · exact hGM
    · change (-M.gram).det ≠ 0
      rw [Matrix.det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGM
  obtain ⟨T, hT, hTinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl _) hR.good hstd hdetX hdetW hG
  have hΦ1 : Φ 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans (map_zero Φ).symm))
  have hRf₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r := GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace _ f₁ r (hFr 1).1 hΦ1
  have hRQ := (hFr Q).1
  have hone : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1).1.1 = 1
    rw [GlobalTheory.TripleRead.toUX_val, GlobalTheory.WeilVacMove.mt_one]
    exact Matrix.submatrix_one_equiv _
  have key : ∀ x, GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r) x =
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl _) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r) x := by
    intro x
    have h1 := _root_.GlobalTheory.T.thetaSum_differentiable_along_line hPr Mo ψ' χX χW om hstd hR.good hweil γ hγ (Φ P) f₁ r (hFr P).1 hact
      (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
    have h2 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ' (GlobalTheory.TripleRead.ptO (sgn ε M).gram (Equiv.refl _) x)
        (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r))) =
        ω (g t, 1) (ptF (V := sgn ε M) ψ' θ (frSgn ε A) B f₀ P) x := by
      intro t
      have h3 := hR.transp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) (hFr P).1.2 (g t) 1
      rw [hg t, hone, (hFr P).2] at h3
      exact congrFun h3 x
    simp only [h2] at h1
    have h4 := h1.unique (hQd x)
    rw [(hFr Q).2]
    exact h4
  obtain ⟨d, hd⟩ : ∃ d : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank), d = f₁ - Φ Q := ⟨_, rfl⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f₁ r - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ Q) r := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, sub_mul, hd]
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin X.rank) := by
    rw [e1]; exact sub_mem hRf₁.2 hRQ.2
  have hT0 : T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) d r) = 0 := by
    rw [e1, map_sub, hT _ hRf₁.2, hT _ hRQ.2, funext key, sub_self]
  have hz := hTinj _ hmem hT0
  have hr : ∃ x₀, r x₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) r = 0 := funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hcon]
    have h2 := (hFr 1).2
    rw [h0, ← hT 0 (zero_mem _), map_zero, GlobalTheory.LieScalar.ptF_one] at h2
    exact hne h2.symm
  have hfeq : f₁ = Φ Q := by
    obtain ⟨x₀, hx₀⟩ := hr
    rw [← sub_eq_zero, ← hd]
    refine DFunLike.ext _ _ fun y => ?_
    let z : Fin M.rank × Fin X.rank → AF D.host.F := fun i => LinearMap.inl D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i)))
    have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) z := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * z i = 0
      refine Prod.ext ?_ ?_
      · show u.1 * (z i).1 = 0
        rw [hu1, zero_mul]
      · show u.2 * (z i).2 = 0
        simp [z]
    have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F ((x₀ + z) i)) = y := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((x₀ i).1 + (z i).1) = y i
      rw [map_add (f := _)]
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i) + InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x₀ i))) = y i
      rw [RingEquiv.apply_symm_apply, add_sub_cancel]
    have h5 := congrFun hz (x₀ + z)
    have h6 : r (x₀ + z) = r x₀ := (hFr 1).1.1 x₀ z hzAt
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.zero_apply] at h5
    rw [hev, h6] at h5
    simpa [hx₀] using h5
  rw [hfeq]
  exact Submodule.mem_map_of_mem hQ
end GlobalTheory.RealDict
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

theorem _root_.GlobalTheory.T.real_lie_derivative_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
          f₁ ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants | exact _root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants | (intros; apply _root_.GlobalTheory.RealDict.lie_derivative_mem_coinvariants <;> assumption)
end
end
end
