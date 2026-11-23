module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
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
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistPolarizationDatumLieDerivative

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAtStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.KapXLine.exists_line | exact GlobalTheory.KapXLine.exists_line | (intros; apply GlobalTheory.KapXLine.exists_line <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.LieEq

theorem exists_op {S S' Pi : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Pi] [Module ℂ Pi]
    (N : Submodule ℂ S) (N' : Submodule ℂ S') (p : S →ₗ[ℂ] Pi) (p' : S' →ₗ[ℂ] Pi) (δ : S →ₗ[ℂ] S) (δ' : S' →ₗ[ℂ] S')
    (h : ∀ f ∈ N, ∀ f' ∈ N', p f = p' f' → p (δ f) = p' (δ' f')) :
    ∃ A : Pi →ₗ[ℂ] Pi, (∀ f ∈ N, A (p f) = p (δ f)) ∧ ∀ f' ∈ N', A (p' f') = p' (δ' f') := by
  let L : (N × N') →ₗ[ℂ] Pi := p ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  let L₁ : (N × N') →ₗ[ℂ] Pi := p ∘ₗ δ ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ δ' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  have hk : LinearMap.ker L ≤ LinearMap.ker L₁ := by
    intro x hx
    simp only [LinearMap.mem_ker, L, L₁, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype] at hx ⊢
    have e : p (x.1 : S) = p' (-(x.2 : S')) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
    have := h _ x.1.2 _ (N'.neg_mem x.2.2) e
    rw [this, map_neg, map_neg, neg_add_cancel]
  let A₀ : LinearMap.range L →ₗ[ℂ] Pi := (LinearMap.ker L).liftQ L₁ hk ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hA₀ : ∀ x, A₀ ⟨L x, LinearMap.mem_range_self L x⟩ = L₁ x := by
    intro x
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨A, hA⟩ := LinearMap.exists_extend A₀
  have hA' : ∀ x, A (L x) = L₁ x := fun x => by
    rw [← hA₀ x, ← hA]; rfl
  refine ⟨A, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hA' (⟨f, hf⟩, 0)
    simpa [L, L₁] using this
  · have := hA' (0, ⟨f', hf'⟩)
    simpa [L, L₁] using this

end GlobalTheory.SquareAgree.LieEq

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ), IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.ThetaInj.theta_inj | exact GlobalTheory.ThetaInj.theta_inj | (intros; apply GlobalTheory.ThetaInj.theta_inj <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsDatumDerivativeSecondFactorEqSumPure

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.SquareAgree.LieDat
theorem isDatum_derivative_second_factor_eq_sum_pure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hDer T m f f₁ φ hf hact hD Φ'D hΦ'D
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hM : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hW : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have hev : ∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v := fun i =>
    ⟨(hf i).2.1, Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => by
      by_contra h; exact hv ((hf i).2.2 v h))⟩
  have hval : ∀ (t : ℝ) u, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)))) =
      ωB (1, oneP θ X τ Y t) Φ (cB u) := by
    intro t u
    have h := (hO.weilB _ Φ hD 1 (oneP θ X τ Y t)).2 u
    rwa [GlobalTheory.LocWeilAct.conjU_one', ← hγ t] at h
  have hnew : IsDatum Γ.M' ψ cB (∑ i, pure (f₁ i) (φ i)) Φ' := by
    refine ⟨Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA (f₁ i) (φ i) (hev i).1
      (((hev i).2.and hM.std).mono fun v hv => hv.1.trans hv.2), fun u => ?_⟩
    have h1 := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hstd hM hW γ hL m f f₁ φ hev hact u
    have h2 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i))))) (Φ' (cB u)) 0 := by
      simp only [hval]
      exact hDer (cB u)
    exact h1.unique h2
  exact GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq Γ.M' ψ hstd cB Φ'D _ Φ' hΦ'D hnew
end GlobalTheory.SquareAgree.LieDat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.twist_polarization_datum_derivative_second : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W₁ X → ℂ), IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M'.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M' ψ cB (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M' ψ cB Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  first | exact @_root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | exact _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure | (intros; apply _root_.GlobalTheory.SquareAgree.LieDat.isDatum_derivative_second_factor_eq_sum_pure <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationMatchLieDerivative

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.LieEq
theorem polarization_match_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀' ∈ algF ψ θ false A₁ B, IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₀' → ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ'D ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀'D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Φ'D Φ' → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → IsDatum Γ.M' ψ cB Φ₀'D Φ₀' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf Φ'D Φ₀'D := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hTr R Rf hM Pi rf rl p p' _ τ Y hY
    Φ _ Φ' _ Φ₀ _ Φ₀' _ hD hD₀ ΦD _ Φ'D _ Φ₀D _ Φ₀'D _ hd1 hd2 hd3 hd4 hPM
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw Bs Γ Xc om om' hTr γ hγ
  obtain ⟨δ', hδ'⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hTr γ hγ
  obtain ⟨Aop, hA, hA'⟩ := exists_op (Γ.M.Pol Bs.ψ Bs.emb) (Γ.M'.Pol Bs.ψ Bs.emb) R.p R.p' δ δ'
    (fun f hf f' hf' hpp => hM.real.lie γ hγ f hf f' hf' _ _ (hδ f hf).2 (hδ' f' hf').2 hpp)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hs⟩ := hPM
  have e1 := _root_.GlobalTheory.T.twist_polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ Φ' hD T m f
    (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) (hΦ ▸ hd1) Φ'D hd2
  have e2 := _root_.GlobalTheory.T.twist_polarization_datum_derivative_second hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTr τ Y γ hγt hγ Φ₀ Φ₀' hD₀ T m' f'
    (fun j => δ' (f' j)) φ' hf' (fun j => (hδ' _ (hf' j).1).2) (hΦ' ▸ hd3) Φ₀'D hd4
  refine ⟨T, hT, m, m', fun i => δ (f i), φ, fun j => δ' (f' j), φ', fun i => ⟨(hδ _ (hf i).1).1, (hf i).2⟩,
    fun j => ⟨(hδ' _ (hf' j).1).1, (hf' j).2⟩, e1, e2, ?_⟩
  have := congrArg (TensorProduct.map Aop LinearMap.id) hs

  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
  simpa only [hA _ (hf _).1, hA' _ (hf' _).1] using this
end GlobalTheory.SquareAgree.LieEq
end
end
end
end
