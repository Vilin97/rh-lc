module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchange

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.QStep

theorem gl₂_embX_eq_embA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  intro D ψ σ S Q g
  obtain ⟨a₀, ha⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (ofSplit Q.q) Q.F.F₂ g
  exact ⟨a₀, GlobalTheory.LocGrp.isLoc_unique (ofSplit Q.q)
    (GlobalTheory.NormalFramePeriod.isLoc_embA (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' ha) (Q.loc₂ _), ha⟩

end GlobalTheory.QPl.QStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  exact @GlobalTheory.QPl.QStep.gl₂_embX_eq_embA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecond

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOmb

theorem isComp_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by
  intro t a ha
  have := Q.comp₂ t a ha
  rw [MonoidHom.inv_apply] at this
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, Circle.coe_inv, inv_inv]

theorem isLoc_one {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsLoc Q.F.F₁ (1 : GA D S.J.W₀) (1 : GL Q.n₁ Q.k) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [GlobalTheory.MixModel.mt_one]
  · rw [GlobalTheory.MixModel.mt_one, Units.val_one, Matrix.mul_one, Q.F.F₁.βγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_one_of_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {g : GL Q.n₂ Q.k}
    {a₀ : GA D S.B'.A} (hloc : (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g) (y : WO S.J.W₀ S.B'.A)
    (hy' : IsHalf (1 - (Q.q.e + cA D Q.q.e)) y) : actO S.J.W₀ S.B'.A 1 a₀ y = y := by
  have hsupp := GlobalTheory.LocGrp.suppAt_iff.1 hloc.1
  have he := Q.q.split
  set f : AE D := Q.q.e + cA D Q.q.e with hf
  have hce : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, he.1]
  have hff : f * (1 - f) = 0 := by
    rw [hf]; linear_combination (-1 : AE D) * he.1 - hce - 2 * he.2.1
  have hfy : f • y = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← hy' i j, ← mul_assoc, hff, zero_mul]
  have hz : HMul.hMul (Formalism.L2.Theta.mt S.B'.A a₀ - 1) (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := by
    rw [← hsupp, Matrix.smul_mul, ← Matrix.mul_smul]
    have h0 : ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) • (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := hfy
    rw [h0, Matrix.mul_zero]
  simp only [actO, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  exact hz

theorem biComb_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) :
    biComb ψ A S A' c₁ c₂ C u =
      ∑ x ∈ c₁.support, (c₁ x * ψ (symplOH A S u x)) • GlobalTheory.SeeSaw.comb ψ S A' c₂ (C (u + x)) := by
  funext v
  simp only [biComb, GlobalTheory.SeeSaw.comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem weil_last_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  intro D ψ σ S Q c₁ c₂ hAway Λ hbi g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ u
  have hcomm : ∀ G, IsThetaFunO ψ S.J.W₀ S.B'.A G →
      S.omb (1, a₀) (GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ G) = GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ (S.omb (1, a₀) G) := by
    intro G hG

    simp only [GlobalTheory.SeeSaw.comb, map_sum, map_smul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [S.weilb.om_heis 1 a₀ y G hG, actO_one_of_away Q hloc y (hAway y hy)]

  rw [biComb_eq_sum, biComb_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  obtain ⟨T₂, hT₂, hΛ⟩ := hbi.2 Ξ₁ (u + x)
  have e1 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (u + x) = T₂ Ξ₂ :=
    funext fun v => hΛ Ξ₂ _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e2 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (u + x) = T₂ Ξ₂' :=
    funext fun v => hΛ Ξ₂' _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e3 : S.omb (1, a₀) (T₂ Ξ₂) = T₂ Ξ₂' := by
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ (isComp_inv Q)
      (isComp_inv Q) Q.n₂ Q.n₁ Q.F.F₁ Q.F.F₂ T₂ hT₂ 1 1 a₀ g (isLoc_one Q) hloc Ξ₂ Ξ₂' ?_
    rw [hΞ, inv_inv]
    simp
  rw [e1, e2, hcomm _ (hT₂.theta _), e3]

end GlobalTheory.LastOmb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecondStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  first | exact @GlobalTheory.LastOmb.weil_last_local | exact GlobalTheory.LastOmb.weil_last_local | (intros; apply GlobalTheory.LastOmb.weil_last_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TriStep.valK_gl₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ h₁ h₂ φ hφ Λ hΛ g Ξ₁ Ξ₂ Ξ₂' hΞ hC f hf
  obtain ⟨a₀, ha, hloc⟩ := (GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange) D ψ σ S Q g
  have hop := (GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second) D ψ σ S Q c₁ c₂ h₂ Λ hΛ g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ
  have hf0 : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, GlobalTheory.TriStep.rTrans_one] at this
  have hF := GlobalTheory.SeeSawLastValue.contAut_biLift (GlobalTheory.SeeSaw.biAct_all D) S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ hC
  have hB3 := ((GlobalTheory.SeeSaw.biAct_all D) ψ _ _ _ _ _ _ _ S.oma S.omb S.weila S.weilb _ hC).2.2.1
  have hshift : biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂'))) =
      rTrans a₀ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)))) := by
    funext h
    simp only [biLift, rTrans]
    congr 1; funext h₁; congr 1; funext h₀; congr 1
    have e : ((h₁, h * a₀) : GA D S.J.W₀ × GA D S.B'.A) = (h₁, h) * (1, a₀) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    refine congrArg (fun X => S.omb (h₁, h) X 0) ?_
    funext v
    rw [hB3]
    refine congrArg (fun X => S.oma (h₀, h₁) X 0) ?_
    funext u
    rw [hop u]
  have hc : Q.c + 1 = 2 * σ + 1 := Q.F.bes'.1
  have hexp : ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) = 0 := by
    rw [hc]; push_cast; ring
  rw [hexp, Real.rpow_zero, Complex.ofReal_one, one_mul]
  unfold GlobalTheory.TriStep.valK
  rw [hshift, ← ha]
  exact GlobalTheory.Core.Mi.per_rTrans D ψ σ S.B' _ f a₀ hψ hF hf0
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.local_bimodel_translation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  first | exact @GlobalTheory.TriStep.valK_gl₂ | exact GlobalTheory.TriStep.valK_gl₂ | (intros; apply GlobalTheory.TriStep.valK_gl₂ <;> assumption)
end
end
