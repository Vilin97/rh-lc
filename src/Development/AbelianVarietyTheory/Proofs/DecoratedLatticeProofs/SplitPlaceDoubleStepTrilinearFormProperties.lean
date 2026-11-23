module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalDoublingIntegralOddCase
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGLStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AconvSingleList

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep.IdempotentCombination

variable {D : D7}

section Idem
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

end GlobalTheory.TriStep.IdempotentCombination

namespace GlobalTheory.TriStep

theorem aconv_single_list {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  show d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b)) = d
  calc d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b))
        = d.sum (fun g a => Finsupp.single g a) := by
          congr 1; funext g a; rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    _ = d := Finsupp.sum_single d

theorem comb_aconv_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {A T : HSp D}
    (c d : WO A T →₀ ℂ) (hc : Q.Away c)
    (hd : ∀ u ∈ d.support, IsHalf ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) u) (g : WO A T → ℂ) :
    comb ψ A T (aconv [c, d]) g = comb ψ A T c (comb ψ A T d g) := by
  rw [GlobalTheory.TriStep.IdempotentCombination.comb_aconv_cons c [d] ?_ g, aconv_single_list]
  intro x hx y hy
  rw [aconv_single_list] at hy
  have hy' : IsHalf (Q.q.e + cA D Q.q.e) y := hd y hy
  refine GlobalTheory.HeisComb.symplO_half A T (1 - (Q.q.e + cA D Q.q.e)) (Q.q.e + cA D Q.q.e) x y ?_ ?_ (hc x hx) hy'
  · rw [map_sub, map_one, GlobalTheory.TriStep.IdempotentCombination.cA_idem]
  · rw [sub_mul, one_mul, GlobalTheory.TriStep.IdempotentCombination.idem_sq, sub_self]

theorem valK_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hcon Ξ₁ Ξ₂ d₁ d₂ hd₁ hd₂ O₁ O₂ hO₁ hO₂ f hf
  have hσc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol
  let P₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let P₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₁ : SB (Matrix Q.n₁ Q.n₀ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₂ : SB (Matrix Q.n₂ Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have e₁ : flatBF S.s₁ (T₁ O₁) = U₁ P₁ := hU₁ O₁ P₁ (by
    rw [hO₁, (hun Q.n₁ Q.n₀ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)])
  have e₂ : flatFB S.s₂ (T₂ O₂) = U₂ P₂ := hU₂ O₂ P₂ (by
    rw [hO₂, (hun Q.n₂ Q.n₁ Q.n₀ (Q.c + 1) (σ + 1)).2.1 (by omega) (by omega)])
  obtain ⟨ΞO, hΞO, eΛ⟩ := hcon P₁ P₂
  have hΞO' : ∀ q, ΞO.1 q = R₁.1 q.1 * R₂.1 q.2 := fun q => by
    rw [hΞO]; exact (hun Q.n₁ Q.n₀ Q.n₂ 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) ψ Q.n₁ Q.n₀ Q.n₂).1 S.B.A S.J.W₀ S.B'.A
    Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ d₁ d₂ Ξ₁ R₁ Ξ₂ R₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) ΞO hΛ hd₁ hd₂ rfl rfl (fun q => rfl) hΞO'
  have hbc := GlobalTheory.ProdLocInv.biComb_comp ψ S.B.A S.J.W₀ S.B'.A c₁ d₁ (aconv [c₁, d₁]) c₂ d₂ (aconv [c₂, d₂])
    (comb_aconv_away Q c₁ d₁ hc₁ hd₁.1) (comb_aconv_away Q c₂ d₂ hc₂ hd₂.1) (Λ ΞO)
  have hom₁ : S.s₁.om (1, 1) = 1 := map_one _
  have hom₂ : S.s₂.om (1, 1) = 1 := map_one _
  simp only [GlobalTheory.TriStep.valK, Dbl2.val, Dbl2.con, GlobalTheory.TriStep.rTrans_one]
  rw [hom₁, hom₂, Module.End.one_apply, Module.End.one_apply, e₁, e₂, eΛ, ← hbc, hbi]

end GlobalTheory.TriStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotent

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

namespace GlobalTheory.TriStep


open GlobalTheory.NormalFramePeriod in
theorem valK_nEquiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ _ Λ _ Ξ g hg f hf
  have hc : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, rTrans_one] at this
  unfold valK
  rw [per_flagN S.B' ψ hψ _ f hc.1 (GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)),
    GlobalTheory.LocBesChar.psiBes_isLoc D Q.k (ofSplit Q.q) ψ Q.ψk Q.char σ S.B' _ Q.n₂ (Q.c + 1) Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)]

end GlobalTheory.TriStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  first | exact @GlobalTheory.TriStep.valK_nEquiv | exact GlobalTheory.TriStep.valK_nEquiv | (intros; apply GlobalTheory.TriStep.valK_nEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValue

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
namespace GlobalTheory.TriStep

theorem val_eq_tensorVal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hCL T hT Φ₁ Φ₂ f
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨hcol, hrow, hop, ⟨m, Ψ, Φ₀, hfl⟩, hsum⟩ :=
    GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.μ₁ Φ₁ Φ₂
  obtain ⟨Ξ, hΞ, hΛΞ⟩ := hCL ⟨_, hcol⟩ ⟨_, hrow⟩
  refine ⟨m, Ψ, Φ₀, hfl, ?_⟩
  have e1 : S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1 = valK S Q c₁ c₂ φ Λ Ξ f.1 := by
    unfold Dbl2.val Dbl2.con valK
    rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
      map_one, map_one, rTrans_one, Module.End.one_apply, Module.End.one_apply, hU₁ Φ₁ ⟨_, hcol⟩ rfl,
      hU₂ Φ₂ ⟨_, hrow⟩ rfl, hΛΞ]
  have e2 : Ξ = ∑ i, GlobalTheory.LocFlat.CFac.prodSB (Ψ i) ⟨_, hop (Φ₀ i)⟩ := by
    apply Subtype.ext
    funext x
    rw [hΞ, hsum m Ψ Φ₀ hfl x]
    simp [Submodule.coe_sum, Finset.sum_apply, GlobalTheory.LocFlat.CFac.prodSB_apply]

  rw [e1, ← hT, e2, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) (Ψ i)) ⟨_, hop (Φ₀ i)⟩
  exact (LinearMap.congr_fun h f).symm

end GlobalTheory.TriStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  exact @GlobalTheory.TriStep.val_eq_tensorVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormProperties

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

theorem isBiTheta_add' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ}
    (hf : IsBiTheta ψ A S A' f) (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem isBiTheta_zero' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem isBiTheta_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] (Λ : SB (X × Y) →ₗ[ℂ] (WO A S → WO S A' → ℂ))
    (h : ∀ a b, IsBiTheta ψ A S A' (Λ (GlobalTheory.LocFlat.CFac.prodSB a b))) (Ξ : SB (X × Y)) : IsBiTheta ψ A S A' (Λ Ξ) := by
  have hmem : Ξ ∈ Submodule.span ℂ (Set.range fun q : SB X × SB Y => GlobalTheory.LocFlat.CFac.prodSB q.1 q.2) := by
    rw [GlobalTheory.T.span_schwartzBruhatProduct_eq_top X Y]; trivial
  have key : ∀ c : ℂ, IsBiTheta ψ A S A' (Λ (c • Ξ)) := by
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      intro c
      have e : c • GlobalTheory.LocFlat.CFac.prodSB q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSB (c • q.1) q.2 := by
        change c • GlobalTheory.LocFlat.CFac.prodSBBil X Y q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSBBil X Y (c • q.1) q.2
        rw [map_smul, LinearMap.smul_apply]
      rw [e]; exact h _ _
    | zero => intro c; rw [smul_zero, map_zero]; exact isBiTheta_zero'
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add (f := _)]; exact isBiTheta_add' (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  simpa using key 1

theorem tri : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ φ hφ
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hCL := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hν : Q.ν.IsAddHaarMeasure := Q.unitVol.1
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B Q.F.s Q.F.F₀ Q.F.G₀ Q.F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂ Q.F.bes'
  have hjac : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link (ofSplit Q.q) S.B S.B' S.l]; exact Q.F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _ (Q.c + 1 + 1)
    Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _ (Q.c + 1)
    Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac hC₂ Q.F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL Q.k (ofSplit Q.q) Q.ν hν ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL Q.F.s Q.F.s_ne
    _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hψkc : Continuous Q.ψk := by
    obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
    exact (hψk Q.ψk Q.char).1
  have hΛθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) := by
    haveI := GlobalTheory.SplitWeil.t2Space Q.k
    haveI : NonarchimedeanAddGroup Q.k := ⟨fun V hV => by
      obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
      exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
        GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
    haveI : TotallyDisconnectedSpace Q.k := inferInstance
    haveI : ∀ n n' : Type, T2Space (Matrix n n' Q.k) := fun n n' => inferInstanceAs (T2Space (n → n' → Q.k))
    haveI : ∀ n n' : Type, TotallyDisconnectedSpace (Matrix n n' Q.k) :=
      fun n n' => inferInstanceAs (TotallyDisconnectedSpace (n → n' → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₁ Q.n₀ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₁ → Q.n₀ → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₂ Q.n₁ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₂ → Q.n₁ → Q.k))
    refine isBiTheta_of_prod Λ fun Ξ₁ Ξ₂ => ?_
    obtain ⟨φ₀, φ₀', hφ₀⟩ := GlobalTheory.ContractionLocal.exists_normPair Q.ψk Q.ν hψkc hν Q.n₁
    obtain ⟨Ξ', h1, h2⟩ := hΛe (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁) (GlobalTheory.ContractionLocal.rowTens φ₀' Ξ₂)
    have e : Ξ' = GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂ :=
      Subtype.ext (funext fun q => by rw [h1, GlobalTheory.ContractionLocal.contr_tens, hφ₀, mul_one]; rfl)
    rw [← e, ← h2]
    exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hstd _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (hU₁.theta _) (hU₂.theta _)).1
  have hθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hstd _ _ _ _ (hΛθ Ξ) c₁ c₂
  obtain ⟨T, hT⟩ := GlobalTheory.T.doubleThetaLiftValue_bilinear D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ hΛθ
  have key : ∀ Ξ₁ Ξ₂ (f : GlobalTheory.TriStep.space Q), (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T Ξ₁ Ξ₂ f =
      GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f.1 := fun Ξ₁ Ξ₂ f => hT _ f
  refine ⟨GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.rep Q, (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T, GlobalTheory.TriStep.smooth Q,
    fun y f => rfl, GlobalTheory.T.mem_space_of_typed_automorphic D ψ σ S Q, ⟨fun Ψ₁ => ⟨fun Ψ₂ g hg v => ?_, fun g Ψ Ψ' v h => ?_⟩, fun g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ => ?_⟩,
    GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe T hT, fun Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f => ?_⟩
  · rw [key, key]
    exact GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ _ g hg v.1 v.2
  · rw [key, key]
    exact GlobalTheory.T.local_bimodel_translation D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ Ψ' h (hθ _) v.1 v.2
  · ext1 f
    rw [key, key]
    exact GlobalTheory.T.doubleThetaLiftValue_invariant_middleGL D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ (hθ _) f.1 f.2
  · rw [key]
    exact GlobalTheory.TriStep.valK_comb D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f.1 f.2

end GlobalTheory.TriStep
end
end
end
