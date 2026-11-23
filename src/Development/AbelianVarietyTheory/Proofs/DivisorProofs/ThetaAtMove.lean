module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitarySelfDualLatticeGridDoublingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberEqProdLocalGridBasesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberEqProdLocalGridBasesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulArrowVacuaProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulArrowVacuaProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  first | exact @GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA | exact GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA | (intros; apply GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have w2' := rd_vac W.ψ_std W.θ_is A₁ AV₁ w2
  have key : IsVacF W.ψ W.θ A₁ (frSum AV AV₁) (box2 (ρ.vT i j) (rd _ _ (ρ.vX i j))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    let o := GlobalTheory.BiTransfer.sumDec (spV G i j) (spV₁ G i j)
    refine ⟨o.isThetaFunO_boxT w1.1 w2'.1, fun τ z => ?_⟩
    have h1 := w1.2 τ (o.qA.map (tauE D τ) * z)
    have h2 := w2'.2 τ (o.qB.map (tauE D τ) * z)
    have e1 : o.qA.map (tauE D τ) = prL (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qA_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prL, Matrix.one_apply, apply_ite (tauE D τ)]
    have e2 : o.qB.map (tauE D τ) = prR (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qB_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prR, Matrix.one_apply, apply_ite (tauE D τ)]
    unfold annih at h1 h2 ⊢
    rw [GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e1]; exact prL_cart AV AV₁ τ),
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e2]; exact prR_cart AV AV₁ τ)]
    funext x
    have k1 := congrFun h1 (o.resT _ x).1
    have k2 := congrFun h2 (o.resT _ x).2
    simp only [GlobalTheory.MixModel.OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at k1 k2 ⊢
    linear_combination (rd _ _ (ρ.vX i j)) (o.resT _ x).2 * k1 + (ρ.vT i j) (o.resT _ x).1 * k2
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacuaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  first | exact @GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | exact GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | (intros; apply GlobalTheory.TopFlipVacB.vac_eq_smul_vacB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtMove

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7}

theorem om_fockF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) {h : GA D X} (hh : h ∈ GfC X)
    {f : WO M X → ℂ} (hf : IsFinF ψ θ ε A B f) (c : ℂ) (P) :
    fockF ψ θ ε A B (c • ω (1, h) f) P = c • ω (1, h) (fockF ψ θ ε A B f P) := by
  have e : ω.toSgn ε (1, h) = ω (1, h) := by simp [GlobalTheory.Grid.WRep.toSgn]
  have h1 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (S := GlobalTheory.Grid.sgn ε M) (hk := one_mem _)
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (hk := hh)
  have := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ _ X χ χ' _ hω hθ (frSgn ε A).cart _ A.onb _ B.cart _ B.onb _ 1 h
    (fun τ => by rw [h1, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h1, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.one_mul]) f hf.1 P).2
  rw [e] at this
  exact (GlobalTheory.FiniteFock.pureTensorO_smul _ _ _ _ _ _ _ _ _ _ _).trans (congrArg (c • ·) this.symm)

theorem om_compare {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' χ₁ χ₁' : (AE D)ˣ →* Circle} {ω ω₁}
    (hω : IsWeilDatumO ψ S X χ χ' ω) (hω₁ : IsWeilDatumO ψ S X χ₁ χ₁' ω₁) {h : GA D X} {y : (AE D)ˣ} (hy : IsDetRoot X h y)
    {f} (hf : IsThetaFunO ψ S X f) : ω₁ (1, h) f = ((χ₁ y : ℂ) * (χ y : ℂ)⁻¹) • ω (1, h) f := by
  rw [GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ S X χ χ' χ₁ χ₁' ω ω₁ hω hω₁ 1 h 1 y (by simp [IsDetRoot]) hy f hf]
  simp [splitFacO]

theorem thetaAt_move {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' : (AE D)ˣ →* Circle} {ω}
    (hω : IsWeilDatumO ψ S X χ χ' ω) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS) (hX : Submodule.IsFullLattice D.host.E ΛX)
    {a : AE D} (ha : a * a = a) (hc : a * cA D a = 0) (hinf : infPart D a = 0) {b b' Φ f : WO S X → ℂ} (hb : IsThetaFunO ψ S X b)
    {h : GA D X} (hfx : ∀ x : WO S X, IsHalf a x ∨ IsHalf (cA D a) x → actO S X 1 h x = x) {c : ℂ} (hc0 : c ≠ 0)
    (e : ω (1, h) b = c • b')
    (hf : IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b Φ f) :
    IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b' Φ (c⁻¹ • ω (1, h) f) := by
  letI := hS
  letI := hX
  have := GlobalTheory.ThetaBaseMove.isThetaAt_move hω
    (fun f₀ h₀ Tm hTm Ψ hΨ => GlobalTheory.DiagLiftFix.isTheta_placeModel hω.std inferInstance inferInstance ha hc hinf h₀ Tm hTm Ψ hΨ) hb 1 h
    (inv_ne_zero hc0) hfx hf
  rwa [e, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}



theorem exists_move (hL : L.Is μ₀) (hst : ∀ t, SquareStanding G t) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {i j : Fin D.R.m}
    {X : TriG G i j} (hX : TopGrid W i j X) {νH}
    (hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) νH (locPl G))
    {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) :
    ∃ h ∈ GfC (spX G i j), ∃ (cA cB : ℂ) (y : (AE D)ˣ), cA ≠ 0 ∧ cB ≠ 0 ∧ ∀ t,
      IsLinA B t i j ρ (X.e t) (locFst B t X) (cA⁻¹ • X.ω t (1, h) (X.f t)) ∧
      IsLinB B t i j ρ (X.e t) (locSnd B t X) ((cB * (L.xi t y : ℂ))⁻¹ • X.ω' t (1, h) (X.f' t)) := by
  obtain ⟨h, hh, Λ, hΛ, hfx, hmv, tA, tB⟩ := GlobalTheory.T.exists_finiteUnitary_selfDual_lattice_grid_doubling (G := G) hL i j
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hX
  have x7 := x6 AV AV₁ hV hV₁
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  have sW₁ := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := by have := hI.rigW.1; rwa [x3] at this
  have vA := hI.isVac
  have vB := hI.isVac'
  rw [x1, x3, x4, x7] at vA
  rw [x2, x3, x5, x7] at vB
  have eA : ∀ t, (X.ω t).toSgn true (1, h) = X.ω t (1, h) := fun t => by simp [GlobalTheory.Grid.WRep.toSgn]
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ (hk := hh)
  have mA := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ (isSelfDualC_neg sW)) _ vA
  have mB := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil' μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ sW₁) _ vB
  obtain ⟨cA', hcA, kA⟩ := GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tA _ mA
  obtain ⟨cB, hcB, kB⟩ := GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tB _ mB
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ h
  refine ⟨h, hh, cA', cB * (L.xi μ₀ y : ℂ)⁻¹, y, hcA, mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _)), fun t => ⟨?_, ?_⟩⟩
  · have he := hI.idem t
    have f1 := hI.fst t
    rw [x1, x3, GlobalTheory.T.standardPairFirstMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : (X.ω t).toSgn true (1, h) X.vac = cA' • vacA ρ i j := by
      rw [om_compare (hI.weil μ₀) (hI.weil t) hy vA.2.theta, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul, kA]
    have := thetaAt_move (ΛS := G.Λ (.grid (i + 1) (j + 1))) (ΛX := latX G i j)
      (hI.weil t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2 (GlobalTheory.PlaceVec.idemSum_infPart he)
      vA.2.theta (hfx t (hst t) _ he _) hcA k f1
    rwa [eA] at this
  · have he := hI.idem t
    have f1 := hI.snd t
    rw [x2, x3, GlobalTheory.T.standardPairSecondMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : X.ω' t (1, h) X.vac' = (cB * (L.xi μ₀ y : ℂ)⁻¹ * (L.xi t y : ℂ)) • vacB ρ i j := by
      refine (om_compare (hI.weil' μ₀) (hI.weil' t) hy vB.2.theta).trans ?_
      rw [kB, smul_smul]
      congr 1
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, LevCh.mu, Lift.tup, MonoidHom.mul_apply, Circle.coe_mul]
      field_simp
    exact thetaAt_move (S := spW₁ G i j) (ΛS := G.Λ (.grid i j)) (ΛX := latX G i j)
      (hI.weil' t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW₁)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])
      (by rw [← map_mul, he.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he))
      vB.2.theta (fun x hx => hfx t (hst t) _ he _ x (by rwa [GlobalTheory.LatVac.cA_cA, or_comm] at hx))
      (mul_ne_zero (mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _))) (Circle.coe_ne_zero _)) k f1

end GlobalTheory.TopFlip

end
end
end
