module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEq
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  first | exact @GlobalTheory.FockConjNeg.fock_neg_cj | exact GlobalTheory.FockConjNeg.fock_neg_cj | (intros; apply GlobalTheory.FockConjNeg.fock_neg_cj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.VacCjNeg

variable {D : D7}


open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id f) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isVacVec_cj_of_isVac_neg : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f →
      GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  intro D S T ψ θ f h
  obtain ⟨hψ, hv⟩ := h
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hv.theta
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S.V) T.V f from hth), ?_, fun τ => ?_⟩
  · intro h0
    have hf0 : f = 0 := by
      rw [← GlobalTheory.CjNeg.cj_id_cj_id f, h0]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.norm
    have h1 := hall p hp
    rw [hf0] at h1
    simp [nrm2] at h1
  · intro z
    have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S.V) T.V) θ τ (cplxO (-(cart S.M τ)) (cart T.M τ)) z f = 0 :=
      hv.fock τ z
    have hJ : cplxO (-(cart S.M τ)) (cart T.M τ) z = -cplxO (cart S.M τ) (cart T.M τ) z := by
      simp [cplxO]
    unfold annih at h0 ⊢
    rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hv.inf hth] at h0
    rw [dRho_cj hψ, dRho_cj hψ]
    funext x
    have h2 := congrFun h0 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq]
    have e := congrArg (starRingEnd ℂ) h2
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at e
    linear_combination e

end GlobalTheory.VacCjNeg

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f → GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  first | exact @GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | exact GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | (intros; apply GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  first | exact @GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | exact GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | (intros; apply GlobalTheory.ConjWeilBack.weil_conjRep_of_neg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjoint

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

theorem isIntw_transport {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X Y P P' : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P'] [Module ℂ P'] (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (ω₀ : GA D V × GA D W →* Module.End ℂ (Y → ℂ))
    (pt : P → (X → ℂ)) (pt₀ : P' → (Y → ℂ)) (e : P ≃ₗ[ℂ] P') (b : Y → X) (It : P' →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (hpt : ∀ φ, pt₀ (e φ) = pt φ ∘ b) (hω : ∀ p F, ω₀ p (F ∘ b) = ω p F ∘ b) (h : IsIntw θ M M' ω₀ pt₀ It) :
    IsIntw θ M M' ω pt (It ∘ₗ e.toLinearMap) := by
  refine { ne := ?_, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro h0
    apply h.ne
    apply LinearMap.ext
    intro φ
    have hφ := congrArg (fun L => L (e.symm φ)) h0
    simpa using hφ
  · intro φ w
    exact h.bdd (e φ) w
  · intro τ g hg φ φ' hφ v
    exact h.eqK τ g hg (e φ) (e φ') (by rw [hpt, hpt, hφ, hω]) v
  · intro τ Y hY φ φ' hd v
    exact h.eqg τ Y hY (e φ) (e φ') (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) v
  · intro τ k hk φ φ' v v' hφ hv
    exact h.invK τ k hk (e φ) (e φ') v v' (by rw [hpt, hpt, hφ, hω]) hv
  · intro τ Y hY φ φ' v v' hd hv
    exact h.invg τ Y hY (e φ) (e φ') v v' (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) hv


open GlobalTheory.FockAdjoint in
theorem ptOf_dag {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} {SV SW : D.what₂.Tau → SPar} (M : DSModel V SV) (M' : DSModel W SW) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) :
    ptOf ψ θ M' M (dag V W g) (jHom (Fr.ofModel M) (Fr.ofModel M') Q) = dag V W (ptOf ψ θ M M' g Q) := by
  set A := Fr.ofModel M
  set B := Fr.ofModel M'
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ V W
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  have hd := L.theta g hg
  show ptF ψ θ B A (dag V W g) (jHom A B Q) = dag V W (ptF ψ θ A B g Q)
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
      dag_smul']
  | add p q hp hq => rw [map_add (f := _), ptF_add, ptF_add, hp, hq, dag_add]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
      ptF_X_mul hψ hθ A B hg]
    dsimp only
    rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hg p), cdag_unitMap,
      aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hg p), dag_smul', Complex.conj_ofReal, smul_smul]
    rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]

open GlobalTheory.FockAdjoint in
theorem jHom_map_conj {S T : HSp D} (A : Fr S) (B : Fr T) (P : PolF D T.rank S.rank) :
    jHom A B (MvPolynomial.map (starRingEnd ℂ) P) = swapHom A B P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [jHom_C, swapHom]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.map_X, jHom_X, map_mul, swapHom_X]

theorem dag_cj {S T : HSp D} (F : WO S T → ℂ) : dag S T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = F ∘ adjO S T := by
  funext y; simp [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

end GlobalTheory.AdjTr


open GlobalTheory.AdjTr in
theorem GlobalTheory.AdjTr.downArrow_transport : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  intro D S T ψ θ χ ω f hθ hW hV
  set A := Fr.ofModel S.M
  set B := Fr.ofModel T.M
  have hstd : IsStdChar D ψ (-1) := hV.1
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hstd S.V T.V
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hV.2.theta
  have hvv := GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace S T ψ θ f hV
  refine ⟨adjRep ω, dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f), χ⁻¹, (swapEquiv A B).toLinearEquiv, ?_,
    fun τ a h => GlobalTheory.Mem.HeckeExp.hasInfExp_inv h, ⟨L.theta _ hvv.theta, ?_, fun τ => GlobalTheory.FockAdjoint.vac_dag hstd hθ L τ
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ) hvv.theta (hvv.vac τ)⟩,
    fun It hIt => ?_⟩
  · exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S.V T.V χ⁻¹ χ⁻¹ (conjRep ω) (GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace ψ S.V T.V χ χ ω hW)
  · intro h0
    apply hvv.ne
    funext x
    have := congrFun h0 (adjO T.V S.V x)
    simp only [dag, GlobalTheory.AdjLawPf.adj_invol, Pi.zero_apply, map_eq_zero] at this
    exact this
  · refine isIntw_transport θ T.M S.M ω.swap (adjRep ω) (GlobalTheory.Grid.fock ψ θ true S T f)
      (ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))) (swapEquiv A B).toLinearEquiv (adjO S.V T.V) It
      (fun φ => ?_) (fun p F => ?_) ((GlobalTheory.Grid.isIntw_iff θ T.M S.M _ _ It).2 hIt)
    · show ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (swapHom A B φ) = _
      rw [← jHom_map_conj, ptOf_dag hstd hθ S.M T.M hvv.theta, ← GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq S T ψ θ f hstd hθ hth, dag_cj]
    · obtain ⟨h, g⟩ := p
      rw [adjRep_apply, WRep.swap_apply]
      funext y
      simp only [Function.comp_apply, GlobalTheory.AdjLawPf.adj_invol]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjointStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  first | exact @GlobalTheory.AdjTr.downArrow_transport | exact GlobalTheory.AdjTr.downArrow_transport | (intros; apply GlobalTheory.AdjTr.downArrow_transport <;> assumption)
end
end
