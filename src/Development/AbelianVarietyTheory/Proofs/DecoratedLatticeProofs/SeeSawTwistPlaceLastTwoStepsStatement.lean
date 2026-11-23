module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsModelCombL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhatStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvariStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u y yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb → ∀ d₁ d₂, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) d₁ (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb) → (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM d₂ (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁]) (aconv [c₂, d₂]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QPl.LastOrb.orb | exact GlobalTheory.QPl.LastOrb.orb | (intros; apply GlobalTheory.QPl.LastOrb.orb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditive

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

namespace GlobalTheory.LastOneLin

variable {D : D7}

theorem sum_fin {G M : Type*} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem biTheta_left (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => C u' v) u) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ A S c (fun u' => C u' v) u) =
      fun w => ∑ x ∈ c.support, c x * heisO ψ _ S (GlobalTheory.BiTransfer.inlH d S x) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inl, GlobalTheory.BiTransfer.snd_inl, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun x _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c x) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_right (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (C u) v) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ S A' c (C u) v) =
      fun w => ∑ y ∈ c.support, c y * heisO ψ _ S (GlobalTheory.BiTransfer.inrH d S y) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inr, GlobalTheory.BiTransfer.snd_inr, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, zero_add]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun y _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c y) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_biComb_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) :=
  biTheta_left hψ hθ (biTheta_right hψ hθ hC c') c

end Theta

theorem aconv_one {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G)
  rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_nil, mul_one]

theorem comb_aconv_pair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {E : AE D} (hE : cA D E = E) (hEE : E * E = E)
    (c d : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, IsHalf (1 - E) u) (hd : ∀ u ∈ d.support, IsHalf E u)
    (f : WO S T → ℂ) : comb ψ S T (aconv [c, d]) f = comb ψ S T c (comb ψ S T d f) := by
  have h := GlobalTheory.QFinLaw.comb_aconv_cons ψ S T c [d] (fun x hx y hy => by
    rw [aconv_one] at hy
    exact GlobalTheory.HeisComb.symplO_half S T (1 - E) E x y (by rw [map_sub, map_one, hE])
      (by rw [sub_mul, one_mul, hEE, sub_self]) (hc x hx) (hd y hy)) f
  rwa [aconv_one] at h

theorem place_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  refine ⟨by rw [map_add (f := _), cA_cA, add_comm], ?_⟩
  linear_combination h1 + 2 * h2 + h3

theorem lin : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  intro D c v χ Q hc hv h hr hτ s₁ hs₁ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ ι S d₁ d₂ hd₁ hd₂
  obtain ⟨hE, hEE⟩ := place_idem (D := D) Q.q
  have hL : IsBiTheta c.ψ _ _ _ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (Q.s + 1)) (c.X (Q.s + 1)) c.T (c.jac Q.s 0 h).d hc.std
    have hY' : IsThetaFunO c.ψ (c.X (Q.s + 1)) c.T (fun w => Ψ₂ ((c.jac Q.s 0 h).d.ext0 c.T w)) := (hthS Ψ₂).2 hΨ₂
    have hZ' : IsThetaFunO c.ψ (c.B Q.s 0 h).V (c.J Q.s 0 h).W Ψ₁ := hΨ₁
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero s₁ hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes Q.s 0 h).V₀ (c.X Q.s) (c.bes Q.s 0 h).L (c.X (Q.s + 1))
      (c.X (Q.s + 1 + 1)) c.T c.Lz (c.bes Q.s 0 h).o (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hτ (flatBF s₁ Ψ₁) _ hΞ hY'
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X Q.s) := (hc.x Q.s (by omega)).cpt
  have hS : CoCpt (c.X (Q.s + 1)) := (hc.x (Q.s + 1) (by omega)).cpt
  have step : biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) =
      ∑ i ∈ S, biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    show (GlobalTheory.BiCombStable.biCombL c.ψ _ _ _ c₁ c₂) (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ProdLocInv.biComb_comp c.ψ _ _ _ c₁ (d₁ i) (aconv [c₁, d₁ i]) c₂ (d₂ i) (aconv [c₂, d₂ i])
      (comb_aconv_pair c.ψ _ _ hE hEE c₁ (d₁ i) hc₁ (hd₁ i)) (comb_aconv_pair c.ψ _ _ hE hEE c₂ (d₂ i) hc₂ (hd₂ i)) _
  rw [step]
  funext h₂
  rw [Finset.sum_apply, sum_fin S (fun i => biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)),
    sum_fin S (fun i => c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) h₂)]
  exact GlobalTheory.SeeSmallPf.biLift_sum hB hoa hob hA hS _ _ hφ
    (fun j => biComb c.ψ _ _ _ (aconv [c₁, d₁ (S.equivFin.symm j)]) (aconv [c₂, d₂ (S.equivFin.symm j)])
      (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))
    (fun j => biTheta_biComb_any hc.std hc.inf hL _ _) h₂

end GlobalTheory.LastOneLin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.LastOneLin.lin | exact GlobalTheory.LastOneLin.lin | (intros; apply GlobalTheory.LastOneLin.lin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  first | exact @GlobalTheory.QPl.CoupStab.coupIdx_stab | exact GlobalTheory.QPl.CoupStab.coupIdx_stab | (intros; apply GlobalTheory.QPl.CoupStab.coupIdx_stab <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLastTwoSteps

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

namespace GlobalTheory.QLastOne



theorem lastOne : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by

  intro D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u
  classical
  obtain ⟨hfin, -, hsymm, htrans, hstab⟩ := GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable D c v χ Q

  have hcomb : ∀ {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (FS : GlobalTheory.LocMod.Frame Q.k S.rank Y') (FT : GlobalTheory.LocMod.Frame Q.k T.rank Y) (Ξ : Matrix Y Y' Q.k → ℂ),
      Ξ ∈ SB _ → ∃ d, (ofSplit Q.q).IsCombAt c.ψ FS FT d Ξ := by
    intro S T Y Y' _ _ _ _ FS FT Ξ hΞ
    let O : SB (Matrix Y Y' Q.k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Y Y'⟩
    have hO : O ≠ 0 := by
      intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      simp [O, Set.indicator_apply] at this
    obtain ⟨d, hd, hT⟩ := GlobalTheory.T.exists_heisenberg_combination_split_place_datum D Q.k (ofSplit Q.q) Y Y' S T FS FT c.ψ hc.std O ⟨Ξ, hΞ⟩ hO
    refine ⟨d, hd, fun Tm hTm Φ₀ Φ h0 h1 => ?_⟩
    have e0 : Φ₀ = O := Subtype.ext h0
    have e1 : Φ = ⟨Ξ, hΞ⟩ := Subtype.ext h1
    rw [e0, e1]
    exact hT Tm hTm
  choose d₁ hd₁ using fun yb => hcomb (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1
  choose d₂ hd₂ using fun yb => hcomb (Q.FX (Q.s + 1) le_rfl) Q.FM _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2
  set S := hfin.toFinset with hS
  have hSc : Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S := by simp [S]
  have hmemS : ∀ yb, yb ∈ S ↔ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := fun yb => by simp [S]
  set C := c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂ with hC
  have hpt := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α S hSc d₁ d₂ hd₁ hd₂
  have hlin := GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1 φ hφ
  rw [hpt, hlin _ S d₁ d₂ (fun i => (hd₁ i).1) (fun i => (hd₂ i).1)]

  set B : Q.Ch (Q.s + 1) → GA D (c.X (Q.s + 1 + 1)) → ℂ := fun y =>
    c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) with hB

  have hterm : ∀ yb ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ yb]) (aconv [c₂, d₂ yb]) C) =
      ∑ y, if SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb then B y else 0 := by
    intro yb hyb
    obtain ⟨y₀, hy₀⟩ := Q.cos_cov yb ((hmemS yb).1 hyb)
    rw [Finset.sum_eq_single y₀]
    · rw [if_pos hy₀]
      exact GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u y₀ yb hy₀
        (d₁ yb) (d₂ yb) (hd₁ yb) (hd₂ yb)
    · intro y _ hy
      rw [if_neg]
      intro h'
      exact hy (Q.cos_inj y y₀ (htrans _ _ _ h' (hsymm _ _ hy₀)))
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  by_cases hy : Q.cos y ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)
  · have hset : {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} =
        ↑(S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) := by
      ext yb
      simp only [Set.mem_setOf_eq, Finset.coe_filter]
      exact ⟨fun h' => ⟨(hmemS yb).2 (hstab _ hy yb h'), h'⟩, fun h' => h'.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.cast_smul_eq_nsmul]
  · have hempty : (S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro yb hyb h'
      exact hy (hstab yb ((hmemS yb).1 hyb) _ (hsymm _ _ h'))
    have hnot : Q.cos y ∉ S := fun h' => hy ((hmemS _).1 h')

    have hz : biComb c.ψ _ _ _ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u) C = 0 := by
      have h2 := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α (insert (Q.cos y) S)
        (hSc.trans (by simp)) (Function.update d₁ (Q.cos y) (Q.dL Q.s α y))
        (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u))
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_pen α y
          · rw [Function.update_of_ne e]; exact hd₁ yb)
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_top y u
          · rw [Function.update_of_ne e]; exact hd₂ yb)
      rw [hpt, Finset.sum_insert hnot, Function.update_self, Function.update_self] at h2
      have h3 : ∑ yb ∈ S, biComb c.ψ _ _ _ (Function.update d₁ (Q.cos y) (Q.dL Q.s α y) yb)
          (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u) yb) C =
          ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C := by
        refine Finset.sum_congr rfl fun yb hyb => ?_
        have e : yb ≠ Q.cos y := fun e => hnot (e ▸ hyb)
        rw [Function.update_of_ne e, Function.update_of_ne e]
      rw [h3] at h2
      rw [← hC] at h2
      have h4 := congrArg (fun F => F - ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C) h2
      simp only [sub_self, add_sub_cancel_right] at h4
      exact h4.symm
    have hB0 : c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) = 0 := by
      have e1 := hlin Unit (Finset.univ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      have e2 := hlin Unit (∅ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.sum_empty] at e1 e2
      rw [hz] at e1
      rw [← e1, e2]
    rw [hempty, Finset.card_empty, zero_smul, hB0, smul_zero]

end GlobalTheory.QLastOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLastTwoStepsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_twistPlace_last_two_steps : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QLastOne.lastOne | exact GlobalTheory.QLastOne.lastOne | (intros; apply GlobalTheory.QLastOne.lastOne <;> assumption)
end
end
