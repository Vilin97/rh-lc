module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartitionStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValues

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem evG_id_smul {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (a : ℂ) (P : Pol ℂ ι n) :
    evG fr sh (RingHom.id ℂ) (a • P) = a • evG fr sh (RingHom.id ℂ) P := by
  funext y
  simp only [evG, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply]
  ring

theorem Kmap_isVal : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi hU c c' f hf
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨n, h1, h2, h3, h4⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hle : D.R.N i ≤ D.R.N (i + 1) := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have key := GlobalTheory.KerWt.tied_on_models D u C O i hi (nuT D u i) hU ℂ (RingHom.id ℂ) (lamTG M i) n h1 c c'
    (jetC O.dgen (O.Th i c c')) 1 (fun m => by simp) (fun τ => (lamTG M i τ).detShift) h2 P hP
  rw [one_smul] at key
  have hsh : (fun τ => -C.sDiv i τ) = fun τ => (lamTG M (i + 1) τ).detShift := funext fun τ => (h4 τ).symm
  rw [hsh] at key
  refine ⟨(C.rhoDet i c * C.rhoDet' i c') • jetMap (jetC O.dgen (O.Th i c c')) n P, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (GlobalTheory.KerWt.jet_in_vv_of_weight ℂ D.what₂.Tau _ _ hle (lamTG M i) (lamTG M (i + 1)) n h3 _ P hP)
  · rw [key, evG_id_smul]

end GlobalTheory.KerJ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValuesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.pair_kernel_maps_step_weight_values : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.Kmap_isVal | exact GlobalTheory.KerJ.Kmap_isVal | (intros; apply GlobalTheory.KerJ.Kmap_isVal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyAt0PolDEquivariant

section

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.BasicNotions NumberField GlobalTheory.ThStr GlobalTheory.ThBe0 Classical

namespace GlobalTheory.ClassSumEquiv

open MvPolynomial

theorem polD_subst (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ τ, (γ' τ).det ≠ 0) :
    aeval (fun l : Idx D N N' => ∑ k, C ((γ' l.1)⁻¹ k l.2.1) * (X (l.1, k, l.2.2) : MvPolynomial (Idx D N N') ℂ))
      (aeval (fun l : Idx D N N' => ∑ k, C (γ l.1 l.2.2 k) * (X (l.1, l.2.1, k) : MvPolynomial (Idx D N N') ℂ))
        (polD D s Q (fun τ => γ' τ * y' τ))) =
      polD D s (aeval (fun k : FrV D N => ∑ a : Fin N, C (γ k.1 k.2.1 a) *
        (X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y' := by
  unfold polD
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun ⟨τ, a, k⟩ => ?_

  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hk
  · have e : y' τ b' ⟨k, hk⟩ = ∑ b, (γ' τ)⁻¹ b' b * (γ' τ * y' τ) b ⟨k, hk⟩ := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ (h τ).isUnit]

    rw [e, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · simp

theorem applyAt0_polD_equivariant : ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ) (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (G : VC D N N' → ℂ), (∀ τ, (γ' τ).det ≠ 0) → Differentiable ℂ G → applyAt0 D (polD D s Q (fun τ => γ' τ * y' τ)) (fun z => G (fun τ => ((γ' τ)⁻¹ * Matrix.of (z τ) * γ τ : Matrix (Fin N') (Fin N) ℂ))) = applyAt0 D (polD D s (MvPolynomial.aeval (fun k : FrV D N => ∑ a : Fin N, MvPolynomial.C (γ k.1 k.2.1 a) * (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y') G := by
  intro D N N' s Q y' γ' γ G h hG
  have hd : Differentiable ℂ (fun z => G (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹) z)) :=
    hG.comp (LinearMap.toContinuousLinearMap (GlobalTheory.NormSum.Minor.mulL (a := N) (fun τ => (γ' τ)⁻¹))).differentiable
  have h1 := GlobalTheory.NormSum.Minor.applyAt0_comp hd (GlobalTheory.NormSum.Minor.mulR γ) (fun l k => γ l.1 l.2.2 k)
    (fun l k => (l.1, l.2.1, k)) (GlobalTheory.NormSum.Minor.mulR_coordV γ) (polD D s Q (fun τ => γ' τ * y' τ))
  rw [GlobalTheory.NormSum.Minor.applyAt0_comp hG (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹))
    (fun l k => (γ' l.1)⁻¹ k l.2.1) (fun l k => (l.1, k, l.2.2)) (GlobalTheory.NormSum.Minor.mulL_coordV _),
    polD_subst D N N' s Q y' γ' γ h] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]
  rfl

end GlobalTheory.ClassSumEquiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

open GlobalTheory.KerWt

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) (k : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : GL3Theta.applyAt0 D P (fun z => k * G z) = k * GL3Theta.applyAt0 D P G := by
  exact (GlobalTheory.NormSum.applyAt0_minorPol_linear D N N' (fun _ => 0) G hG).2.2.1 k P

theorem applyAt0_polD_eigen (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' γ : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (k : ℂ) (hγ : ∀ τ, (γ τ).det ≠ 0)
    (hG : Differentiable ℂ G) (hk : ∀ z : TaylorLogMetric.VC D N N', G (fun τ => (γ τ * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * G z) :
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q (fun τ => γ τ * y' τ)) G = k * GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  have h := GlobalTheory.ClassSumEquiv.applyAt0_polD_equivariant D N N' s Q y' γ (fun _ => 1) (fun z => k * G z) hγ (hG.const_mul k)
  have e1 : (fun z : TaylorLogMetric.VC D N N' => k * G (fun τ => ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N') (Fin N) ℂ))) = G := by
    funext z
    refine (hk _).symm.trans (congrArg G (funext fun τ => ?_))
    have : (γ τ * ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N') (Fin N) ℂ) = Matrix.of (z τ) := by
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hγ τ).isUnit]
    exact this
  have e2 : (MvPolynomial.aeval (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) Q) = Q := by
    have : (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) = MvPolynomial.X := by
      funext k
      rw [Finset.sum_eq_single k.2.1]
      · simp
      · intro b _ hb
        simp [Matrix.one_apply_ne hb.symm]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  beta_reduce at h
  rw [e1, e2, applyAt0_const_mul D _ k G hG] at h
  exact h

theorem lawAt_Kmap : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi h c c' hd g ⟨hdet, k, hk, hg⟩ f ⟨P, hP, hf⟩ y y' hy
  obtain ⟨n, hw, hn, -, -⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hs : C.sharp i f = frPoly O i (MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) (RingHom.id ℂ) _ (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    rw [hf]
    exact h1
  have hQ : MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ (nuT D u i) := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ (lamTG M i) n (MvPolynomial.map (RingHom.id ℂ) P) (map_mem_VV _ _ P hP)
    have e : (fun τ r => (lamTG M i τ).natW r + n τ) = nuT D u i := by funext τ r; exact hw τ r
    rwa [e] at h2
  generalize MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ = Q at hs hQ
  have hu : ∀ x : C.Y (i + 1), C.unf i c c' (C.sharp i f) x =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c') := fun x => by
    rw [hs]
    exact (unfolding_iff_alt D u C O i hi.le _).1 h c c' Q hQ x
  have hK : ∀ x : C.Y (i + 1), C.Kmap i c c' f x = (C.rhoDet i c * C.rhoDet' i c') *
      ((∏ τ, (O.frm (i + 1) x τ).det ^ C.sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c')) := fun x => by
    rw [← hu x]
    simp only [← O.frm_de (i + 1) hi]
    rfl
  have hdm : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det = TaylorLogMetric.embT D τ g.1.det := fun τ => ((TaylorLogMetric.embT D τ).map_det g.1).symm
  have hne : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det ≠ 0 := fun τ => by
    rw [hdm]; exact (map_ne_zero _).2 hdet
  have hy' : O.frm (i + 1) y = fun τ => g.1.map (TaylorLogMetric.embT D τ) * O.frm (i + 1) y' τ := funext hy
  rw [hK, hK, hy', applyAt0_polD_eigen D _ _ _ Q _ _ _ k hne hd hk, hg]
  simp only [Matrix.det_mul, hdm, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  ring

end GlobalTheory.KerJ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLawStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.pair_kernel_term_target_stabiliser_law : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.lawAt_Kmap | exact GlobalTheory.KerJ.lawAt_Kmap | (intros; apply GlobalTheory.KerJ.lawAt_Kmap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantForms

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ.FiCore

theorem isVal_sum {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → Yv → ℂ) (h : ∀ c, IsVal fr lam (RingHom.id ℂ) (f c)) :
    IsVal fr lam (RingHom.id ℂ) (∑ c ∈ s, w c • f c) := by
  choose P hP hf using h
  refine ⟨∑ c ∈ s, w c • P c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hP c), ?_⟩
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, evG, MvPolynomial.eval₂_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem lawAt_sum {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ)
    (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → C.Y i → ℂ) (h : ∀ c, LawAt O i g (f c)) :
    LawAt O i g (∑ c ∈ s, w c • f c) := by
  intro y y' hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [h c y y' hy]; ring

theorem K_mem_Fi : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  intro D u C A Pm M O G hF hU hd hT i hi φ hφ
  have hv := hF.1 i hi.le φ hφ
  refine (hF.2 (i + 1) (Nat.le_add_left 1 i) hi _).2 fun c' => ?_
  have hK : C.K i φ c' = ∑ c, C.wt i c • C.Kmap i c c' (φ c) := by
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM]
  rw [hK]
  exact ⟨isVal_sum _ _ _ _ _ fun c => GlobalTheory.T.pair_kernel_maps_step_weight_values D u C A Pm M O i hi (hU i hi) c c' _ (hv c),
    fun g hg => lawAt_sum O _ g _ _ _ fun c =>
      GlobalTheory.T.pair_kernel_term_target_stabiliser_law D u C A Pm M O i hi (hU i hi) c c' (hd i hi c c') g (hT i hi c c' g hg) _ (hv c)⟩

end GlobalTheory.KerJ.FiCore
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  first | exact @GlobalTheory.KerJ.FiCore.K_mem_Fi | exact GlobalTheory.KerJ.FiCore.K_mem_Fi | (intros; apply GlobalTheory.KerJ.FiCore.K_mem_Fi <;> assumption)
end
end
