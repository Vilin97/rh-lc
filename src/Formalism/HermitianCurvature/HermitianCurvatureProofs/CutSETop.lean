module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.PiTensorProduct
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DecayPairEstimate
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpansionSiteZeroInduction

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEBTCls

section

@[expose] public section

open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

section BTClsPf

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem opClos_op (X : ActualOps k r z z' π π') (l : Fin r) (B : Submodule ℂ (RadSp k r z z' π π')) (j : Fin 6) :
    ∀ Φ ∈ OpClos X l B, X.op l j Φ ∈ OpClos X l B := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨js, Ψ, hΨ, rfl⟩ := hx
    exact Submodule.subset_span ⟨j :: js, Ψ, hΨ, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem act_mem_of_entSub {S : Type} [Fintype S] [DecidableEq S] (C : Submodule ℂ (RadSp k r z z' π π'))
    (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : M ∈ entSub (presAlg C)) (u : Ix S → RadSp k r z z' π π')
    (hu : ∀ b, u b ∈ C) (b : Ix S) : act M u b ∈ C := by
  exact Formalism.FourierDecayAlt.P5.HerA.act_mem_pres M (fun a c => hM a c) u hu b

end BTClsPf

theorem boundary_torus_closure : BTCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ l _ u hu
  have hAL := hD.2.2.1
  have hop : ∀ (j : Fin 6) (Φ : (RadSp P.k P.r z z' π π')), Φ ∈ (ClsE S P z z' π π' X L st l0 D l) → X.op l j Φ ∈ (ClsE S P z z' π π' X L st l0 D l) :=
    fun j Φ hΦ => opClos_op X l _ j Φ hΦ
  have hmk : ∀ i j : Fin 6, mkP (X.op l i) (X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => hop j Φ hΦ⟩)
  have hmkneg : ∀ i j : Fin 6, mkP (X.op l i) (-X.op l j) ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := fun i j =>
    (show (∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).1 Φ ∈ (ClsE S P z z' π π' X L st l0 D l)) ∧
        ∀ Φ ∈ (ClsE S P z z' π π' X L st l0 D l), (mkP (X.op l i) (-X.op l j)).2.unop Φ ∈ (ClsE S P z z' π π' X L st l0 D l) from
      ⟨fun Φ hΦ => hop i Φ hΦ, fun Φ hΦ => by
        show (-X.op l j) Φ ∈ (ClsE S P z z' π π' X L st l0 D l)
        rw [LinearMap.neg_apply]
        exact Submodule.neg_mem _ (hop j Φ hΦ)⟩)
  have hp : L.p l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.1 l]; exact hmkneg 0 3
  have hc : L.c l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.1 l]; exact hmk 1 4
  have hci : L.ci l ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l) := by rw [hAL.2.2.2.1 l]; exact hmk 2 5
  have hconv : ∀ M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')),
      M ∈ Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) →
        M ∈ Formalism.FourierDecayAlt.P5.HerA.entSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) := fun M h => h
  have hins : ∀ (a : S) (M : M2 (Pr (RadSp P.k P.r z z' π π'))), (∀ i j, M i j ∈ Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)) →
      ins a (lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) ∈
        Formalism.FourierDecayAlt.P5.matSub (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra (Ix S) := by
    intro a M hM
    apply Formalism.FourierDecayAlt.P5.ins_mem
    have h : ∀ (i j : Fin 2) (p q : Ix S), ((lift0 M : M2 (SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))) i j) p q ∈
        (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra := by
      intro i j p q
      simp only [lift0, Matrix.map_apply, io, Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hM i j
      · exact Subalgebra.zero_mem _
    exact h
  refine ⟨fun le b => ?_, fun le b => ?_, fun a i j b => ?_⟩
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
        hp hc hci i j
    · exact star_mem
        (Formalism.FourierDecayAlt.P5.Ts_mem (T := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) (site L l) le.pt
          hp hc hci i j)
  · refine act_mem_of_entSub _ _ (hconv _ (hins le.intersection_update_fsHerm_neg_one _ ?_)) u hu b
    intro i j
    split_ifs
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem (star_mem hci)) (star_mem hc)
        (add_mem (algebraMap_mem _ _) (star_mem hp)) i j
    · exact Formalism.FourierDecayAlt.P5.HerA.matrix_two_entries_mem (zero_mem _) (neg_mem hci) hc
        (add_mem (algebraMap_mem _ _) hp) i j
  · exact act_mem_of_entSub _ _
      (hconv _ (Formalism.FourierDecayAlt.P5.eU_mem (C := (Formalism.FourierDecayAlt.P5.HerA.presAlg (ClsE S P z z' π π' X L st l0 D l)).toSubalgebra) a i j)) u hu b

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEIbTInv

section

@[expose] public section

open Matrix Formalism.FourierDecayAlt.Wd

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

namespace IbTInvPf

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem plus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) (hY : star Y = Y) :
    (!![0, -star σ.ci; star σ.c, algebraMap K A (Y + 1) + star σ.p] : M2 A) * (Ts σ Y)ᴴ = 1 := by
  have hs := congrArg star hW.2.2
  simp only [star_mul, star_add] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · rw [← star_mul, hW.1, star_one]
  · rw [← algebraMap_star_comm, hY, mul_add, add_mul, add_mul, one_mul, hs, Algebra.commutes]
    abel
  · rw [← star_mul, hW.2.1, star_one]

theorem minus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) :
    (!![0, -σ.ci; σ.c, algebraMap K A (Y - 1) + σ.p] : M2 A) * ((Ts σ Y).map star)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · exact hW.2.1
  · rw [mul_add, add_mul, sub_mul, one_mul, hW.2.2, Algebra.commutes]
    abel
  · exact hW.1

theorem lift_zero_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  unfold lift0
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [io]

theorem ivlet_mul_star (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (l : Letter K S)
    (hl : star l.pt = l.pt) : ivlet σ l * star (vlet σ l) = 1 := by
  unfold ivlet vlet
  rw [Formalism.FourierDecayAlt.P.Wd1.ins_star _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _),
    ← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _), Formalism.FourierDecayAlt.P.Wd7.liftMatrix_conjTranspose,
    ← Formalism.FourierDecayAlt.P.Wd7.lift_reduction_mul]
  cases hpl : l.plus
  · simp only [Bool.false_eq_true, ite_false]
    rw [minus_inv σ hW l.pt, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  · simp only [ite_true]
    rw [plus_inv σ hW l.pt hl, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]

theorem ibT_mul_star (σ : Site A) (hσ : IsSite σ) :
    ∀ w : List (Letter K S), (∀ l ∈ w, star l.pt = l.pt) → ibT σ w * star (bT σ w) = 1
  | [], _ => by simp [ibT, bT]
  | l :: w, h => by
    have hw := ibT_mul_star σ hσ w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [ibT, bT, star_mul, mul_assoc, ← mul_assoc (ibT σ w), hw, one_mul,
      ivlet_mul_star σ hσ.1 l (h l (by simp))]

end IbTInvPf

theorem boundary_torus_invariance : IbTInv := by
  intro K A S _ _ _ _ _ _ _ _ σ w hσ hw
  exact IbTInvPf.ibT_mul_star σ hσ w hw

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWdExpand

section

@[expose] public section

open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem wdx_diff {n m : ℕ} {f : ℂ → ℂ} (hf : ContDiffOn ℝ n f {t | t ≠ 0}) (hm : m < n) {t : ℂ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t := by
  have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
  have hd := hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hs.uniqueDiffOn
  have hdt : DifferentiableAt ℝ (iteratedFDerivWithin ℝ m f {t | t ≠ 0}) t :=
    (hd t ht).differentiableAt (hs.mem_nhds ht)
  exact hdt.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hs.mem_nhds ht)
    fun s hs' => (iteratedFDerivWithin_of_isOpen m hs hs').symm)

theorem wdx_hasFDerivAt_iter {m : ℕ} {f : ℂ → ℂ} {t : ℂ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) t) (w : Fin m → ℂ) :
    HasFDerivAt (fun s => iteratedFDeriv ℝ m f s w)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).comp (fderiv ℝ (iteratedFDeriv ℝ m f) t)) t := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℂ) ℂ w).hasFDerivAt.comp t hd.hasFDerivAt

theorem wdx_step_eval {m : ℕ} {f : ℂ → ℂ} {t : ℂ} (h : ℂ) (w : Fin m → ℂ) :
    (fderiv ℝ (iteratedFDeriv ℝ m f) t h) w = iteratedFDeriv ℝ (m + 1) f t (Fin.cons h w) := by
  rw [iteratedFDeriv_succ_apply_left]
  simp

theorem word_expansion : WdExpand := by
  intro n f bs hlen hf
  induction bs with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => Fin.elim0, fun _ => by simp, fun t _ => ?_⟩
    simp [WD]
  | cons b bs ih =>
    have hlen' : bs.length ≤ n := by simp at hlen; omega
    have hlt : bs.length < n := by simp at hlen; omega
    obtain ⟨K, a, v, -, hv⟩ := ih hlen'
    have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
    have hder : ∀ t : ℂ, t ≠ 0 → ∀ h : ℂ, fderiv ℝ (WD bs f) t h =
        ∑ i, a i * iteratedFDeriv ℝ (bs.length + 1) f t (Fin.cons h (v i)) := by
      intro t ht h
      have heq : WD bs f =ᶠ[𝓝 t] fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i) :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds ht) fun s hs' => hv s hs'
      have hd := wdx_diff hf hlt ht
      have hH : HasFDerivAt (fun s => ∑ i, a i * iteratedFDeriv ℝ bs.length f s (v i))
          (∑ i, a i • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin bs.length => ℂ) ℂ (v i)).comp
            (fderiv ℝ (iteratedFDeriv ℝ bs.length f) t))) t := by
        first
          | exact HasFDerivAt.fun_sum fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)
          | (convert HasFDerivAt.sum (u := Finset.univ)
              (fun i _ => (wdx_hasFDerivAt_iter hd (v i)).const_mul (a i)) using 1
             ext s
             simp)
      rw [heq.fderiv_eq, hH.fderiv]
      simp [wdx_step_eval]
    refine ⟨K + K, Fin.append (fun i => (1 / 2 : ℂ) * a i)
        (fun i => (1 / 2 : ℂ) * ((if b then -Complex.I else Complex.I) * a i)),
      Fin.append (fun i => Fin.cons (1 : ℂ) (v i)) (fun i => Fin.cons Complex.I (v i)),
      fun h => by simp at h, fun t ht => ?_⟩
    show wirt b (WD bs f) t = ∑ i : Fin (K + K), _ * iteratedFDeriv ℝ (bs.length + 1) f t _
    unfold wirt
    rw [hder t ht, hder t ht, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, mul_add, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETop

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.FourierDecayAlt.P5.HerD

theorem expansion_l2_of_open_estimates (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : LevelDensitySquareIntegrable :=
  expansion_L2_of_decay_pairs word_expansion (step_density_expansion_of_mirror boundary_torus_invariance (expansion_site_zero_induction hS hO boundary_torus_closure))
    decay_pair_estimate h2 h3 h4

theorem stepExp0_of_open (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : StepExp0 :=
  step_density_of_square (expansion_l2_of_open_estimates hO hS h2 h3 h4)

end Formalism.FourierDecayAlt.P.CutSE
end
end
end
