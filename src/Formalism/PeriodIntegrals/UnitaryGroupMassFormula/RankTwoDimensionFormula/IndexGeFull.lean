module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrame
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.MemMLOfInAt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.UnitriangularReductionOfMemLevel

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UniAMulDiag

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh23.uniA_mul_diag :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by
  intro F _ k A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAUni

section

@[expose] public section

namespace PI.UnitaryDimensionFormula

open Matrix

section Core

variable {F : Type} [Field F] {k : ℕ}

theorem uniA_mul_diag (A B : Matrix (Fin k) (Fin k) F) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  first | exact UpperTheory.Reformulated.B.Qh23.uniA_mul_diag .. | (apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB i | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F

theorem uniA_tri (x : GL (Fin k) F) (hx : ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0) :
    (x : Matrix (Fin k) (Fin k) F).BlockTriangular id := fun i j h => hx i j h

theorem uniA_mul (x y : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x)
    (hy : Formalism.L2.SG.GGMirabolic.IsUni k y) : Formalism.L2.SG.GGMirabolic.IsUni k (x * y) := by
  have tx := uniA_tri x hx.2
  have ty := uniA_tri y hy.2
  have txy : ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F)).BlockTriangular id :=
    tx.mul ty
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · rw [Units.val_mul, uniA_mul_diag _ _ tx ty, hx.1 i, hy.1 i, one_mul]
  · rw [Units.val_mul]; exact txy h

theorem uniA_inv (x : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x) :
    Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹ := by
  have tx := uniA_tri x hx.2
  have : Invertible (x : Matrix (Fin k) (Fin k) F) := Units.invertible x
  have tinv : ((x : Matrix (Fin k) (Fin k) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular tx
  have hc : ((x⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (x : Matrix (Fin k) (Fin k) F)⁻¹ :=
    Matrix.coe_units_inv x
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · have h1 : ((x : Matrix (Fin k) (Fin k) F)⁻¹ * (x : Matrix (Fin k) (Fin k) F)) i i = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq]
    rw [uniA_mul_diag _ _ tinv tx, hx.1 i, mul_one] at h1
    rw [hc]; exact h1
  · rw [hc]; exact tinv h

end Core

theorem uniSub : UniSub := by
  intro F _ k x y hx hy
  exact ⟨uniA_mul x y hx hy, uniA_inv x hx⟩

end PI.UnitaryDimensionFormula
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAFrG

section

@[expose] public section

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace PI.UnitaryDimensionFormula

def FrGram : Prop := ∀ (D : D7) (X : HidaSetting D) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
  ∀ G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), (∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E) →
  (∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then epsX X e else 0)) →
  ∃ y ∈ IntAf X.B.I.F X.B.I.E, epsX X e * G.det * y = epsX X e

theorem fg_det {B : Type} [CommRing B] (S : Subring B) {k : ℕ} (G : Matrix (Fin k) (Fin k) B) (ε gg : B)
    (hε : ε ∈ S) (hg : gg ∈ S) (hG : ∀ l j, G l j ∈ S)
    (hc : ∀ l j, ∃ t ∈ S, G l j - (if l = j then ε else 0) = gg * t) :
    ∃ m ∈ S, G.det = ε ^ k + gg * m := by
  classical

  let G' : Matrix (Fin k) (Fin k) S := fun l j => ⟨G l j, hG l j⟩
  let ε' : S := ⟨ε, hε⟩
  let g' : S := ⟨gg, hg⟩
  let I : Ideal S := Ideal.span {g'}
  have hmap : (Ideal.Quotient.mk I).mapMatrix G' =
      Matrix.scalar (Fin k) (Ideal.Quotient.mk I ε') := by
    ext l j
    obtain ⟨t, ht, he⟩ := hc l j
    have hsub : G' l j - (if l = j then ε' else 0) ∈ I := by
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      split_ifs at he ⊢ <;> simp [G', ε', g'] <;> first | linear_combination he | linear_combination -he
    have := Ideal.Quotient.eq.mpr hsub
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    rw [this]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I G'.det = Ideal.Quotient.mk I (ε' ^ k) := by
    rw [RingHom.map_det, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, map_pow]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hdet)
  refine ⟨m, m.2, ?_⟩
  have hG' : S.subtype.mapMatrix G' = G := by
    ext l j
    rfl
  have h1 : G.det = S.subtype G'.det := by
    rw [RingHom.map_det, hG']
  have h2 : G'.det = ε' ^ k + m * g' := by
    rw [hm]; ring
  rw [h1, h2]
  simp [ε', g', mul_comm]

theorem frGram : FrGram := by
  intro D X e hE G hGi hGc
  have h1 : X.ew * X.ew = X.ew := X.ew_idem
  have h2 : X.ew ∈ IntAf X.B.I.F X.B.I.E := X.ew_int
  have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E := by
    unfold IntAf Formalism.UG.tensInt
    exact Subring.subset_closure (Or.inr ⟨⟨e, hE.1⟩, rfl⟩)
  have hε : epsX X e ∈ IntAf X.B.I.F X.B.I.E := (IntAf X.B.I.F X.B.I.E).mul_mem h3 h2
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem (IntAf X.B.I.F X.B.I.E) _
  obtain ⟨m, hm, hdet⟩ := fg_det (IntAf X.B.I.F X.B.I.E) G (epsX X e)
    ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hε hg hGi (fun l j => hGc l j)

  have hidem : epsX X e * epsX X e = epsX X e := by
    unfold epsX
    calc (1 ⊗ₜ[X.B.I.F] e * X.ew) * (1 ⊗ₜ[X.B.I.F] e * X.ew)
        = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (X.ew * X.ew) := by ring
      _ = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * X.ew := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hE.2.1, h1]
  have hpow : ∀ n : ℕ, epsX X e * epsX X e ^ n = epsX X e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hidem]
  obtain ⟨y, hy, hyeq⟩ := idxDJacE X.B.I.F X.B.I.E X.B.g e hE m hm
  refine ⟨y, hy, ?_⟩
  rw [hdet, mul_add, hpow]
  have hfac : epsX X e + epsX X e * (((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) =
      X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e *
        (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m)) := by
    unfold epsX
    ring
  rw [hfac, mul_assoc, hyeq]
  unfold epsX
  ring

end PI.UnitaryDimensionFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrameAsm

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  PI.UnitaryDimensionFormula.unitaryCongruence PI.UnitaryDimensionFormula.NormCutK PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxDFrame_of (hS : IdxDSig) (hJ : IdxDJacE) (hG : FrGram) : IdxDFrame := by
  intro D X u e hE
  set eps := epsX X e with heps
  set G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    Matrix.of fun l j => Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (cv e u l) (bv e u j) with hGdef
  have hGint : ∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E := fun l j =>
    hA_int X.B.I (cv_Lf hJ hE u l) (bv_Lf hJ hE u j)
  have hGc : ∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then eps else 0) := fun l j => G_cong hJ hE u l j
  obtain ⟨y, hy, hyE⟩ := hG D X e hE G hGint hGc
  set M := (eps * y) • G.adjugate with hMdef
  have hM : M * G = eps • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) := FrameAlg.inv_on G eps y hyE
  have hMint : ∀ i l, M i l ∈ IntAf X.B.I.F X.B.I.E := fun i l =>
    mul_mem (mul_mem (eps_int hE) hy) (int_adj hGint i l)
  have hMe : ∀ i l, M i l * eps = M i l := fun i l => by
    show eps * y * G.adjugate i l * eps = eps * y * G.adjugate i l
    have := eps_idem (X := X) hE.2.1
    linear_combination (y * G.adjugate i l) * this
  have hse : sigA X.B.I eps * sigA X.B.I eps = sigA X.B.I eps := by
    rw [← map_mul, eps_idem hE.2.1]
  refine ⟨bv e u, fun i => ∑ l, sigA X.B.I (M i l) • cv e u l, ⟨eps_idem hE.2.1, eps_orth, fun i => ?_,
    fun i => ?_, fun i j => ?_⟩, fun i => ⟨bv_Lf hJ hE u i, ?_⟩, fun i w hw => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩
  · rw [bv, smul_smul, eps_idem hE.2.1]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cv, smul_comm (sigA X.B.I eps) (sigA X.B.I (M i l)), smul_smul (sigA X.B.I eps), hse]
  · exact FrameAlg.dual_fix (sigA X.B.I) (JA X.B.I) (hS X.B.I).1 (bv e u) (cv e u) eps M hM i j
  · exact Submodule.sum_mem _ fun l _ => smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)
  · rw [hA_symm X.B.I w, bv, hA_smul_right]
    have := fixV_perp hS hE.2.1 u (X.bw i) w hw
    rw [eps_eq, show E1 X e * X.ew * hA X.B.I w (Qv X e u (X.bw i)) =
      X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bw i))) by ring, this, mul_zero, map_zero]
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [hA_symm X.B.I w, ← hL_apply, map_sum]
    have hz : ∀ l, hL X.B.I w (sigA X.B.I (M i l) • cv e u l) = 0 := fun l => by
      rw [hL_apply, hA_smul_right, cv, hA_smul_right, sig_eps]
      have := fixV_perp hS hE.2.1 u (X.bwd l) w hw
      rw [show sigA X.B.I (M i l) * (E1 X e * sigA X.B.I X.ew * hA X.B.I w (Qv X e u (X.bwd l))) =
        sigA X.B.I (M i l) * sigA X.B.I X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bwd l))) by ring, this, mul_zero]
    rw [Finset.sum_eq_zero fun l _ => hz l, map_zero]
  ·
    have hsum : hA X.B.I (∑ l, sigA X.B.I (M i l) • cv e u l) (X.bw j) =
        ∑ l, M i l * hA X.B.I (cv e u l) (X.bw j) := by
      show Formalism.UG.hform (sigA X.B.I) (JA X.B.I) _ _ = _
      rw [FrameAlg.h_sum_left]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [FrameAlg.h_smul_left, sigA_sigA]; rfl
    have h1 : ZMod' X.B.I X.B.g (∑ l, M i l * (hA X.B.I (cv e u l) (X.bw j) - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (cbw_cong hJ hE u l j)
    have h2 : ZMod' X.B.I X.B.g (∑ l, M i l * (G l j - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (hGc l j)
    have hMG : ∑ l, M i l * G l j = if i = j then eps else 0 := by
      have := congrFun (congrFun hM i) j
      simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
    have hs : ∀ (F : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        ∑ l, M i l * (F l - if l = j then eps else 0) = ∑ l, M i l * F l - M i j := fun F => by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hMe]
    rw [hs, hMG] at h2
    rw [hs] at h1
    refine to_ew hE (hA_int X.B.I (Submodule.sum_mem _ fun l _ =>
      smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)) ((X.vectorsInLattice.2.2 j).1)) (i = j) ?_
    rw [hsum]
    have := Z_sub X.B.I X.B.g h1 h2
    convert this using 1
    ring
  · exact to_ew hE (hA_int X.B.I ((X.vectorsInLattice.2.2 i).2) (bv_Lf hJ hE u j)) (i = j) (bwdb_cong hJ hE u i j)

theorem idxDFrame : IdxDFrame := idxDFrame_of idxDSig idxDJacE frGram

end PI.UnitaryDimensionFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKHom

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cj_good {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    NormCutK.Good X (cj X u s) := by
  have hk1 : (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((s : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    simpa [cj, mul_assoc] using hs
  have hk2 : ((s : X.B.I.Gf) * X.xu u)⁻¹ * (((1 : Hfin X u) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    have hi := PI.UnitaryDimensionFormula.kset_inv hs
    simpa [cj, mul_assoc, mul_inv_rev] using hi
  have hg := NormCutK.colGood X u 1 s hk1 hk2
  simpa [cj, mul_assoc] using hg

theorem idxHom : IdxHom := by
  intro D X Y u _
  refine ⟨NormCutK.levi_one (TR := Y.TR), fun s t hs ht => ?_, fun s hs hKu v => ?_⟩
  · have hst : cj X u (s * t) = cj X u s * cj X u t := by
      simp [cj, mul_assoc]
    rw [hst, NormCutK.levi_mul (TR := Y.TR) (cj_good u s hs) (cj_good u t ht)]
  · exact NormCutK.unitriangular_reduction_of_mem_level (TR := Y.TR) (cj_good u s hs) hKu v

end PI.UnitaryDimensionFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGeFull

section

@[expose] public section

namespace PI.UnitaryDimensionFormula

theorem indexGe : IndexGe := indexGe_of uniSub idxHom (idxSurj_of_frame idxDFrame)

end PI.UnitaryDimensionFormula
end
end
