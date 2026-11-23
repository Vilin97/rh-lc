module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.UTransEMp

section

@[expose] public section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section muSS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def QN (k r : ℕ) : Measure (U.RC k r 0 × (G.UT r → ℂ)) := (U.muRC k r 0).prod volume

instance (k r : ℕ) : SigmaFinite (U.muRC k r 0) := Dx2.SplitF.sf_RC r 0

instance (k r : ℕ) : SFinite (QN k r) := by unfold QN; infer_instance

def TN (k r : ℕ) (p : (Mt k r × (U.RC k r 0 × (G.UT r → ℂ))) × (Mt k r × (U.RC k r 0 × (G.UT r → ℂ)))) :
    B.SS k r :=
  ((p.1.1, psiR k r p.1.2), (p.2.1, psiR k r p.2.2))

theorem TN_meas : Measurable (TN k r) := by
  unfold TN
  exact ((measurable_fst.comp measurable_fst).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_fst))).prodMk
    ((measurable_fst.comp measurable_snd).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_snd)))

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) :
    S.μSS = ((S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r))).map (TN k r) := by
  have hW : SigmaFinite S.μW := Dx2.MN.sigma_of_haar S.haarW
  have hW' : SigmaFinite S.μW' := Dx2.MN.sigma_of_haar S.haarW'
  have hN' : S.μN = (QN k r).map (psiR k r) := by rw [hN]; exact muN_rev (k := k) r
  unfold B.RealPlaceData.μSS
  rw [hN', ← Measure.map_id (μ := S.μW), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    ← Measure.map_id (μ := S.μW'), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    Measure.map_prod_map _ _ (measurable_id.prodMap (psiR_meas r)) (measurable_id.prodMap (psiR_meas r)),
    Measure.map_id, Measure.map_id]
  rfl

end muSS

section utrans

variable {r : ℕ} {X : Type} [MeasurableSpace X]

theorem ut_of_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : G.upper (StabilizerDisintegration.utc A) = A := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (ne_of_lt h), dite_eq_left h, zero_add]
  · subst h
    rw [if_pos rfl, dite_eq_right (lt_irrefl _), add_zero, hA.2 i]
  · rw [if_neg (ne_of_gt h), dite_eq_right (not_lt.2 h.le), add_zero, hA.1 i j h]

theorem ut_inv_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : A⁻¹ ∈ C2.UTset r := by
  have hT : Matrix.BlockTriangular A id := fun i j hij => hA.1 i j hij
  have hu : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hT]
    simp [hA.2]
  haveI := Matrix.invertibleOfIsUnitDet A hu
  have hTi : Matrix.BlockTriangular A⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨fun i j hij => hTi hij, fun i => ?_⟩
  have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [hA.2, one_mul] at h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hTi h, mul_zero]
  · simp

theorem ut_det {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : IsUnit A.det := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hA.1 i j hij)]
  simp [hA.2]

def uTransE (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j) :
    (X × (G.UT r → ℂ)) ≃ᵐ (X × (G.UT r → ℂ)) where
  toFun p := (p.1, StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2))
  invFun p := (p.1, StabilizerDisintegration.utc (A p.1 * G.upper p.2))
  left_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (ut_inv_mem (hA p.1)) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  right_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (hA p.1) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  measurable_toFun := by
    refine measurable_fst.prodMk ?_
    refine Measurable.of_eval fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAi _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd
  measurable_invFun := by
    refine measurable_fst.prodMk ?_
    refine Measurable.of_eval fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAc _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd

theorem uTransE_mp (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j)
    (μ : Measure X) [SFinite μ] :
    MeasurePreserving (uTransE A hA hAc hAi) (μ.prod volume) (μ.prod volume) := by
  have h := MeasurePreserving.skew_product (f := id) (g := fun x u => StabilizerDisintegration.utc ((A x)⁻¹ * G.upper u))
    (MeasurePreserving.id μ) (measurable_snd.comp (uTransE A hA hAc hAi).measurable)
    (Filter.Eventually.of_forall fun x => (StabilizerDisintegration.utLeft r _ (ut_inv_mem (hA x))).map_eq)
  exact h

end utrans

end Formalism.FourierDecayAlt.P.PBM
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree

section

@[expose] public section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section perms

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc]
  [SFinite μd]

theorem measurePreserving_prod_perm_one : MeasurePreserving (fun p : α × (β × (γ × δ)) => ((p.1, p.2.2.2), (p.2.2.1, p.2.1)))
    (μa.prod (μb.prod (μc.prod μd))) ((μa.prod μd).prod (μc.prod μb)) := by
  have h1 := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc.prod μd))
  have h2 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μc) (ν := μd)).prod (MeasurePreserving.id μb))
  have h3 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μd μc μb)
  have h4 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μd (μc.prod μb))
  exact h4.comp (h3.comp (h2.comp h1))

theorem measurePreserving_prod_perm_two : MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.2.2, p.1.2)))
    ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μd.prod μb)) := by
  have g1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have g2 := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc.prod μd))
  have g3 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μd μb)
  have g4 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μd.prod μb))
  exact g4.comp (g3.comp (g2.comp g1))

theorem measurePreserving_prod_perm_three : MeasurePreserving (fun p : α × ((β × γ) × δ) => ((p.2.1.1, p.1), (p.2.1.2, p.2.2)))
    (μa.prod ((μb.prod μc).prod μd)) ((μb.prod μa).prod (μc.prod μd)) := by
  have k1 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd)
  have k2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb (μc.prod μd))
  have k3 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id (μc.prod μd))
  exact k3.comp (k2.comp k1)

end perms

section phi

variable {k r : ℕ} (σ : Equiv.Perm (Fin r)) (y1 y1' : B.Mat k 0)
  (A : (C2.Lstidx σ.symm → ℂ) → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r)
  (hAc : ∀ i j, Measurable fun x => A x i j) (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j)

def phiC (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) :=
  ((rnAct y1 p.2.1.1, StabilizerDisintegration.UC.fSp σ.symm (p.1, fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q))),
   (rnAct y1' p.2.1.2, StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2.2.2.2)))

instance : SFinite (U.muRC k r 0) := inferInstance

instance : SFinite (U.muXiH r 0 σ) := by unfold U.muXiH; infer_instance

include hA hAc hAi in
theorem phiC_mp (hy1 : y1 ∈ B.GV k 0) (hy1' : y1' ∈ B.GV k 0) :
    MeasurePreserving (phiC σ y1 y1' A) ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ))
      ((QN k r).prod (QN k r)) := by
  have := Dx2.SL.probT r

  have hin : MeasurePreserving (fun t : U.XiH r 0 σ => (fun q => t.2.1 (StabilizerDisintegration.UC.iota σ q), t.2.2))
      (U.muXiH r 0 σ) ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))) := by
    have h1 := Dx2.SL.dropE_mp ((Fin 0 → Fin r → ℂ) × (Fin r → Fin 0 → ℂ)) ((U.LW σ → ℂ) × (G.UT r → ℂ))
      volume ((volume : Measure (U.LW σ → ℂ)).prod volume)
    have h2 : MeasurePreserving (Prod.map (fun (y : U.LW σ → ℂ) (q : C2.LPidx σ.symm) => y (StabilizerDisintegration.UC.iota σ q)) id)
        ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (G.UT r → ℂ)))
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod volume) :=
      (Dx2.SL.reindex_mp (StabilizerDisintegration.UC.iota σ)).prod (MeasurePreserving.id _)
    have := h2.comp h1
    unfold U.muXiH
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod (α := U.LW σ → ℂ)]
    convert this using 1
    funext t
    rfl
  have hA' : MeasurePreserving
      (fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        (p.1, (p.2.1, (fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q), p.2.2.2.2))))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (((U.muRC k r 0).prod (U.muRC k r 0)).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))))) :=
    (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hin)
  have hC := measurePreserving_prod_perm_one (volume : Measure (C2.Lstidx σ.symm → ℂ)) ((U.muRC k r 0).prod (U.muRC k r 0))
    (volume : Measure (C2.LPidx σ.symm → ℂ)) (volume : Measure (G.UT r → ℂ))
  have hD : MeasurePreserving (Prod.map (uTransE A hA hAc hAi) id)
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod ((U.muRC k r 0).prod (U.muRC k r 0))))
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod ((U.muRC k r 0).prod (U.muRC k r 0)))) :=
    (uTransE_mp A hA hAc hAi _).prod (MeasurePreserving.id _)
  have hE := measurePreserving_prod_perm_two (volume : Measure (C2.Lstidx σ.symm → ℂ)) (volume : Measure (G.UT r → ℂ))
    (volume : Measure (C2.LPidx σ.symm → ℂ)) ((U.muRC k r 0).prod (U.muRC k r 0))
  have hF : MeasurePreserving
      (Prod.map (StabilizerDisintegration.UC.fSp σ.symm) (Prod.map (Prod.map (rnAct (j := r) y1) (rnAct (j := r) y1')) id))
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (C2.LPidx σ.symm → ℂ))).prod
        (((U.muRC k r 0).prod (U.muRC k r 0)).prod (volume : Measure (G.UT r → ℂ))))
      ((volume : Measure (G.UT r → ℂ)).prod (((U.muRC k r 0).prod (U.muRC k r 0)).prod
        (volume : Measure (G.UT r → ℂ)))) := by
    refine MeasurePreserving.prod ?_ (((rnAct_mp y1 hy1).prod (rnAct_mp y1' hy1')).prod (MeasurePreserving.id _))
    have := StabilizerDisintegration.UC.fSp_mp σ.symm
    rw [Measure.volume_eq_prod] at this
    exact this
  have hG := measurePreserving_prod_perm_three (volume : Measure (G.UT r → ℂ)) (U.muRC k r 0) (U.muRC k r 0) (volume : Measure (G.UT r → ℂ))
  have := hG.comp (hF.comp (hE.comp (hD.comp (hC.comp hA'))))
  unfold QN
  convert this using 1
  funext p
  rfl

def psiC (q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) :
    (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ :=
  (((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1,
    ((rnAct y1⁻¹ q.1.1, rnAct y1'⁻¹ q.2.1),
      (default, (fun l => ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).2 ((StabilizerDisintegration.UC.iota σ).symm l),
        StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 * G.upper q.2.2)))))

theorem rnAct_inv_rnAct {a : B.Mat k 0} (ha : IsUnit a.det) (x : U.RC k r 0) : rnAct a⁻¹ (rnAct a x) = x := by
  simp only [rnAct, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
    Equiv.symm_apply_apply]

theorem rnAct_rnAct_inv {a : B.Mat k 0} (ha : IsUnit a.det) (x : U.RC k r 0) : rnAct a (rnAct a⁻¹ x) = x := by
  simp only [rnAct, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
    Equiv.symm_apply_apply]

theorem rnAct_meas (a : B.Mat k 0) : Measurable (rnAct (j := r) a) := by
  have h : (rnAct (j := r) a) = fun x => (Matrix.of.symm (a * Matrix.of x.1), x.2) := by
    funext x
    rfl
  rw [h]
  refine Measurable.prodMk ?_ measurable_snd
  refine Measurable.of_eval (fun i => Measurable.of_eval (fun l => ?_))
  change Measurable fun x : U.RC k r 0 => ∑ m, a i m * x.1 m l
  exact Finset.measurable_sum _ (fun m _ => measurable_const.mul
    ((measurable_pi_apply l).comp ((measurable_pi_apply m).comp measurable_fst)))

include hA in
theorem psiC_phiC (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) :
    Function.LeftInverse (psiC σ y1 y1' A) (phiC σ y1 y1' A) := by
  intro p
  obtain ⟨x0, ⟨⟨a, b⟩, ⟨e, ⟨v, u⟩⟩⟩⟩ := p
  have hM : (A x0)⁻¹ * G.upper u ∈ C2.UTset r :=
    StabilizerDisintegration.HC.UT_mul (ut_inv_mem (hA x0)) (StabilizerDisintegration.HC.upper_mem u)
  have hE : (StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.fSp σ.symm (x0, fun q => v (StabilizerDisintegration.UC.iota σ q))) =
      (x0, fun q => v (StabilizerDisintegration.UC.iota σ q)) := (StabilizerDisintegration.UC.eSp σ.symm).symm_apply_apply _
  have hU : A x0 * G.upper (StabilizerDisintegration.utc ((A x0)⁻¹ * G.upper u)) = G.upper u := by
    rw [ut_of_mem hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_det (hA x0)), Matrix.one_mul]
  simp only [psiC, phiC, hE, rnAct_inv_rnAct hy1, rnAct_inv_rnAct hy1', Equiv.apply_symm_apply, hU,
    StabilizerDisintegration.HC.utc_upper, Prod.mk.injEq, and_true, true_and]
  exact Subsingleton.elim _ _

include hA in
theorem phiC_psiC (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) :
    Function.RightInverse (psiC σ y1 y1' A) (phiC σ y1 y1' A) := by
  intro q
  obtain ⟨⟨x1, w1⟩, ⟨x2, w2⟩⟩ := q
  have hE : StabilizerDisintegration.UC.fSp σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm w1) = w1 := (StabilizerDisintegration.UC.eSp σ.symm).apply_symm_apply w1
  have hM : A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1 * G.upper w2 ∈ C2.UTset r :=
    StabilizerDisintegration.HC.UT_mul (hA _) (StabilizerDisintegration.HC.upper_mem w2)
  have hU : (A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1)⁻¹ *
      G.upper (StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1 * G.upper w2)) = G.upper w2 := by
    rw [ut_of_mem hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_det (hA _)), Matrix.one_mul]
  simp only [psiC, phiC, rnAct_rnAct_inv hy1, rnAct_rnAct_inv hy1', Equiv.symm_apply_apply, Prod.mk.eta, hE, hU,
    StabilizerDisintegration.HC.utc_upper]

include hA hAc hAi in
theorem phiC_emb (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) : MeasurableEmbedding (phiC σ y1 y1' A) := by
  have hup : ∀ m j : Fin r, Measurable fun v : G.UT r → ℂ => G.upper v m j := by
    intro m j
    by_cases h : m < j
    · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_pos h]
      exact measurable_const.add (measurable_pi_apply _)
    · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
      exact measurable_const
  have hmφ : Measurable (phiC σ y1 y1' A) := by
    have h1 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => rnAct y1 p.2.1.1 :=
      (rnAct_meas y1).comp measurable_snd.fst.fst
    have h2 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        StabilizerDisintegration.UC.fSp σ.symm (p.1, fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q)) :=
      (StabilizerDisintegration.UC.eSp σ.symm).measurable.comp (measurable_fst.prodMk (Measurable.of_eval fun q =>
        (measurable_pi_apply _).comp measurable_snd.snd.snd.fst))
    have h3 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => rnAct y1' p.2.1.2 :=
      (rnAct_meas y1').comp measurable_snd.fst.snd
    have h4 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2.2.2.2) := by
      refine Measurable.of_eval fun q => ?_
      change Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        ∑ m, (A p.1)⁻¹ q.1.1 m * G.upper p.2.2.2.2 m q.1.2
      exact Finset.measurable_sum _ fun m _ => ((hAi _ _).comp measurable_fst).mul
        ((hup m _).comp measurable_snd.snd.snd.snd)
    exact (h1.prodMk h2).prodMk (h3.prodMk h4)
  have hmψ : Measurable (psiC σ y1 y1' A) := by
    have hes : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        (StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2 :=
      (StabilizerDisintegration.UC.eSp σ.symm).symm.measurable.comp measurable_fst.snd
    have g1 := hes.fst
    have g2 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        rnAct y1⁻¹ q.1.1 := (rnAct_meas y1⁻¹).comp measurable_fst.fst
    have g3 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        rnAct y1'⁻¹ q.2.1 := (rnAct_meas y1'⁻¹).comp measurable_snd.fst
    have g5 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        fun l => ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).2 ((StabilizerDisintegration.UC.iota σ).symm l) :=
      Measurable.of_eval fun l => (measurable_pi_apply _).comp hes.snd
    have g6 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 * G.upper q.2.2) := by
      refine Measurable.of_eval fun q' => ?_
      change Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        ∑ m, A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 q'.1.1 m * G.upper q.2.2 m q'.1.2
      exact Finset.measurable_sum _ fun m _ => ((hAc _ _).comp g1).mul
        ((hup _ _).comp measurable_snd.snd)
    exact g1.prodMk ((g2.prodMk g3).prodMk (measurable_const.prodMk (g5.prodMk g6)))
  let e : ((C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) ≃ᵐ
      ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) :=
    { toFun := phiC σ y1 y1' A
      invFun := psiC σ y1 y1' A
      left_inv := psiC_phiC σ y1 y1' A hA hy1 hy1'
      right_inv := phiC_psiC σ y1 y1' A hA hy1 hy1'
      measurable_toFun := hmφ
      measurable_invFun := hmψ }
  exact e.measurableEmbedding

end phi

end Formalism.FourierDecayAlt.P.PBM
end
end
end
