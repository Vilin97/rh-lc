module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StPuncturedExpOrder
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg

-- Source module: GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology

namespace MCInvEntryDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}

theorem differentiableAt_det {M : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hM : ∀ j l, DifferentiableAt ℝ (fun q => M q j l) p) :
    DifferentiableAt ℝ (fun q => (M q).det) p := by
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul
      (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i q => M q (σ i) i)
        fun i _ => (hM _ _).hasFDerivAt).differentiableAt

theorem inv_entry_eq (A : Matrix (Fin g) (Fin g) ℝ) (j l : Fin g) :
    A⁻¹ j l = (A.det)⁻¹ * (A.updateRow l (Pi.single j 1)).det := by
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]

theorem differentiableAt_inv_entry {Y : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hY : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p) (hdet : (Y p).det ≠ 0) (j l : Fin g) :
    DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p := by
  simp only [inv_entry_eq]
  refine ((differentiableAt_det hY).inv hdet).mul (differentiableAt_det fun k m => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hY k m

end MCInvEntryDeriv

theorem InvEntryDeriv.proof (h₁ : InvEntryBound.Statement) : InvEntryDeriv.Statement := by
  intro E _ _ g Y p c b hc hpsd hY
  have hpd : (Y p).PosDef := MCBounds.posDef_of_ge hc hpsd
  have hdet : (Y p).det ≠ 0 := hpd.det_pos.ne'
  have hYd : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p := fun j l => (hY j l).1
  have hZd := MCInvEntryDeriv.differentiableAt_inv_entry hYd hdet
  have hnear : ∀ᶠ q in 𝓝 p, (Y q).det ≠ 0 :=
    (MCInvEntryDeriv.differentiableAt_det hYd).continuousAt.eventually_ne hdet

  have key : ∀ j m, ∑ s, Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p =
      -∑ s, (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p := by
    intro j m
    have hconst : (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) =ᶠ[𝓝 p]
        fun _ => (1 : Matrix (Fin g) (Fin g) ℝ) j m := by
      filter_upwards [hnear] with q hq
      rw [← Matrix.mul_apply, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq)]
    have h1 : fderiv ℝ (fun q => ∑ s, Y q j s * (Y q)⁻¹ s m) p =
        ∑ s, (Y p j s • fderiv ℝ (fun q => (Y q)⁻¹ s m) p +
          (Y p)⁻¹ s m • fderiv ℝ (fun q => Y q j s) p) := by
      rw [fderiv_fun_sum (u := Finset.univ) (A := fun s q => Y q j s * (Y q)⁻¹ s m)
        (fun s _ => (hYd j s).mul (hZd s m))]
      exact Finset.sum_congr rfl fun s _ => fderiv_fun_mul (hYd j s) (hZd s m)
    rw [hconst.fderiv_eq, fderiv_const_apply, Finset.sum_add_distrib] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have form : ∀ j l, fderiv ℝ (fun q => (Y q)⁻¹ j l) p =
      -∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p := by
    intro j l
    have hZY : (Y p)⁻¹ * Y p = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
    calc fderiv ℝ (fun q => (Y q)⁻¹ j l) p
        = ∑ s, ((Y p)⁻¹ * Y p) j s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          simp only [hZY, Matrix.one_apply, ite_smul, one_smul, zero_smul,
            Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      _ = ∑ m, (Y p)⁻¹ j m • ∑ s, Y p m s • fderiv ℝ (fun q => (Y q)⁻¹ s l) p := by
          simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          simp only [key, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib]
  intro j l
  refine ⟨hZd j l, ?_⟩
  rw [form, norm_neg]
  have hinv := h₁ g (Y p) c hc hpsd
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  calc ‖∑ m, ∑ s, ((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖
      ≤ ∑ m, ∑ s, ‖((Y p)⁻¹ j m * (Y p)⁻¹ s l) • fderiv ℝ (fun q => Y q m s) p‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
    _ ≤ ∑ _m : Fin g, ∑ _s : Fin g, c⁻¹ * c⁻¹ * b := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun s _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (mul_le_mul (hinv j m) (hinv s l) (abs_nonneg _) hci) (hY m s).2
          (norm_nonneg _) (mul_nonneg hci hci)
    _ = (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCLogDetGramDeriv

def constK (g k : ℕ) : ℝ := (k.factorial : ℝ) * k * ((g : ℝ) ^ 2) ^ k * ((g : ℝ) ^ 2 + 2) + 1

theorem constK_pos (g k : ℕ) : 0 < constK g k := by
  unfold constK; positivity

theorem key_bound (g k : ℕ) (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    (k.factorial : ℝ) * k * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ (k - 1) *
        ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b))) ≤
      constK g k * (1 + a) ^ (2 * k) * (1 + x) ^ (k + 1) * (1 + b) := by
  rcases k with _ | n
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    have := constK_pos g 0
    positivity
  · simp only [Nat.add_sub_cancel]
    have hx1 : 1 ≤ 1 + x := by linarith
    have hA : (a ^ 2) ^ n * a ^ 2 ≤ (1 + a) ^ (2 * (n + 1)) := by
      rw [← pow_succ, pow_mul]
      gcongr
      linarith
    have hX1 : x ^ (n + 1) ≤ (1 + x) ^ (n + 1 + 1) :=
      (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ hx1 (by omega))
    have hX2 : x ^ (n + 2) ≤ (1 + x) ^ (n + 1 + 1) := pow_le_pow_left₀ hx (by linarith) _
    have hbr : 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
        ((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
      have h1 : 2 * x ^ (n + 1) ≤ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        have : (1 + x) ^ (n + 1 + 1) ≤ (1 + x) ^ (n + 1 + 1) * (1 + b) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        linarith
      have h2 : (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
          (g : ℝ) ^ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        rw [mul_assoc]
        gcongr
        have : 0 ≤ x ^ (n + 2) := by positivity
        nlinarith
      linarith
    have hP : 0 ≤ ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) := by
      positivity
    have hbr0 : 0 ≤ 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b := by positivity
    calc ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ n *
          ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b)))
        = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            ((a ^ 2) ^ n * a ^ 2) * (2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b) := by
          ring
      _ ≤ (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            (1 + a) ^ (2 * (n + 1)) * (((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b))) := by
          gcongr
      _ = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) *
            ((g : ℝ) ^ 2 + 2)) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          ring
      _ ≤ constK g (n + 1) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          gcongr
          unfold constK
          push_cast
          linarith
      _ = constK g (n + 1) * (1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b) := by ring

end MCLogDetGramDeriv


open MCLogDetGramDeriv in
theorem LogDetGramDeriv.proof (h₁ : InvEntryBound.Statement) (h₂ : InvEntryDeriv.Statement)
    (h₃ : MatrixDetDeriv.Statement) (h₄ : GramEntryDeriv.Statement) :
    LogDetGramDeriv.Statement := by
  intro g k
  refine ⟨constK g k, constK_pos g k, ?_⟩
  intro E _ _ F Y p a b c μ hc hμ ha hb hF hY hYc hdet
  have hZ : ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧ |(Y p)⁻¹ j l| ≤ c⁻¹ ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := fun j l =>
    ⟨(h₂ g Y p c b hc hYc hY j l).1, h₁ g (Y p) c hc hYc j l, (h₂ g Y p c b hc hYc hY j l).2⟩
  have hG := h₄ g k F (fun q => (Y q)⁻¹) p a c⁻¹ ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b) hF hZ
  have hD := h₃ k (fun q => (F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q) p
    ((g : ℝ) ^ 2 * a ^ 2 * c⁻¹)
    ((g : ℝ) ^ 2 * (2 * a ^ 2 * c⁻¹ + a ^ 2 * ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b))) hG
  set d : E → ℂ := fun q => ((F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q).det with hd_def
  have hpos : 0 < (d p).re := lt_of_lt_of_le hμ hdet
  have hre : HasFDerivAt (fun q => (d q).re) (Complex.reCLM.comp (fderiv ℝ d p)) p := by
    have := Complex.reCLM.hasFDerivAt.comp p hD.1.hasFDerivAt
    simpa [Function.comp_def] using this
  have hL := hre.log hpos.ne'
  have hfun : (fun q => logDetGram (Y q) (F q)) = fun q => Real.log (d q).re := by
    funext q; rfl
  rw [hfun]
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  have hnorm : ‖Complex.reCLM.comp (fderiv ℝ d p)‖ ≤ ‖fderiv ℝ d p‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.reCLM_norm, one_mul]
  have hkey := key_bound g k a b c⁻¹ ha hb (inv_nonneg.mpr hc.le)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  calc (d p).re⁻¹ * ‖Complex.reCLM.comp (fderiv ℝ d p)‖
      ≤ (d p).re⁻¹ * ‖fderiv ℝ d p‖ := by gcongr
    _ = ‖fderiv ℝ d p‖ / (d p).re := by ring
    _ ≤ ‖fderiv ℝ d p‖ / μ := by gcongr
    _ ≤ constK g k * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ := by
      gcongr
      exact hD.2.trans hkey

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace MCMatrixDetDeriv

theorem prod_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (g : ι → E → ℂ) (p : E) (A B : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (g i) p ∧ ‖g i p‖ ≤ A ∧ ‖fderiv ℝ (g i) p‖ ≤ B) :
    DifferentiableAt ℝ (fun q => ∏ i ∈ s, g i q) p ∧
      ‖fderiv ℝ (fun q => ∏ i ∈ s, g i q) p‖ ≤ (s.card : ℝ) * A ^ (s.card - 1) * B := by
  have hd : HasFDerivAt (fun q => ∏ i ∈ s, g i q)
      (∑ i ∈ s, (∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p) p :=
    HasFDerivAt.finsetProd fun i hi => (h i hi).1.hasFDerivAt
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  calc ‖∑ i ∈ s, (∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p‖
      ≤ ∑ i ∈ s, ‖(∏ j ∈ s.erase i, g j p) • fderiv ℝ (g i) p‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, A ^ (s.card - 1) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hA : 0 ≤ A := (norm_nonneg _).trans (h i hi).2.1
        have hprod : ‖∏ j ∈ s.erase i, g j p‖ ≤ A ^ (s.card - 1) := by
          rw [norm_prod, ← Finset.card_erase_of_mem hi, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun j hj => (h j (Finset.mem_of_mem_erase hj)).2.1)
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        exact mul_le_mul hprod (h i hi).2.2 (norm_nonneg _) (pow_nonneg hA _)
    _ = (s.card : ℝ) * A ^ (s.card - 1) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end MCMatrixDetDeriv

theorem MatrixDetDeriv.proof : MatrixDetDeriv.Statement := by
  intro E _ _ k H p A B h
  classical
  have hexp : (fun q => (H q).det) =
      fun q => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i := by
    funext q
    exact Matrix.det_apply' (H q)
  have hterm : ∀ σ : Equiv.Perm (Fin k),
      DifferentiableAt ℝ (fun q => ∏ i, H q (σ i) i) p ∧
        ‖fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖ ≤ (k : ℝ) * A ^ (k - 1) * B := by
    intro σ
    have := MCMatrixDetDeriv.prod_fderiv_le (Finset.univ : Finset (Fin k))
      (fun i q => H q (σ i) i) p A B (fun i _ => h (σ i) i)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hd : HasFDerivAt (fun q => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, H q (σ i) i)
      (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p) p :=
    HasFDerivAt.fun_sum fun σ _ => ((hterm σ).1.hasFDerivAt).const_mul _
  rw [hexp]
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  calc ‖∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) •
        fderiv ℝ (fun q => ∏ i, H q (σ i) i) p‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), (k : ℝ) * A ^ (k - 1) * B := by
        apply Finset.sum_le_sum
        intro σ _
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
        rw [hs, one_mul]
        exact (hterm σ).2
    _ = (k.factorial : ℝ) * k * A ^ (k - 1) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        ring

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement :=
  GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
end
end
