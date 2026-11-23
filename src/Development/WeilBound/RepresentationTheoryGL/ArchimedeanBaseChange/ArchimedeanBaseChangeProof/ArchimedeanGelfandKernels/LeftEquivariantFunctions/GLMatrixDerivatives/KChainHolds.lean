module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFactsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.GelfandReading
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ConjTInvInv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ContDiffAtMatmul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HasDerivAtFderivLine
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbBase
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbCurve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HermInvConj
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.DetMulConjTNe

section

@[expose] public section

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr PositivityTheory.RgBcC.LfSt.Kchain.KbDer
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem det_mul_conjT_ne {y : Mat n} (hy : y ∈ GLs n) : (y * yᴴ).det ≠ 0 := mul_mem hy (conjT_mem hy)

theorem contDiffAt_wt (c : ℝ) {y : Mat n} (hy : y ∈ GLs n) : ContDiffAt ℝ ∞ (fun y' : Mat n => wt c y') y := by
  unfold wt
  have h1 : ContDiffAt ℝ ∞ (fun y' : Mat n => (y' * y'ᴴ).det) y :=
    contDiff_det.contDiffAt.comp y (contDiffAt_matmul contDiffAt_id contDiff_conjT.contDiffAt)
  exact contDiffAt_const.mul ((h1.pow n).inv (pow_ne_zero _ (det_mul_conjT_ne hy)))

theorem wt_line (c : ℝ) (y : Mat n) {X : Mat n} (hX : X.IsHermitian) (t : ℝ) :
    wt c (y * (1 + t • X)) = (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹) := by
  unfold wt
  have e : (y * (1 + t • X)) * (y * (1 + t • X))ᴴ = y * ((1 + t • X) * (1 + t • X)) * yᴴ := by
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  rw [show y.det * ((1 + t • X).det * (1 + t • X).det) * yᴴ.det = (y.det * yᴴ.det) * (1 + t • X).det ^ 2 by ring,
    mul_pow, ← pow_mul, mul_inv, mul_assoc]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derTwo_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n)) (c : ℝ)
    {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) {y : Mat n} (hy : y ∈ GLs n) {X : Mat n} (hX : X.IsHermitian) :
    fderiv ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y (y * X) =
      wt c y • (Fr x * (((-(2 * n : ℂ)) * X.trace) • k (x⁻¹ * d * yᴴ⁻¹) * Γ * T -
        Rd X k (x⁻¹ * d * yᴴ⁻¹) * Γ * T - k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * fderiv ℝ Fr 1 X) * Fr y⁻¹) := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) y :=
    contDiffAt_matmul contDiffAt_const ((contDiffAt_inv (conjT_mem hy)).comp y contDiff_conjT.contDiffAt)
  have hdiff : DifferentiableAt ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun y' : Mat n => k (x⁻¹ * d * y'ᴴ⁻¹)) y :=
      hkw.comp y (hg.differentiableAt (by simp))
    have h2 : DifferentiableAt ℝ (fun y' : Mat n => Fr y'⁻¹) y :=
      (diffAt_of h.smooth (inv_mem hy)).comp y ((contDiffAt_inv hy).differentiableAt (by simp))
    exact ((contDiffAt_wt c hy).differentiableAt (by simp)).smul
      ((((h1.const_mul (Fr x)).mul_const Γ).mul_const T).mul h2)
  have h1 := hasDerivAt_fderiv_line hdiff (y * X)
  have hq := (hasDerivAt_detLine X).fun_pow (2 * n)
  have hq0 : ((1 + (0 : ℝ) • X).det) ^ (2 * n) ≠ 0 := by simp
  have hW := (hq.fun_inv hq0).const_mul ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹)
  have hc : HasDerivAt (fun t : ℝ => w * (1 + t • X)⁻¹) (w * (-X)) 0 :=
    (hasDerivAt_matmul (hasDerivAt_const (0 : ℝ) w) (hasDerivAt_lineInv X)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k (w * (1 + t • X)⁻¹)) (fderiv ℝ k w (w * (-X))) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hP : HasDerivAt (fun t : ℝ => Fr (1 + t • X)⁻¹) (fderiv ℝ Fr 1 (-X)) 0 :=
    (diffAt_of h.smooth one_mem).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineInv X) (by simp)
  have hB := (((hK.const_mul (Fr x)).mul_const Γ).mul_const T).fun_mul (hP.mul_const (Fr y⁻¹))
  have h2 := hW.fun_smul hB
  have e : ∀ᶠ t : ℝ in 𝓝 0, wt c (y + t • (y * X)) • Kf Fr k Γ T d x (y + t • (y * X)) =
      ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹)) •
        (Fr x * k (w * (1 + t • X)⁻¹) * Γ * T * (Fr (1 + t • X)⁻¹ * Fr y⁻¹)) := by
    filter_upwards [line_mem X] with t ht
    have e1 : y + t • (y * X) = y * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [e1, wt_line c y hX t]
    congr 1
    unfold Kf
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      h.mul _ (inv_mem ht) _ (inv_mem hy)]
    simp only [hwdef, Matrix.mul_assoc, _root_.mul_assoc]
  have h2' := h2.congr_of_eventuallyEq e
  rw [h1.unique h2']
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul, h.one, _root_.one_mul, Matrix.det_one,
    one_pow, inv_one, _root_.mul_one, map_neg, Matrix.mul_neg, Rd]
  have ew : (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ = wt c y := rfl
  rw [ew]
  simp only [smul_sub, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_neg, mul_neg, neg_mul, smul_add, mul_add,
    add_mul, _root_.mul_assoc, smul_smul]
  push_cast
  ring_nf
  abel_nf

theorem derTwo : DerTwo := fun _ _ _ _ _ _ _ _ _ h _ hk c _ _ hd hx _ hy _ hX => derTwo_at h hk c hd hx hy hX

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual

section

@[expose] public section

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem trace_hOf_mul (hH : HbFacts) (u u' : Fin n × Fin n → ℝ) :
    (hOf u * hOf u').trace = ∑ p, ((u p * u' p : ℝ) : ℂ) := by
  obtain ⟨-, horth, -⟩ := hH n
  simp only [hOf, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, horth, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  push_cast
  ring

theorem map_hOf {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (u : Fin n × Fin n → ℝ) : α (hOf u) = ∑ p, ((u p : ℝ) : ℂ) • α (hb p) := by

  simp only [hOf, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ((u p : ℝ) : ℂ) • (hb p : Mat n) = (u p) • hb p := by
    ext a b
    simp [Complex.real_smul]
  rw [e, map_smul]
  ext v
  simp [Complex.coe_smul]

theorem dualSum (hH : HbFacts) : DualSum := by
  intro n V _ _ α β A A' hA hA' htr
  obtain ⟨-, -, hcoord, -, -, -, -, -⟩ := hH n
  set a : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A i) p with ha
  set a' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A' i) p with ha'
  have eA : ∀ i, A i = hOf (a i) := fun i => (hcoord _ (hA i)).symm
  have eA' : ∀ i, A' i = hOf (a' i) := fun i => (hcoord _ (hA' i)).symm
  have h1 : a * a'ᵀ = 1 := by
    ext i j
    have := htr i j
    rw [eA i, eA' j, trace_hOf_mul hH] at this
    have hre := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [hre]
    split_ifs <;> simp
  have h2 : a'ᵀ * a = 1 := mul_eq_one_comm.mp h1
  calc ∑ i, α (A i) * β (A' i)
      = ∑ i, ∑ p, ∑ q, ((a i p * a' i q : ℝ) : ℂ) • (α (hb p) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eA i, eA' i, map_hOf α, map_hOf β, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [smul_mul_smul_comm]
        push_cast
        rfl
    _ = ∑ p, ∑ q, ((a'ᵀ * a) q p : ℂ) • (α (hb p) * β (hb q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ p, α (hb p) * β (hb p) := by
        rw [h2]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Matrix.one_apply]

end PositivityTheory.RgBcC.LfSt.Kchain.KcDual
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Kchain

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_mul {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero ha hb

theorem mem_GLs_inv {a : Mat n} (ha : a ∈ GLs n) : a⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at *
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero ha

theorem mem_GLs_conjT_inv {a : Mat n} (ha : a ∈ GLs n) : aᴴ⁻¹ ∈ GLs n := by
  apply mem_GLs_inv
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_conjTranspose] at *
  exact (star_ne_zero).mpr ha

theorem kChain_of (hS : KcSmooth) (hC : ConeGL) (h1 : HalfOne) (h2 : HalfTwo) : KChain := by
  intro n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK hch d hd c
  refine ⟨hS n E.V σ c Fr k Γ T d hd hσ hσ2 h.smooth hk, ?_, ?_⟩
  · rintro ⟨v, w⟩ ⟨hv, hw⟩
    have hxv := (hC n σ hσ2 v hv).1
    have hxw := (hC n σ hσ2 w hw).1
    have hw0 : (σ v)⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      mem_GLs_mul (mem_GLs_mul (mem_GLs_inv hxv) hd) (mem_GLs_conjT_inv hxw)
    have e1 := h.ΓFr _ hxv
    have e2 := (hch _ hw0).1
    have e4 := h.ΓFr _ (mem_GLs_inv hxw)
    have e3 := h.ΓT
    simp only [Kc, Kf]
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    have hcm : Commute Γ (Fr (σ v) * k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * Γ * T * Fr (σ w)⁻¹) :=
      ((((show Commute Γ (Fr (σ v)) from e1).mul_right (show Commute Γ (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) from e2)).mul_right
        (Commute.refl Γ)).mul_right (show Commute Γ T from e3)).mul_right (show Commute Γ (Fr (σ w)⁻¹) from e4)
    exact hcm.eq
  · rintro ⟨v, w⟩ ⟨hv, hw⟩
    rw [h1 n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK d hd c v hv w hw,
      h2 n lam E Fr ε ι S Γ T h σ hσ hσ2 k hk hkK d hd c v hv w hw, ← smul_add]
    have hxv := (hC n σ hσ2 v hv).1
    have hxw := (hC n σ hσ2 w hw).1
    have hw0 : (σ v)⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      mem_GLs_mul (mem_GLs_mul (mem_GLs_inv hxv) hd) (mem_GLs_conjT_inv hxw)
    have hc := (hch _ hw0).2
    set w0 := (σ v)⁻¹ * d * (σ w)ᴴ⁻¹
    have hz : (∑ p, ε (hb p) * (fderiv ℝ Fr 1 (hb p) * k w0 + Ld (hb p) k w0)) +
        ∑ p, (Rd (hb p) k w0 * ε (hb p) - k w0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) = 0 := by
      have e : ∑ p, ε (hb p) * (fderiv ℝ Fr 1 (hb p) * k w0 + Ld (hb p) k w0) =
          ∑ p, ε (hb p) * (Ld (hb p) k w0 + fderiv ℝ Fr 1 (hb p) * k w0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [add_comm]
      rw [e, hc, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun p _ => ?_
      simp only [neg_mul]
      abel
    rw [← add_mul, ← add_mul, ← add_mul, ← mul_add, ← smul_add, hz, smul_zero, mul_zero, zero_mul,
      zero_mul, zero_mul, smul_zero]

end PositivityTheory.RgBcC.LfSt.Kchain
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainTop

section

@[expose] public section

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt

theorem kChain (hH : HbFacts) (hF : FrameDer) : KChain :=
  kChain_of KcInv.kcSmooth KcInv.coneGL
    (KcHalf1.halfOne_of hH hF (fun n => KcHalf2.isOpen_cone (n := n) hH) KbDer.derOne)
    (KcHalf2.halfTwo_of hH hF KbFr.frComm KbDer2.derTwo (KcDual.dualSum hH))

end PositivityTheory.RgBcC.LfSt.Kchain
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KChainHolds

section

@[expose] public section

namespace PositivityTheory.RgBcC.LfSt

theorem kChain_holds : KChain := Kchain.kChain GlobalTheory.T.height_bound_facts (GelfandReading.frameDer_of GlobalTheory.T.height_bound_facts)

end PositivityTheory.RgBcC.LfSt
end
end
