module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepSuccOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.BStepSuccOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IndexEmbeddingBijective
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MeasurableHaarKernelTriple
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OsOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExponentConditionNeg
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoMulStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqInsSucc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqNonneg
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PolynomialGrowthIntegrals
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XphiLinInd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkMulVecMulVec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.CriticalExponentSucc
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntStepOf

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OscillatoryBound

section

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

lemma fS_scl {p m : ℕ} (s : Fin (p + 2) → ℝ) (hs0 : ∀ l, 0 ≤ s l) (τ : ℝ) (hτ : τ ∈ Icc (1 : ℝ) 2)
    (x : Xp (p + 1) m) : fS s (scl τ x) ≤ ENNReal.ofReal (2 ^ ∑ l, s l) * fS s x := by
  unfold fS
  rw [Real.rpow_sum_of_pos (by norm_num), ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro l _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := de_scl τ hτ.1 hτ.2 x l
  have h2 := de_ge_one x l
  calc de (scl τ x) l ^ (-s l) ≤ (de x l / 2) ^ (-s l) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith [hs0 l])
    _ = 2 ^ s l * de x l ^ (-s l) := by
        rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_inv_eq_mul, mul_comm]

lemma fS_rot {p m : ℕ} (s : Fin (p + 2) → ℝ) (t : ℝ) (x : Xp (p + 1) m) : fS s (rot t x) = fS s x := by
  unfold fS
  simp only [de_rot]

end OSAux

open OSAux in
theorem oscillatoryBound' (hT : TailFin) (hC1 : C1) (hS : SUB) (hK : KER) (hL : SLOW) : OS := by
  intro p m δ γ e hδ0 hδ1 hγ0 hγ hepos hsum
  set s : Fin (p + 2) → ℝ := fun l => s0N (p + 1) m l - e l with hs
  have hS0 : 0 ≤ ∑ i : Fin (p + 1), e i.succ := Finset.sum_nonneg (fun i _ => (hepos _).le)
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have hle : e l ≤ 1 := by
      refine Fin.cases ?_ (fun i => ?_) l
      · linarith [hepos 0]
      · have : e i.succ ≤ ∑ i : Fin (p + 1), e i.succ := Finset.single_le_sum
          (f := fun i : Fin (p + 1) => e i.succ) (fun j _ => (hepos _).le) (Finset.mem_univ i)
        linarith [hepos 0]
    have h1 : 1 ≤ s0N (p + 1) m l := by
      unfold s0N; split_ifs
      · norm_num
      · have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith
    simp only [hs]; linarith
  obtain ⟨Cr, hCr0, hrot⟩ := rot_weight hS hδ0 hδ1
  obtain ⟨C2, hC20, hscl⟩ := scl_weight hS hδ0 hδ1 hγ0 hγ
  obtain ⟨C3, hC3⟩ := tail_bound hT hC1 hK hL (m := m) e hγ0 (by linarith) hepos hsum
  set Ks : ℝ := 2 ^ ∑ l, s l with hKs
  have hKs0 : 0 ≤ Ks := by positivity
  refine ⟨Cr * Ks * C2 * max C3 0, ?_⟩
  intro η η' ζ c₀ hη
  set w0 : Xp (p + 1) m → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))
    with hw0d
  set w1 : Xp (p + 1) m → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + ‖linF η η' ζ x‖) ^ (-δ / 4)) with hw1d
  have hw0 : Measurable w0 :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable (fun r : ℂ => (1 + |2 * r.im + c₀|) ^ (-δ))).comp
      (cont_linF η η' ζ).measurable)
  have hw1 : Measurable w1 :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable (fun r : ℂ => (1 + ‖r‖) ^ (-δ / 4))).comp
      (cont_linF η η' ζ).measurable)
  have hf := meas_fS (p := p) (m := m) s
  have hN : (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) = ENNReal.ofReal (‖η' 0‖ ^ (-γ)) := by
    have e0 : ENNReal.ofReal ‖η' 0‖ = (‖η' 0‖₊ : ℝ≥0∞) := by
      rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [← e0, ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hη)]
  have stepA : OSInt p m s δ η η' ζ c₀ ≤
      ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * ∫⁻ x, fS s x * w1 x := by
    have hA := avg (μ := volume) rot rot_meas (fun t _ => rot_mp t) hf hw0 1
      (fun t _ x => by rw [one_mul, fS_rot])
    calc OSInt p m s δ η η' ζ c₀ = ∫⁻ x, fS s x * w0 x := rfl
      _ ≤ 1 * ∫⁻ x, fS s x * (∫⁻ t in Icc (1 : ℝ) 2, w0 (rot t x)) := hA
      _ ≤ ∫⁻ x, fS s x * ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖linF η η' ζ x‖) ^ (-δ / 4)) := by
          rw [one_mul]
          refine lintegral_mono (fun x => ?_)
          gcongr
          simp only [hw0d, linF_rot]
          exact hrot _ _
      _ = ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * ∫⁻ x, fS s x * w1 x := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr (fun x => ?_)
          rw [hw1d, ENNReal.ofReal_mul (mul_nonneg hCr0.le (by positivity))]
          ring
  have stepB : ∫⁻ x, fS s x * w1 x ≤
      ENNReal.ofReal Ks * (ENNReal.ofReal C2 * ENNReal.ofReal (‖η' 0‖ ^ (-γ)) *
        ∫⁻ x : Xp (p + 1) m, fS s x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ)) := by
    have hB := avg (μ := volume) scl scl_meas (fun τ hτ => scl_mp τ (by linarith [hτ.1])) hf hw1
      (ENNReal.ofReal Ks) (fun τ hτ x => fS_scl s hs0 τ hτ x)
    refine hB.trans ?_
    gcongr
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_mono (fun x => ?_)
    calc fS s x * (∫⁻ τ in Icc (1 : ℝ) 2, w1 (scl τ x))
        ≤ fS s x * (ENNReal.ofReal C2 * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ)) := by
          gcongr
          exact hscl η η' ζ x
      _ = _ := by rw [hN]; ring
  have hC3' : ∫⁻ x : Xp (p + 1) m, fS s x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤ ENNReal.ofReal (max C3 0) :=
    hC3.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc OSInt p m s δ η η' ζ c₀
      ≤ ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * (ENNReal.ofReal Ks * (ENNReal.ofReal C2 *
          ENNReal.ofReal (‖η' 0‖ ^ (-γ)) * ENNReal.ofReal (max C3 0))) := by
        refine stepA.trans ?_
        gcongr
        exact stepB.trans (by gcongr)
    _ = ENNReal.ofReal (Cr * Ks * C2 * max C3 0 * ‖η' 0‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
        have h1 : 0 ≤ (1 + |c₀|) ^ (-δ / 4) := by positivity
        have h2 : 0 ≤ ‖η' 0‖ ^ (-γ) := by positivity
        have h3 : 0 ≤ max C3 0 := le_max_right _ _
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le) h3) h2),
          ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le) h3),
          ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le),
          ENNReal.ofReal_mul (mul_nonneg hCr0.le hKs0), ENNReal.ofReal_mul hCr0.le,
          ENNReal.ofReal_mul hCr0.le]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TLeftH

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B HermitianLiftIdentities

theorem tLeftH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TLeft := by
  intro k r s μG Φ hk hμ _ hK x hx
  obtain ⟨κ, hκ, hF⟩ := fsE_left hIW hk hx
  have h1 : ∀ g : Mt k r, κ⁻¹ * Matrix.of (lmulM κ g) = Matrix.of g := fun g => by
    show κ⁻¹ * (κ * Matrix.of g) = Matrix.of g
    rw [← Matrix.mul_assoc, uh_inv_mul hκ.1, Matrix.one_mul]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s x) * (Φ g * FsE k r s (κ⁻¹ * Matrix.of g)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (κ⁻¹ * Matrix.of g) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        rw [← lmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (κ⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [hK κ hκ g, h1]

theorem tBothH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TBoth := by
  intro k r s μG Φ hk hμ hΦ hK x hx y hy
  obtain ⟨κ, hκ, hF⟩ := fsE_right hIW hk hy
  have hL := tLeftH hIW hB2 k r s μG Φ hk hμ hΦ (fun κ hκ g => (hK κ hκ g).1) x hx
  have h1 : ∀ g : Mt k r, x⁻¹ * Matrix.of (rmulF κ g) = x⁻¹ * Matrix.of g * κ := fun g => by
    show x⁻¹ * (Matrix.of g * κ) = x⁻¹ * Matrix.of g * κ
    rw [Matrix.mul_assoc]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s y) * (Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG := by
        rw [← rmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (x⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [(hK κ hκ g).2, h1]
    _ = _ := by
        rw [hL, ENNReal.ofReal_mul (fsR_nonneg hk hx s)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailFinOf

section

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

namespace J2

lemma sum_Iic {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Iic l, g j = ∑ j, if j ≤ l then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma sum_Ioi {n : ℕ} (g : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∑ j ∈ Finset.Ioi l, g j = ∑ j, if l < j then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma iic_zero {n : ℕ} (g : Fin (n + 1) → ℝ) : ∑ j ∈ Finset.Iic 0, g j = g 0 := by
  rw [sum_Iic]
  simp [Fin.le_zero_iff]

lemma upd_eq {p : ℕ} (ν : Fin (p + 2) → ℝ) :
    Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0) = fun j => ν j.succ + if j = 0 then ν 0 else 0 := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Fin.tail, add_comm]
  · simp [Fin.tail]

lemma iic_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Iic l.succ, ν j = ν 0 + ∑ j ∈ Finset.Iic l, ν j.succ := by
  rw [sum_Iic, sum_Iic (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_le_succ_iff]

lemma ioi_succ {p : ℕ} (ν : Fin (p + 2) → ℝ) (l : Fin (p + 1)) :
    ∑ j ∈ Finset.Ioi l.succ, ν j = ∑ j ∈ Finset.Ioi l, ν j.succ := by
  rw [sum_Ioi, sum_Ioi (fun j => ν j.succ), Fin.sum_univ_succ (n := p + 1)]
  simp [Fin.succ_lt_succ_iff]

lemma cond_step {p : ℕ} (ν : Fin (p + 2) → ℝ) (h : CHCond (p + 1) ν) :
    0 < ν 0 ∧ 0 < ν 0 + 2 * ∑ i, Fin.tail ν i ∧
      CHCond p (Function.update (Fin.tail ν) 0 (ν 0 + Fin.tail ν 0)) := by
  obtain ⟨h1, h2⟩ := h
  have hI : ∑ j ∈ Finset.Ioi (0 : Fin (p + 2)), ν j = ∑ i, Fin.tail ν i := by
    rw [sum_Ioi, Fin.sum_univ_succ (n := p + 1)]
    simp [Fin.tail, Fin.succ_pos]
  have e0 := h1 0
  rw [iic_zero] at e0
  refine ⟨e0, ?_, ?_⟩
  · have := h2 0 (by simp)
    rw [iic_zero, hI] at this
    exact this
  · rw [upd_eq]
    have hA : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Iic l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_Iic.2 (Fin.zero_le l)),
        iic_succ]
      ring
    have hB : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Ioi l, (ν j.succ + if j = 0 then ν 0 else 0) =
        ∑ j ∈ Finset.Ioi l.succ, ν j := by
      intro l
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_neg (by simp), ioi_succ, add_zero]
    refine ⟨fun l => ?_, fun l hl => ?_⟩
    · beta_reduce
      rw [hA]
      exact h1 l.succ
    · beta_reduce
      rw [hA, hB]
      exact h2 l.succ (by rw [Fin.val_succ]; omega)

end J2

theorem c1 : C1 := by
  intro p m x
  rw [J2.de_sq, J2.de_sq, J2.lsq_zero, J2.rhoSq_zero, J2.bco_zero, J2.lsq_one]
  have hL : (0 : ℝ) < 1 + ((x.1 0).re * (x.1 0).re + (x.1 0).im * (x.1 0).im) := by
    nlinarith [mul_self_nonneg (x.1 0).re, mul_self_nonneg (x.1 0).im]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  field_simp
  ring

theorem tailFin_of (hCH : CH) : TailFin := by
  intro p m α ν hc hpos
  rw [J2.tail_eq]
  exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (hCH p m _ hc)

theorem ch_of (hC1 : C1) : CH := by
  intro p
  induction p with
  | zero =>
    intro m ν hν
    exact J2.ch_base m ν (by have := hν.1 0; rwa [J2.iic_zero] at this)
  | succ p ih =>
    intro m ν hν
    obtain ⟨h0, hs, hc⟩ := J2.cond_step ν hν
    rw [J2.ch_step, J2.tail_eq]
    exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith))
      (ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (ih m _ hc))

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExists2

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem xiExists_of_in (h : InductiveHeisenbergInputs) : Formalism.FourierDecayAlt.B.XiExists :=
  xiExists_of_induction_steps (aStepBase_of h (tBothH iwB h))
    (aStepSucc_of h iwB (tLeftH iwB h) FormulaFAux.formulaF_all (ch_of c1))
    (bStepBase_of h)
    (bStepSucc_of h iwB FormulaFAux.formulaF_all
      (oscillatoryBound' (tailFin_of (ch_of c1)) c1 quadraticSublevelDecay' ker slow))
    (coefStep_of h (tBothH iwB h) (det_of h)) (xiIntH h)

theorem xiExists : Formalism.FourierDecayAlt.B.XiExists := xiExists_of_in heisenbergHaarFacts_hold

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
