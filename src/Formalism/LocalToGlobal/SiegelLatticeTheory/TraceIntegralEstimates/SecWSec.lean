module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWLoc

section

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ}

def sfv (sc : ℝ) (b : Fin r) : ℂ := ((sc : ℂ) ^ (r - b.1))⁻¹

def lamv (sc : ℝ) (c : Fin (r + 1) → ℂ) (b : Fin r) : ℂ := c (Fin.castSucc b) / (sfv sc b * sfv sc b)

def alv (T : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := -c (Fin.last r) / (T : ℂ)

def bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := ((Real.sqrt (‖c (Fin.last r)‖ ^ 2 / T - T') : ℝ) : ℂ)

def svv (T T' : ℝ) : ℂ := (((Real.sqrt (T * T'))⁻¹ : ℝ) : ℂ)

def e2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (f : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => lamv sc c b • f b

def p2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (e : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => (conj (lamv sc c b))⁻¹ • e b

def z2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) : Fin n → ℂ :=
  alv T c • z + bev T T' c • w i0

def w2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) :
    Fin k → Fin n → ℂ :=
  fun j => if j = i0 then svv T T' • (bev T T' c • z + (conj (alv T c) * (T : ℂ)) • w i0) else w j

section Facts

variable {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem conj_sfv (sc : ℝ) (b : Fin r) : conj (sfv sc b) = sfv sc b := by
  simp only [sfv, map_inv₀, map_pow, Complex.conj_ofReal]

theorem sfv_ne (hsc : 0 < sc) (b : Fin r) : sfv sc b ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hsc.ne'))

theorem lamv_ne (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0) (b : Fin r) : lamv sc c b ≠ 0 :=
  div_ne_zero (hc _) (mul_ne_zero (sfv_ne hsc b) (sfv_ne hsc b))

theorem conj_bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : conj (bev T T' c) = bev T T' c := Complex.conj_ofReal _

theorem bev_sq (hT : 0 < T) (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    conj (bev T T' c) * bev T T' c = ((‖c (Fin.last r)‖ ^ 2 / T - T' : ℝ) : ℂ) := by
  have hq0 : 0 ≤ ‖c (Fin.last r)‖ ^ 2 / T - T' := by
    rw [div_sub' hT.ne']
    exact div_nonneg (by nlinarith) hT.le
  rw [conj_bev, bev, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]

theorem alv_sq (T : ℝ) (c : Fin (r + 1) → ℂ) :
    conj (alv T c) * alv T c = ((‖c (Fin.last r)‖ ^ 2 / T ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, alv, map_div₀, map_neg, Complex.conj_ofReal, neg_div, neg_div, neg_mul_neg, div_mul_div_comm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem svv_sq (hT : 0 < T) (hT' : 0 < T') : conj (svv T T') * svv T T' = ((1 / (T * T') : ℝ) : ℂ) := by
  rw [svv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity), one_div]

end Facts

section Frame

variable {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem frm2 (F0 : Frm ε e f z w T) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') (i0 : Fin k) :
    Frm ε (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T' := by
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_swapδ F0.ep b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hwz : ∀ j, hJ ε (w j) z = 0 := fun j => hJ_swap0 (F0.zw j)
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hlam := lamv_ne hsc hc
  have hcb := conj_bev T T' c
  have hβ := bev_sq (T' := T') hT hg
  rw [hcb] at hβ
  have hα := alv_sq T c
  have hs := svv_sq hT hT'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT'.ne'⟩
  · intro a b
    simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.pp, mul_zero]
  · intro a b
    simp only [e2, p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe]
    split_ifs with h
    · subst h
      rw [mul_one, inv_mul_cancel₀ ((map_ne_zero _).2 (hlam a))]
    · simp
  · intro a b
    simp only [p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.ee, mul_zero]
  · intro a
    simp only [e2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.pz, F0.pw, mul_zero,
      add_zero]
  · intro a
    simp only [p2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
      add_zero]
  · simp only [z2, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.zz,
      F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
    linear_combination (norm := skip) (-(T : ℂ)) * hα + hβ
    push_cast
    field_simp
    ring
  · intro a j
    by_cases hj : j = i0
    · simp only [e2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.pz, F0.pw,
        mul_zero, add_zero]
    · simp only [e2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.pw, mul_zero]
  · intro a j
    by_cases hj : j = i0
    · simp only [p2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.ez, F0.ew,
        mul_zero, add_zero]
    · simp only [p2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.ew, mul_zero]
  · intro j
    by_cases hj : j = i0
    · simp only [z2, w2, if_pos hj, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right,
        UnitaryIsometries.hJ_smul_left, F0.zz, F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
      ring
    · have hne : i0 ≠ j := fun h => hj h.symm
      simp only [z2, w2, if_neg hj, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_smul_left, F0.zw, F0.ww, if_neg hne, mul_zero,
        add_zero]
  · intro i j
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · subst hi; subst hj
      simp only [w2, if_true, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left,
        F0.zz, F0.zw, hwz, F0.ww, mul_zero, add_zero, zero_add, mul_one, hcb, map_mul, Complex.conj_conj,
        Complex.conj_ofReal]
      linear_combination (norm := skip) ((T : ℂ) ^ 2 * (conj (alv T c) * alv T c) - (T : ℂ) * (bev T T' c * bev T T' c)) * hs +
        (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ) ^ 2) * hα - (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ)) * hβ
      push_cast
      field_simp
      ring
    · subst hi
      have hne : i ≠ j := fun h => hj h.symm
      simp only [w2, if_true, if_neg hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_left, F0.zw, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · subst hj
      have hne : i ≠ j := hi
      simp only [w2, if_true, if_neg hi, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, hwz, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · simp only [w2, if_neg hi, if_neg hj]
      exact F0.ww i j

end Frame

end Formalism.L2.S.Pv.SecW
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWFrame

section

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} (ε : Fin n → Bool)

def fr2L (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def fr2M (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (fr2L ε e p z w e' p' z' w' T)

variable {ε} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {e' p' : Fin r → Fin n → ℂ} {z' : Fin n → ℂ} {w' : Fin k → Fin n → ℂ} {T : ℝ}

theorem frameChangeMatrix_mulVec (v : Fin n → ℂ) :
    fr2M ε e p z w e' p' z' w' T *ᵥ v =
      syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  unfold fr2M
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem frameChangeMatrix_entry (i j : Fin n) :
    fr2M ε e p z w e' p' z' w' T i j =
      syn e' p' z' w' T (fun a => hJ ε (p a) (Pi.single j 1)) (fun a => hJ ε (e a) (Pi.single j 1))
        (hJ ε z (Pi.single j 1)) (fun l => hJ ε (w l) (Pi.single j 1)) i := by
  have h : fr2M ε e p z w e' p' z' w' T *ᵥ Pi.single j 1 = _ := frameChangeMatrix_mulVec _
  rw [Matrix.mulVec_single_one] at h
  exact congrFun h i

theorem frameChangeMatrix_isometry (F : Frm ε e p z w T) (F' : Frm ε e' p' z' w' T) (hdim : n = 2 * r + 1 + k) :
    UnitaryIsometries.IsIsom ε (fr2M ε e p z w e' p' z' w' T) := by
  intro x y
  rw [frameChangeMatrix_mulVec, frameChangeMatrix_mulVec, hJ_syn_syn F']
  conv_rhs => rw [recon F hdim x, recon F hdim y, hJ_syn_syn F]

theorem frameChangeMatrix_isotropic (F : Frm ε e p z w T) (b : Fin r) : fr2M ε e p z w e' p' z' w' T *ᵥ e b = e' b := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) (e b)) = fun a => if a = b then (1 : ℂ) else 0 := by
    funext a
    rw [UnitaryIsometries.hJ_conj, F.ep b a]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  have h2 : (fun a => hJ ε (e a) (e b)) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ee a b
  have h3 : hJ ε z (e b) = 0 := by rw [UnitaryIsometries.hJ_conj, F.ez b, map_zero]
  have h4 : (fun j => hJ ε (w j) (e b)) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.ew b j, map_zero]
  rw [h1, h2, h3, h4]
  simp [syn]

theorem fr2M_mulVec_z (F : Frm ε e p z w T) : fr2M ε e p z w e' p' z' w' T *ᵥ z = z' := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.pz a
  have h2 : (fun a => hJ ε (e a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ez a
  have h4 : (fun j => hJ ε (w j) z) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.zw j, map_zero]
  rw [h1, h2, F.zz, h4]
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast F.T_ne
  simp [syn, hT]

end Formalism.L2.S.Pv.SecW
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWSec

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
  {w w' : Fin k → Fin n → ℂ} {sc T T' : ℝ}

def Mv (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (w w' : Fin k → Fin n → ℂ)
    (sc T T' : ℝ) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fr2M ε e f z' w' (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T'

theorem famSc_castSucc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (b : Fin r) :
    famSc sc e z (Fin.castSucc b) = sfv sc b • e b := by
  simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc, sfv]

theorem famSc_last (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc sc e z (Fin.last r) = z := by
  simp only [famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem zhat_Mv (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hsc : 0 < sc) {c : Fin (r + 1) → ℂ} (i0 : Fin k) :
    Zhat ε (famSc sc e z) (famSc sc e z') (Mv ε e f z z' w w' sc T T' i0 c) = Matrix.diagonal c := by
  have hMe : ∀ b, Mv ε e f z z' w w' sc T T' i0 c *ᵥ e b = e2 sc c f b := fun b => frameChangeMatrix_isotropic F1 b
  have hMz : Mv ε e f z z' w w' sc T T' i0 c *ᵥ z' = z2 T T' c z w i0 := fr2M_mulVec_z F1
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F0.T_ne
  have hfe : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0 := F0.ep
  ext a b
  simp only [Zhat]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_last, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.zz, F0.zw, mul_zero, add_zero, diagonal_apply_eq,
        alv]
      field_simp
    | cast b =>
      rw [famSc_last, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_right, hJ_swap0 (F0.pz b), mul_zero]
      rw [diagonal_apply_ne]
      exact fun h => (Fin.castSucc_lt_last b).ne h.symm
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_castSucc, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
        add_zero]
      rw [diagonal_apply_ne]
      exact (Fin.castSucc_lt_last a).ne
    | cast b =>
      rw [famSc_castSucc, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe, conj_sfv]
      by_cases h : a = b
      · subst h
        rw [diagonal_apply_eq, if_pos rfl, lamv]
        have hs : sfv sc a ≠ 0 := sfv_ne hsc a
        field_simp
      · rw [if_neg h, diagonal_apply_ne _ (fun h' => h (Fin.castSucc_injective _ h'))]
        ring

theorem measurable_Mv (i0 : Fin k) :
    Measurable (fun c : Fin (r + 1) → ℂ => Mv ε e f z z' w w' sc T T' i0 c) := by
  have hlam : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => lamv sc c a) := fun a =>
    (measurable_pi_apply _).div_const _
  have hinv : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => (conj (lamv sc c a))⁻¹) := fun a =>
    (Complex.continuous_conj.measurable.comp (hlam a)).inv
  have hal : Measurable (fun c : Fin (r + 1) → ℂ => alv T c) := (measurable_pi_apply _).neg.div_const _
  have hbe : Measurable (fun c : Fin (r + 1) → ℂ => bev T T' c) := by
    unfold bev
    exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      ((((measurable_pi_apply _).norm.pow_const 2).div_const _).sub_const _))
  have hcal : Measurable (fun c : Fin (r + 1) → ℂ => conj (alv T c)) := Complex.continuous_conj.measurable.comp hal
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Mv, frameChangeMatrix_entry, syn, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ((Finset.measurable_sum _ fun a _ => ?_).add (Finset.measurable_sum _ fun a _ => ?_)).add ?_ |>.add
    (Finset.measurable_sum _ fun l _ => ?_)
  · simp only [e2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hlam a).mul measurable_const)
  · simp only [p2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hinv a).mul measurable_const)
  · simp only [z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hal.mul measurable_const).add (hbe.mul measurable_const))
  · simp only [w2]
    by_cases hl : l = i0
    · simp only [if_pos hl, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact measurable_const.mul (measurable_const.mul ((hbe.mul measurable_const).add
        ((hcal.mul measurable_const).mul measurable_const)))
    · simp only [if_neg hl]
      exact measurable_const

instance matrix_borel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

theorem measurableEmbedding_uMat (ε : Fin n → Bool) :
    MeasurableEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding

def secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T) (hT' : 0 < T')
    (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Formalism.REAL.UJ ε :=
  if h : (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then
    UnitaryIsometries.toUJ ε (frameChangeMatrix_isometry F1 (frm2 (sc := sc) F0 hT hT' hsc h.1 h.2 i0) hdim)
  else 1

theorem uMat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) :
    Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c) =
      if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c else 1 := by
  unfold secV
  split_ifs with h
  · rfl
  · simp [Formalism.MainNotions.S.uMat]

theorem measurable_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k)
    (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) :
    Measurable (secV F0 F1 hdim hT hT' hsc i0) := by
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have he : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) ∘ secV F0 F1 hdim hT hT' hsc i0 =
      fun c => if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c
        else 1 := by
    funext c
    exact uMat_secV F0 F1 hdim hT hT' hsc i0 c
  rw [he]
  have hm1 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton 0).compl.preimage (measurable_pi_apply l)
  have hm2 : MeasurableSet {c : Fin (r + 1) → ℂ | 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    measurableSet_lt measurable_const ((((measurable_pi_apply _).norm.pow_const 2)).sub_const _)
  have hm : MeasurableSet {c : Fin (r + 1) → ℂ | (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    hm1.inter hm2
  exact Measurable.ite hm (measurable_Mv i0) measurable_const

theorem zhat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) {c : Fin (r + 1) → ℂ} (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c)) =
      Matrix.diagonal c := by
  rw [uMat_secV, if_pos ⟨hc, hg⟩]
  exact zhat_Mv F0 F1 hsc i0

end Formalism.L2.S.Pv.SecW
end
end
end
