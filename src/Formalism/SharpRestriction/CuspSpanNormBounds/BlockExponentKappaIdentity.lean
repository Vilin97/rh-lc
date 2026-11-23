module

public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.RatioInvLeFrameFactor

section

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Pts

variable {k r : ℕ} {κ τ : ℝ}

theorem scaleBlocks_map_snd (κ τ : ℝ) (r acc : ℕ) (bs : List (ℂ × ℕ)) :
    (scaleBlocks κ τ r acc bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, List.map_cons, ih]

theorem scaleBlocks_blocks (hκ : 0 < κ) (hτ : 0 < τ) (acc : ℕ) (bs : List (ℂ × ℕ))
    (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) : ∀ b ∈ scaleBlocks κ τ r acc bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := by
  induction bs generalizing acc with
  | nil => intro b hb; simp [scaleBlocks] at hb
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro x hx
    simp only [scaleBlocks, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have h0 := h (t, s) (by simp)
      refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) h0.1, h0.2⟩
    · exact ih (acc + s) (fun b hb => h b (by simp [hb])) x hx

def ptTr (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) : Point ℂ (r + 1) :=
  ⟨scaleBlocks κ τ r 0 γ.1, scaleBlocks_blocks hκ hτ 0 γ.1 γ.2.1, by rw [scaleBlocks_map_snd]; exact γ.2.2⟩

theorem ptTr_val (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    (ptTr κ τ hκ hτ γ).1 = scaleBlocks κ τ r 0 γ.1 := rfl

theorem ptEntry_scaleBlocks (acc : ℕ) (bs : List (ℂ × ℕ)) (i j : ℕ)
    (h : acc + (bs.map Prod.snd).sum ≤ r + 1) :
    ptEntry (scaleBlocks κ τ r acc bs) i j =
      ((tF r κ τ (acc + i) * tF r κ τ (acc + j) : ℝ) : ℂ) * ptEntry bs i j := by
  induction bs generalizing acc i j with
  | nil => simp [scaleBlocks, ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    simp only [scaleBlocks, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        have e : 2 * (r + 1 - (acc + s)) + (s - 1) = (r - (acc + i)) + (r - (acc + j)) := by omega
        rw [e, tF, tF, pow_add]; push_cast; ring
      · rw [if_neg h2, if_neg h2, mul_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih (acc + s) (i - s) (j - s) (by omega),
          show acc + s + (i - s) = acc + i by omega, show acc + s + (j - s) = acc + j by omega]
      · rw [if_neg h3, if_neg h3, mul_zero]

theorem ptMat_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) (a b : Fin (r + 1)) :
    ptMat (ptTr κ τ hκ hτ γ) a b = ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) * ptMat γ a b := by
  have := ptEntry_scaleBlocks (κ := κ) (τ := τ) (r := r) 0 γ.1 a.val b.val (by rw [γ.2.2]; omega)
  rw [zero_add, zero_add] at this
  exact this

theorem prod_filter_lt (f : ℕ → ℝ) (l : ℕ) (hl : l ≤ r + 1) :
    ∏ a : Fin (r + 1) with a.val < l, f a = ∏ a ∈ range l, f a := by
  rw [Finset.prod_filter, Fin.prod_univ_eq_prod_range (fun a => if a < l then f a else 1), ← Finset.prod_filter]
  congr 1
  ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem prod_range_tF_sq (l : ℕ) :
    ∏ a ∈ range l, tF r κ τ a ^ 2 = τ ^ (2 * l) * κ ^ (∑ a ∈ range l, (r - a) * 2) := by
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum, ← pow_mul]

theorem sum_range_sub_mul_two (r : ℕ) : ∑ a ∈ range (r + 1), (r - a) * 2 = r * (r + 1) := by
  have h1 : ∑ a ∈ range (r + 1), (r - a) = ∑ a ∈ range (r + 1), a := by
    rw [← Finset.sum_range_reflect (fun a => a) (r + 1)]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Nat.add_sub_cancel]
  have h2 := Finset.sum_range_id_mul_two (r + 1)
  rw [← Finset.sum_mul, h1, h2, Nat.add_sub_cancel, mul_comm]

theorem sum_range_sub_mul_two' (r : ℕ) : ∑ a ∈ range r, (r - a) * 2 = r * (r + 1) := by
  have := sum_range_sub_mul_two r
  rw [Finset.sum_range_succ, Nat.sub_self, zero_mul, add_zero] at this
  exact this

theorem leadMinor_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) (l : ℕ) (hl : l ≤ r + 1) :
    leadMinor (ptMat (ptTr κ τ hκ hτ γ)) l hl =
      ((∏ a : Fin (r + 1) with a.val < l, tF r κ τ a ^ 2 : ℝ) : ℂ) * leadMinor (ptMat γ) l hl := by
  unfold leadMinor
  set d : Fin l → ℂ := fun i => ((tF r κ τ i.val : ℝ) : ℂ) with hd
  have hM : (ptMat (ptTr κ τ hκ hτ γ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal d * (ptMat γ).submatrix (Fin.castLE hl) (Fin.castLE hl) * Matrix.diagonal d := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.submatrix_apply, ptMat_ptTr]
    simp only [hd, Fin.val_castLE]; push_cast; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_filter_lt (fun a => tF r κ τ a ^ 2) l hl,
    ← Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ 2) l]
  push_cast
  rw [Finset.prod_pow]; ring

theorem GPoint_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    Gpt (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) = κ ^ (2 * r * (r + 1)) * τ ^ (4 * (r + 1)) * Gpt T T' γ := by
  unfold Gpt
  rw [leadMinor_ptTr, leadMinor_ptTr, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal, prod_filter_lt (fun a => tF r κ τ a ^ 2) _ le_rfl,
    prod_filter_lt (fun a => tF r κ τ a ^ 2) _ (Nat.le_succ r), prod_range_tF_sq, prod_range_tF_sq,
    sum_range_sub_mul_two, sum_range_sub_mul_two']
  ring

theorem blockIdx_scaleBlocks (acc : ℕ) (bs : List (ℂ × ℕ)) (p : ℕ) :
    blockIdx (scaleBlocks κ τ r acc bs) p = blockIdx bs p := by
  induction bs generalizing acc p with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, blockIdx, ih]

theorem rootPat_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    rootPat (ptTr κ τ hκ hτ γ) = rootPat γ := by
  simp only [rootPat, ptTr_val, blockIdx_scaleBlocks]

def frStart : List (ℂ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, p => if p < s then 0 else s + frStart bs (p - s)

theorem frStart_le : ∀ (bs : List (ℂ × ℕ)) (p : ℕ), frStart bs p ≤ p
  | [], p => Nat.zero_le p
  | (t, s) :: bs, p => by
    simp only [frStart]
    split_ifs with h
    · exact Nat.zero_le p
    · have := frStart_le bs (p - s); omega

theorem blockIdx_eq_iff : ∀ (bs : List (ℂ × ℕ)) (a b : ℕ), a < b →
    (blockIdx bs a = blockIdx bs b ↔ frStart bs b ≤ a)
  | [], a, b, _ => by simp [blockIdx, frStart]
  | (t, s) :: bs, a, b, hab => by
    simp only [blockIdx, frStart]
    by_cases hb : b < s
    · have ha : a < s := by omega
      rw [if_pos ha, if_pos hb, if_pos hb]; simp
    · by_cases ha : a < s
      · rw [if_pos ha, if_neg hb, if_neg hb]; constructor <;> intro h <;> omega
      · rw [if_neg ha, if_neg hb, if_neg hb]
        have := blockIdx_eq_iff bs (a - s) (b - s) (by omega)
        constructor
        · intro h; have := this.mp (by omega); omega
        · intro h; have := this.mpr (by omega); omega

theorem sum_rootPat (g : ℕ → ℕ → ℕ) (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, g p.1.val p.2.val = ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, g a b := by
  have key : ∀ b : Fin (r + 1), (∑ a : Fin (r + 1),
      if a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val then g a.val b.val else 0) =
      ∑ a ∈ Ico (frStart γ.1 b) b, g a b := by
    intro b
    have hsub : Ico (frStart γ.1 b) b.val ⊆ range (r + 1) := fun x hx => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    rw [← Finset.inter_eq_right.mpr hsub, ← Finset.sum_ite_mem,
      Finset.sum_range (fun a => if a ∈ Ico (frStart γ.1 b) b.val then g a b else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hiff : (a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val) ↔ a.val ∈ Ico (frStart γ.1 b) b.val := by
      rw [Finset.mem_Ico, Fin.lt_def]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(blockIdx_eq_iff γ.1 a b h1).mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, (blockIdx_eq_iff γ.1 a b h2).mpr h1⟩
    by_cases h : a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  rw [rootPat, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product_right,
    Finset.sum_range (fun b => ∑ a ∈ Ico (frStart γ.1 b) b, g a b)]
  exact Finset.sum_congr rfl fun b _ => key b

theorem card_rootPat_le (γ : Point ℂ (r + 1)) : 2 * (rootPat γ).card ≤ r * (r + 1) := by
  have h1 : (rootPat γ).card = ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, 1 := by
    rw [Finset.card_eq_sum_ones]; exact sum_rootPat (fun _ _ => 1) γ
  have h2 : ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, (1 : ℕ) ≤ ∑ b ∈ range (r + 1), b :=
    Finset.sum_le_sum fun b _ => by
      rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]; exact Nat.sub_le _ _
  have h3 := Finset.sum_range_id_mul_two (r + 1)
  rw [Nat.add_sub_cancel] at h3
  rw [h1]
  calc 2 * ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, 1 ≤ 2 * ∑ b ∈ range (r + 1), b := by omega
    _ = r * (r + 1) := by rw [mul_comm, h3, mul_comm]

theorem one_le_max_inv {x : ℝ} (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total x 1 with h | h
  · exact le_max_of_le_right ((one_le_inv₀ hx).mpr h)
  · exact le_max_of_le_left h

theorem pow_le_maxRpow {x : ℝ} (hx : 0 < x) {n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y) :
    x ^ n ≤ max x x⁻¹ ^ y ∧ x⁻¹ ^ n ≤ max x x⁻¹ ^ y := by
  have h1 : max x x⁻¹ ^ n ≤ max x x⁻¹ ^ y := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (one_le_max_inv hx) hny
  exact ⟨(pow_le_pow_left₀ hx.le (le_max_left _ _) n).trans h1,
    (pow_le_pow_left₀ (inv_pos.mpr hx).le (le_max_right _ _) n).trans h1⟩

theorem frame_exps {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ} (hc : 2 * c ≤ r * (r + 1)) :
    ((4 * (r + 1) : ℕ) : ℝ) ≤ Cf * ((2 * r + 2 : ℕ) : ℝ) ∧
    ((2 * r * (r + 1) + 2 * c : ℕ) : ℝ) ≤ Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2 := by
  have hc' : ((2 * c : ℕ) : ℝ) ≤ ((r * (r + 1) : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at hc' ⊢
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · nlinarith
  · have h8 : (0 : ℝ) ≤ (2 * r + 2) ^ 2 := by positivity
    nlinarith

theorem ratio_inv_le_frameFactor (hκ : 0 < κ) (hτ : 0 < τ) {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ}
    (hc : 2 * c ≤ r * (r + 1)) :
    τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1) + 2 * c) ≤
      max κ κ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := by
  obtain ⟨e1, e2⟩ := frame_exps hCf hc
  rw [mul_comm (τ ^ _)]
  exact mul_le_mul (pow_le_maxRpow hκ e2).1 (pow_le_maxRpow hτ e1).1 (by positivity)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_max_inv hκ)) _)

theorem ratio_le_frameFactor (hκ : 0 < κ) (hτ : 0 < τ) {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ}
    (hc : 2 * c ≤ r * (r + 1)) :
    (τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1) + 2 * c))⁻¹ ≤
      max κ κ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := by
  obtain ⟨e1, e2⟩ := frame_exps hCf hc
  rw [mul_inv, ← inv_pow, ← inv_pow, mul_comm ((τ⁻¹) ^ _)]
  exact mul_le_mul (pow_le_maxRpow hκ e2).2 (pow_le_maxRpow hτ e1).2 (by positivity)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_max_inv hκ)) _)

end Pts

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BlockExponentKappaIdentity

section

@[expose] public section

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Weight

variable {k r : ℕ} {κ τ : ℝ}

def Wbig (k r : ℕ) (κ τ : ℝ) : ℝ := ∏ a : Fin (r + 1), tF r κ τ a ^ (4 * (2 * (r - a.val) + k - 1))

def frameBlockSum (g : ℕ → ℕ → ℕ) : ℕ → List (ℂ × ℕ) → ℕ
  | _, [] => 0
  | acc, (_, s) :: bs => g acc s + frameBlockSum g (acc + s) bs

def frGN (k r acc s : ℕ) : ℕ := 2 * s * (Ml k r (acc + s) + s - 3)

def frGE (r acc s : ℕ) : ℕ := 2 * (r + 1 - (acc + s)) + (s - 1)

def frTri (d : ℕ) : ℕ := ∑ j ∈ range d, (d - j)

theorem ptWeightFrom_scale (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ptWeightFrom k r (τ ^ 2 * T) (τ ^ 2 * T') acc (scaleBlocks κ τ r acc bs) =
      τ ^ frameBlockSum (fun a s => 2 * frGN k r a s) acc bs *
        κ ^ frameBlockSum (fun a s => frGE r a s * frGN k r a s) acc bs * ptWeightFrom k r T T' acc bs := by
  induction bs generalizing acc with
  | nil => simp [ptWeightFrom, scaleBlocks, frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, ptWeightFrom, frameBlockSum]
    rw [ih (acc + s)]
    by_cases h : s = 1 ∧ acc + 1 = r + 1
    · rw [if_pos h, if_pos h]
      obtain ⟨rfl, h2⟩ := h
      have e1 : 2 * (r + 1 - (acc + 1)) + (1 - 1) = 0 := by omega
      have e2 : frGE r acc 1 = 0 := by unfold frGE; omega
      have e3 : 2 * frGN k r acc 1 = 4 * (k - 1) := by unfold frGN Ml; omega
      have hbase : Complex.normSq (((τ ^ 2 * κ ^ 0 : ℝ) : ℂ) * t) - τ ^ 2 * T * (τ ^ 2 * T') =
          τ ^ 4 * (Complex.normSq t - T * T') := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
      rw [e1, hbase, e2, e3, mul_pow]
      ring
    · rw [if_neg h, if_neg h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      unfold frGE frGN
      ring

theorem sum_pos_blocks (f : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ∑ p ∈ range (bs.map Prod.snd).sum, f (acc + p) (p - frStart bs p) =
      frameBlockSum (fun a s => ∑ i ∈ range s, f (a + i) i) acc bs := by
  induction bs generalizing acc with
  | nil => simp [frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_range_add, frameBlockSum, ← ih (acc + s)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < s := Finset.mem_range.mp hp
      simp only [frStart, if_pos hp', Nat.sub_zero]
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [frStart]
      rw [if_neg (show ¬ (s + p < s) by omega), show s + p - s = p by omega,
        show acc + (s + p) = acc + s + p by omega,
        show s + p - (s + frStart bs p) = p - frStart bs p by omega]

theorem sum_rootPat_diff (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, (p.2.val - p.1.val) = frameBlockSum (fun a s => ∑ i ∈ range s, frTri i) 0 γ.1 := by
  have h1 := sum_rootPat (fun a b => b - a) γ
  have h2 := sum_pos_blocks (fun _ d => frTri d) 0 γ.1
  rw [γ.2.2] at h2
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  unfold frTri
  refine Finset.sum_congr rfl fun j hj => ?_
  exact (Nat.sub_sub b (frStart γ.1 b) j).symm

theorem Wbig_eq : Wbig k r κ τ = τ ^ (∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1)) *
    κ ^ (∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1))) := by
  unfold Wbig
  rw [Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ (4 * (2 * (r - a) + k - 1)))]
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem alphaPt_sq_mul (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    alphaPt κ τ γ ^ 2 * κ ^ (4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val)) = κ ^ (2 * (rootPat γ).card) := by
  have h1 : ∀ p ∈ rootPat γ,
      (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 * κ ^ (2 * (p.2.val - p.1.val)) = 1 := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
    have hlt' : p.1.val < p.2.val := hlt
    have hle : p.2.val ≤ r := Nat.lt_succ_iff.mp p.2.isLt
    have e : tF r κ τ p.1.val = tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val) := by
      unfold tF; rw [mul_assoc, ← pow_add]; congr 2; omega
    have h2 := tF_pos (r := r) hκ hτ p.2.val
    have h3 : 0 < κ ^ (p.2.val - p.1.val) := pow_pos hκ _
    have h4 : tF r κ τ p.2.val / (tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val)) * κ ^ (p.2.val - p.1.val) = 1 := by
      field_simp
    rw [e, pow_mul', ← mul_pow, h4, one_pow]
  set P := ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 with hP
  set S := ∑ p ∈ rootPat γ, (p.2.val - p.1.val) with hS
  have hPS : P * κ ^ (2 * S) = 1 := by
    rw [hS, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one h1
  unfold alphaPt
  rw [← hP, show (κ ^ (rootPat γ).card * P) ^ 2 * κ ^ (4 * S) =
    κ ^ (2 * (rootPat γ).card) * (P * κ ^ (2 * S)) ^ 2 by ring, hPS]
  ring

theorem frTri_succ (d : ℕ) : frTri (d + 1) = frTri d + (d + 1) := by
  unfold frTri
  rw [Finset.sum_range_succ']
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by omega

theorem two_mul_frTri (d : ℕ) : 2 * frTri d = d * (d + 1) := by
  induction d with
  | zero => simp [frTri]
  | succ n ih => rw [frTri_succ, mul_add, ih]; ring

theorem block_exponent_tau_identity (m k' s' : ℕ) :
    2 * (2 * (s' + 1) * (2 * m + k' + s')) = ∑ i ∈ range (s' + 1), 4 * (2 * (m + i) + k') := by
  induction s' with
  | zero => simp only [zero_add, add_zero, Finset.sum_range_one]; ring
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

theorem block_exponent_kappa_identity (m k' s' : ℕ) :
    (2 * m + s') * (2 * (s' + 1) * (2 * m + k' + s')) + 4 * ∑ i ∈ range (s' + 1), frTri i =
      ∑ i ∈ range (s' + 1), (m + i) * (4 * (2 * (m + i) + k')) := by
  induction s' with
  | zero =>
    simp only [zero_add, add_zero, Finset.sum_range_one, frTri, Finset.range_zero, Finset.sum_empty, mul_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ frTri (n + 1),
      Finset.sum_range_succ (fun i => (m + i) * (4 * (2 * (m + i) + k'))) (n + 1), ← ih]
    have h := two_mul_frTri (n + 1)
    nlinarith [h]

theorem blk_tau (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    2 * frGN k r a s = ∑ i ∈ range s, 4 * (2 * (r - (a + i)) + k - 1) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  rw [hN, block_exponent_tau_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => 4 * (2 * (r - (a + i)) + k - 1)) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  omega

theorem blk_kappa (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    frGE r a s * frGN k r a s + 4 * ∑ i ∈ range s, frTri i =
      ∑ i ∈ range s, (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1)) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  have hE : frGE r a (s' + 1) = 2 * m + s' := by unfold frGE; omega
  rw [hN, hE, block_exponent_kappa_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1))) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  have e1 : r - (a + (s' + 1 - 1 - i)) = m + i := by omega
  have e2 : 2 * (m + i) + k - 1 = 2 * (m + i) + (k - 1) := by omega
  rw [e1, e2]

theorem frame_block_sum_congr {g₁ g₂ : ℕ → ℕ → ℕ} {R : ℕ} (h : ∀ a s, a + s ≤ R → g₁ a s = g₂ a s) (acc : ℕ)
    (bs : List (ℂ × ℕ)) (hb : acc + (bs.map Prod.snd).sum ≤ R) : frameBlockSum g₁ acc bs = frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hb
    simp only [frameBlockSum]
    rw [h acc s (by omega), ih (acc + s) (by omega)]

theorem frame_block_sum_add (g₁ g₂ : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => g₁ a s + g₂ a s) acc bs = frameBlockSum g₁ acc bs + frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem frame_block_sum_mul (c : ℕ) (g : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => c * g a s) acc bs = c * frameBlockSum g acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem ptWeight_ptTr (hk : 1 ≤ k) (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) * κ ^ (2 * (rootPat γ).card) =
      Wbig k r κ τ * alphaPt κ τ γ ^ 2 * ptWeight k r T T' γ := by
  have hsum : 0 + (γ.1.map Prod.snd).sum ≤ r + 1 := by rw [γ.2.2]; omega
  have hU := sum_pos_blocks (fun p _ => 4 * (2 * (r - p) + k - 1)) 0 γ.1
  have hV := sum_pos_blocks (fun p _ => (r - p) * (4 * (2 * (r - p) + k - 1))) 0 γ.1
  rw [γ.2.2] at hU hV
  simp only [zero_add] at hU hV
  have hA : frameBlockSum (fun a s => 2 * frGN k r a s) 0 γ.1 = ∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1) := by
    rw [hU]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_tau hk a s h
  have hB : frameBlockSum (fun a s => frGE r a s * frGN k r a s) 0 γ.1 + 4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val) =
      ∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1)) := by
    rw [hV, sum_rootPat_diff, ← frame_block_sum_mul, ← frame_block_sum_add]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_kappa hk a s h
  have hα := alphaPt_sq_mul hκ hτ γ
  unfold ptWeight
  rw [ptTr_val, ptWeightFrom_scale hκ hτ, Wbig_eq, hA, ← hB, ← hα, pow_add]
  ring

end Weight

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end
end
