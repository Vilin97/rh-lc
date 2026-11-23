module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCNumDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCore
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DvrFractionFieldCharZeroPrime
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SegmentBlockOfMonomial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondCongr
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Std.Tactic.BVDecide.Normalize.BitVec
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.DensitySumsAndDomination

-- Source module: Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.BlockYZeroLeOfBound

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem nb_sum_mod_div {n : ℕ} (f : Fin n → ℕ) (P : ℕ) : ∑ c, f c = ∑ c, f c % P + P * ∑ c, f c / P := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => (Nat.mod_add_div _ _).symm

theorem nb_key {n : ℕ} (P a : ℕ) (f : Fin n → ℕ) (B : ℕ) (h : P * a + ∑ c, f c = B) :
    B = P * (a + ∑ c, f c / P) + ∑ c, f c % P := by
  rw [← h, nb_sum_mod_div f P]
  ring

theorem nb_q_le (Q P r a : ℕ) (hr : r < P) (h : Q * P ≤ a) : Q ≤ a - r := by
  rcases Q with _ | q
  · exact Nat.zero_le _
  · have hP : 1 ≤ P := by omega
    have hq : q ≤ q * P := Nat.le_mul_of_pos_right q hP
    have : (q + 1) * P = q * P + P := by ring
    omega

theorem nb_div_le (a P n : ℕ) (hP : 0 < P) (h : a < (n + 1) * P) : a / P ≤ n :=
  Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hP).2 h)

section NB

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
  (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)

theorem nb_Ppos (hp : 0 < X.p) (i : Fin (segS X.TT j)) : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
  unfold SegData.P
  exact pow_pos hp _

theorem nb_coarseA (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + z0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
  show ((X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold z0A ezA
  ring

theorem nb_coarseC (hp : 0 < X.p)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) (i : Fin (segS X.TT j)) :
    coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i) + y0A C0 CE1 CE2 X j A i + ∑ c, eyA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
  show (segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold y0A eyA
  ring

theorem nb_digits (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) :
    DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) := by
  refine ⟨fun i c => ⟨Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i), Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i)⟩,
    fun i => ?_, fun i => ?_⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
    show ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ (X.seg C0 CE1 CE2 j).bTop i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        (X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
    show ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ segATop X.TT X.aT j i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩

theorem nb_oEff (i : Fin (segS X.TT j)) :
    oEff (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  simp only [oEff, segmentBlockOfMonomial]
  split_ifs with h
  · have h0 : jE (X.seg C0 CE1 CE2 j) ju i.val = 0 := by
      unfold jE
      rw [dite_eq_right (by omega)]
    rw [h0]
    ring
  · rfl

theorem nb_ord :
    blockOrd X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) = nuSeg C0 CE1 CE2 X j ju jp du A := by
  unfold blockOrd nuSeg
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nb_oEff, Fin.sum_univ_succ]
  have e1 := nb_sum_mod_div (fun c : Fin X.m => A ((topOdd X j i, true), c.succ)) ((X.seg C0 CE1 CE2 j).P X.p i)
  have e2 := Nat.mod_add_div (A ((topOdd X j i, false), 0)) ((X.seg C0 CE1 CE2 j).P X.p i)
  simp only [Fin.succ_ne_zero, if_false, if_true, segmentBlockOfMonomial, y0A, ezA] at e1 e2 ⊢
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_ne_zero, if_true, if_false, zero_add]
  linarith

theorem nb_ez_le (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (i : Fin (segS X.TT j))
    (h : ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - b.rz i c.succ) ≤ Qe) :
    ∑ c, ezA C0 CE1 CE2 X j A i c ≤ Qe := by
  obtain ⟨hlt, -, -⟩ := hd
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) h
  exact nb_q_le _ _ _ _ (hlt i c.succ).1 (Nat.div_mul_le_self _ _)

theorem block_y_zero_le_of_bound (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (t : ℕ)
    (h : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i * t + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ t + Qe := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  apply nb_div_le _ _ _ hP
  have : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  nlinarith

theorem block_y_zero_le_z_zero (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (D : ℕ)
    (hD : 1 + 2 * Qe ≤ D)
    (h1 : b.rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i * D ≤ A ((topOdd X j i, true), 0) + Qe)
    (h2 : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  have hq : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  have a1 : y0A C0 CE1 CE2 X j A i ≤ Qe := by
    apply nb_div_le _ _ _ hP
    nlinarith
  have a2 : Qe ≤ z0A C0 CE1 CE2 X j A i := by
    unfold z0A
    rw [Nat.le_div_iff_mul_le hP]
    nlinarith
  omega

theorem nb_coarseA_ge (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) b i ≤
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i + (X.m + 1) := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  set P := (X.seg C0 CE1 CE2 j).P X.p i with hPdef
  set B := (X.seg C0 CE1 CE2 j).bTop i
  have hy : ∑ c : Fin (X.m + 1), (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c ≤ (X.m + 1) * P := by
    calc _ ≤ ∑ _c : Fin (X.m + 1), P := Finset.sum_le_sum fun c _ => by
            simp only [segmentBlockOfMonomial]
            exact (Nat.mod_lt _ hP).le
      _ = (X.m + 1) * P := by simp
  unfold coarseA
  rw [← hPdef]
  calc (B - ∑ c, b.rz i c) / P ≤ B / P := Nat.div_le_div_right (Nat.sub_le _ _)
    _ ≤ (B - ∑ c, (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c + (X.m + 1) * P) / P :=
        Nat.div_le_div_right (by omega)
    _ = _ := Nat.add_mul_div_right _ _ hP

end NB

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem jE_mono {s : ℕ} (S : SegData s) {f g : Fin S.t → ℕ} (h : ∀ l, f l ≤ g l) (i : ℕ) : jE S f i ≤ jE S g i := by
  unfold jE
  split_ifs
  · exact h _
  · exact le_rfl

theorem jE_add {s : ℕ} (S : SegData s) (f g : Fin S.t → ℕ) (i : ℕ) : jE S (fun l => f l + g l) i = jE S f i + jE S g i := by
  unfold jE
  split_ifs <;> rfl

theorem jE_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) (i : Fin s) (h : S.sigma ≤ i.val) :
    jE S (fun l => g (uTop S l)) i.val = g i := by
  unfold jE
  rw [dite_eq_left ⟨h, i.2⟩]
  have e : uTop S ⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩ = i := by
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega
  show g (uTop S ⟨i.val - S.sigma, _⟩) = g i
  rw [e]

theorem ch_cases {s : ℕ} (a : Fin (2 * s + 1)) : a = chU s ∨ (∃ i : Fin s, a = chW i) ∨ ∃ i : Fin s, a = chE i := by
  have ha := a.2
  by_cases h : a.val = 2 * s
  · exact Or.inl (Fin.ext h)
  · by_cases h2 : a.val % 2 = 0
    · exact Or.inr (Or.inl ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2); omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2) + 1; omega)⟩)


theorem segCoreAt_of_num {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm n hn1 hnc β hβ L e he1 hen j
  intro (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
  intro hju Gu du hGI hGP hdu hGY A hcz hcw hcy hcx hy0 hγ dz dy dx
  classical
  have hp : 0 < X.p := hD.1.pos
  have hKz : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero_prime S hD.1
  have hsN : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hQ1 : 1 ≤ X.p ^ X.G' * e := Nat.mul_pos (pow_pos hp _) he1
  obtain ⟨hroom, hnum⟩ := hN X hD hH hc mm hmm n hn1 hnc e he1 hen j (β j) (hβ j)
  obtain ⟨hdig, hU, hSt, hoP, -⟩ := hβ j
  have hA' := nb_coarseA C0 CE1 CE2 X j ju (L.jp j) du A hp dz
  have hC' := nb_coarseC C0 CE1 CE2 X j ju (L.jp j) du A hp dy
  have hdig' := nb_digits C0 CE1 CE2 X j ju (L.jp j) du A hp dz dy
  have hez : ∀ i, ∑ c, ezA C0 CE1 CE2 X j A i c ≤ X.p ^ X.G' * e := fun i =>
    nb_ez_le C0 CE1 CE2 X j A hp (β j) hdig _ i (hcw i)
  have hlb := level_bounds X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (L.ok j)
  have hjE : ∀ i : ℕ, jE (X.seg C0 CE1 CE2 j) ju i ≤ jE (X.seg C0 CE1 CE2 j) (L.lv j) i := fun i => jE_mono _ hju i

  have hduW : ∀ i : Fin (segS X.TT j), du (chW i) ≤
      (if i.val < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i) - jE (X.seg C0 CE1 CE2 j) (L.lv j) i.val := by
    intro i
    have h1 := hdu (chW i)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chW i)
    have h3 := segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chW i) i rfl
    have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
    rw [h3, q] at h2
    have h1' : du (chW i) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chW i) := h1
    omega
  have hduU : du (chU _) ≤ (β j).oPlus - L.jp j := by
    have h1 := hdu (chU _)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chU _)
    have h3 := chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chU _) rfl
    rw [h3, if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)] at h2
    have h1' : du (chU _) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chU _) := h1
    omega

  have hy0U : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_neg (by omega)] at h
    have := block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i 0 h
    omega
  have hy0S : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → y0A C0 CE1 CE2 X j A i ≤ (β j).sg i + X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_pos hi] at h
    exact block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ h
  have hyz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
    intro i hi
    have h1 := hcz i
    rw [if_neg (by omega)] at h1
    have h2 := hcy i
    rw [if_neg (by omega), mul_zero, add_zero] at h2
    have h3 := hroom i hi
    exact block_y_zero_le_z_zero C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ (by omega) h1 h2

  have oU : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).o i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = _
    rw [if_neg (by omega)]
  have wS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).w i = du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have sgS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).sg i = y0A C0 CE1 CE2 X j A i := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have oP : (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).oPlus = L.jp j + du (chU _) + ∑ c, axA X j A c := rfl
  have dx' : L.jp j + du (chU _) + (A ((topEnd X j, true), 0) + ∑ c, axA X j A c) = (segAPlus X.TT X.aT j) := by
    rw [← dx, Fin.sum_univ_succ]
    rfl
  have hcx' : ∑ c, axA X j A c ≤ X.p ^ X.G' * e := hcx
  obtain ⟨hBL', hthr⟩ := hnum (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) hdig' (fun i => nb_coarseA_ge C0 CE1 CE2 X j ju (L.jp j) du A hp (β j) i)
    (by
      intro i hi
      have a1 := hA' i
      have a2 := oU i hi
      have a3 := hyz i hi
      have a4 := hy0U i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_neg (by omega)] at a6
      have a7 := hjE i.val
      have a8 := (hlb.1 i hi).1
      refine ⟨by omega, by omega, ?_, ?_⟩
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)]
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)])
    (by
      intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      have a3 := sgS i hi
      have a4 := hy0S i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_pos hi] at a6
      have a7 := hC' i
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = 0
      rw [if_pos hi])
    (by omega) (by have := hlb.2; omega)
  refine ⟨(segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A), hBL', nb_ord C0 CE1 CE2 X j ju (L.jp j) du A,
    uTot O X.m (X.seg C0 CE1 CE2 j) ju (L.jp j) (Gu * (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (fun l => z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l)) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))
      (A ((topEnd X j, true), 0)) (L.γ j), ?_, ?_⟩
  · refine uTot_mem (fun l => hyz _ (Nat.le_add_right _ _)) ?_ (by omega) (du + (dEps (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (intPol_mul' hGI (mEps_int _ _ _)) (hom_Pol_mul (KK O) hGP (mEps_pol (KK O) _ _ _)) ?_ ?_ ?_
    · intro l
      have hi : (X.seg C0 CE1 CE2 j).sigma ≤ (uTop (X.seg C0 CE1 CE2 j) l).val := Nat.le_add_right _ _
      have a1 := hA' (uTop (X.seg C0 CE1 CE2 j) l)
      have a2 := oU _ hi
      have a3 := hyz _ hi
      omega
    · intro a
      rw [jE_add]
      simp only [Pi.add_apply]
      rcases ch_cases a with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chU _) rfl, dEps_U,
          if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)]
        have q : (chU (segS X.TT j)).val / 2 = segS X.TT j := by show 2 * segS X.TT j / 2 = _; omega
        rw [q, jE_top, jE_top, oP]
        omega
      · have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
        have hne : ¬ (chW i).val = 2 * segS X.TT j := by have := i.2; show ¬ 2 * i.val = _; omega
        rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chW i) i rfl, dEps_chW_eq_sum, q, if_neg hne]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, wS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, oU i (by omega), jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
      · have q : (chE i).val / 2 = i.val := by show (2 * i.val + 1) / 2 = _; omega
        have hne : ¬ (chE i).val = 2 * segS X.TT j := by show ¬ 2 * i.val + 1 = _; omega
        rw [chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chE i) i rfl, dEps_E, q, if_neg hne, hC' i]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, sgS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
    · have h1 := L.hγ j
      have h2 : L.jp j ≤ (X.seg C0 CE1 CE2 j).bPlus := le_trans (L.ok j).2 (min_le_right _ _)
      have h1' : ∑ c, L.γ j c = (X.seg C0 CE1 CE2 j).bPlus - L.jp j := h1
      omega
    · intro m hm k
      have hW : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chW i) = true := by
        intro i
        show decide ((2 * i.val) % 2 = 0) = true
        simp
      have hE : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chE i) = false := by
        intro i
        show decide ((2 * i.val + 1) % 2 = 0) = false
        simp
      have g0 := hGY k
      have g1 := ycond_mEps (K := KK O) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hE
        (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)
      have g2 := ycond_pairs (K := KK O) (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hW hE
        (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l)
      have g3 := ycond_mul (L.LL j) _ _ _ (ycond_mul (L.LL j) _ _ _ g0 g1) g2
      have hinc := rowInc_le (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k)
        (ezA C0 CE1 CE2 X j A) (axA X j A) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l) (X.p ^ X.G' * e) hez hcx'
        (fun l => le_trans (Nat.sub_le _ _) (hy0U _ (Nat.le_add_right _ _)))
      have hcong := ycond_congr (K := KK O) (r := X.m)
        (LL := (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).lettersAt (fun l => ju l + m l) (L.jp j)) (LL' := L.LL j) rfl
        ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.J k) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.thr k)
      rw [hcong]
      refine ycond_mono (L.LL j) _ ?_ g3
      have t1 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) k
      have t2 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) k
      have hV : ((∑ i, ((∑ c, ezA C0 CE1 CE2 X j A i c : ℕ) : ℤ) *
            (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW i) : ℤ)) +
          ((∑ c, axA X j A c : ℕ) : ℤ) * (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chU _) : ℤ)) +
          ∑ l, ((y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l : ℕ) : ℤ) *
            (pWt ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW (uTop (X.seg C0 CE1 CE2 j) l)) (chE (uTop (X.seg C0 CE1 CE2 j) l)) : ℤ) ≤
          ((X.N1 : ℤ) + 1) * (((X.m : ℤ) + 1) + (X.p : ℤ) ^ X.G' * e) := by
        refine le_trans hinc ?_
        have b1 : ((segS X.TT j : ℕ) : ℤ) ≤ X.N1 := by exact_mod_cast hsN
        have b2 : (0 : ℤ) ≤ ((X.p ^ X.G' * e : ℕ) : ℤ) := Int.natCast_nonneg _
        have b3 : ((X.p ^ X.G' * e : ℕ) : ℤ) = (X.p : ℤ) ^ X.G' * e := by push_cast; ring
        have b4 : (0 : ℤ) ≤ (X.m : ℤ) := Int.natCast_nonneg _
        have b5 : (0 : ℤ) ≤ (X.N1 : ℤ) := Int.natCast_nonneg _
        rw [← b3]
        nlinarith
      have hfin := hthr (capIdx (X.seg C0 CE1 CE2 j) k) _ hV
      have t1' : (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k = _ := t1
      rw [t1', t2, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
  · have hhead : L.head O j ju Gu = ioA (KK O) X.p C0 CE1 CE2 X j
        ((∏ l, EhS O X.m (X.seg C0 CE1 CE2 j) l ^ ju l) * EpS O X.m (X.seg C0 CE1 CE2 j) ^ L.jp j *
          rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) Gu) := rfl
    rw [hhead, segMon_eq O C0 CE1 CE2 X j ju (L.jp j) du A (L.γ j) ?_ hy0 hγ, ioBlock_eq]
    · unfold uTot
      simp only [map_mul]
      ring
    · intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      rw [jE_S _ _ hi] at a1
      omega

theorem restSegCore_of_num (h : RestNumCore) : RestSegCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => segCoreAt_of_num h) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end
