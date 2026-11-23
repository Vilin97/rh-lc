module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports
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
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DigitsOKOfCompat
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CoarseCLower
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SegmentWeightedCountingBoundOfAllRemainingBounds

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem rank_le {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) (dl : DCl X)
    (hc : Compat C0 CE1 CE2 X dl aTop) :
    clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl ≤ mCl C0 CE1 CE2 X dl aTop := by
  have hIn := realise hH aTop aPlus hT hP
  have hm0 : 0 ≤ X.m := hH.2.2.2.2.2.2.2.2.1
  have hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) := hH.2.2.2.2.2.2.2.2.2
  have h := h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2
  rw [rankOnDigits_eq, realW_top, realW_plus] at h
  exact (h hc).2

theorem mem_cbox {dl : DCl X} {aTop : Fin X.s → ℕ} :
    aTop ∈ cbox C0 CE1 CE2 X dl ↔
      aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem clSum_levels (dl : DCl X) (aTop : Fin X.s → ℕ) (f : SegBlock X.s X.r → Lv C0 CE1 CE2 X → ℕ) :
    ((clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, f b x) aTop dl : ℕ) : ℝ) =
      ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (f z.1 z.2 : ℝ) := by
  rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
  unfold idx keptSet
  rw [Finset.sum_sigma]
  push_cast
  rfl

theorem claim2 {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hDir : RestDir C0 CE1 CE2 X) (hW : X.winA.Nonempty)
    (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) ≤ (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
  obtain ⟨aPlus, hP⟩ := hW
  obtain ⟨hT, hc⟩ := mem_cbox.1 ha
  rw [← clSum_levels dl aTop (fun b x => rL C0 CE1 CE2 X aTop b x)]
  have h1 : clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x) aTop dl ≤
      clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl := by
    rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop), clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
    refine Finset.sum_le_sum fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b :=
      (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop).mem_toFinset.1 (Finset.mem_filter.1 hb).1
    exact hDir aTop hT aPlus hP b hk
  exact_mod_cast h1.trans (rank_le hH h11 aTop aPlus hT hP dl hc)

theorem digit_class_dimension_comparison_of_remaining_estimates {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (CM : ℝ) (hCM : 0 ≤ CM)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hPlus : RestPlus C0 CE1 CE2 X CM) (hTM : RestTM C0 CE1 CE2 X CM) (hDir : RestDir C0 CE1 CE2 X)
    (hFree : RestFree C0 CE1 CE2 X) (hRat : RestRatio C0 CE1 CE2 X) :
    DigitClassDimensionComparison C0 CE1 CE2 X (fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
      ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) := by
  classical
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  intro dl hdl
  have hbox : (CountingStatementReduction.box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1) = cbox C0 CE1 CE2 X dl ×ˢ X.winA := by
    ext a
    simp only [CountingStatementReduction.box, Finset.mem_filter, Finset.mem_product, mem_cbox]
    tauto
  rw [hbox, Finset.sum_product, Finset.sum_product]
  have hR : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ _aPlus ∈ X.winA, (mCl C0 CE1 CE2 X dl aTop : ℝ) =
      (X.winA.card : ℝ) * ∑ aTop ∈ cbox C0 CE1 CE2 X dl, (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hR]
  by_cases hW : X.winA.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hW
    simp [hW]
  by_cases hA : (cbox C0 CE1 CE2 X dl).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [hA]
  obtain ⟨a0, ha0⟩ := hA
  have hL : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA,
        ((clSum C0 CE1 CE2 X (fun b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋) aTop dl : ℕ) : ℝ) =
      ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ∑ z ∈ idx C0 CE1 CE2 X dl a0,
        (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    refine Finset.sum_congr rfl fun aTop ha => Finset.sum_congr rfl fun aPlus _ => ?_
    rw [← hFree dl hdl aTop ha a0 ha0]
    exact clSum_levels dl aTop (fun b x => bLvl C0 CE1 CE2 X aTop aPlus b x ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
  rw [hL]
  have key := assemble (cbox C0 CE1 CE2 X dl) X.winA (idx C0 CE1 CE2 X dl a0)
    (Finset.univ : Finset (Fin (X.S C0 CE1 CE2).t))
    (fun aTop aPlus z => (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun aTop z => (bY C0 CE1 CE2 X aTop z.1 z.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun z => (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ))
    (fun aTop z => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ))
    (fun aTop i => upd C0 CE1 CE2 X dl aTop i)
    (fun aTop => (mCl C0 CE1 CE2 X dl aTop : ℝ))
    ((30 + CM) / X.L.Y) (5 / X.L.Y) (Real.exp 3) (by positivity) (by positivity) (fun z => Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fin] at key
    exact key
  · intro aTop ha z hz
    have h := hPlus dl hdl aTop ha z (by rw [hFree dl hdl aTop ha a0 ha0]; exact hz)
    have e : (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) =
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ) *
          (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ) := by
      unfold rL
      push_cast
      rfl
    rw [e] at h
    exact h
  · intro z hz
    exact hTM dl hdl a0 ha0 z hz
  · intro aTop ha
    have h := claim2 hH h11 hDir hW dl aTop ha
    rw [hFree dl hdl aTop ha a0 ha0] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold rL
    push_cast
    rfl
  · intro aTop ha i _
    exact hRat dl hdl aTop ha i

def RestAll (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X ∧
      RestFree C0 CE1 CE2 X ∧ RestRatio C0 CE1 CE2 X ∧ RestDepth C0 CE1 CE2 X CM C

theorem segment_weighted_counting_bound_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) (hCM : 0 ≤ CM)
    (hC : 2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hR : RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X) : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH _
  obtain ⟨hBlk, hPlus, hTM, hDir, hFree, hRat, hD0, hDep⟩ := hR hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  refine ⟨fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋,
    (30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y, by positivity, ?_, ?_,
    digit_class_dimension_comparison_of_remaining_estimates CM hCM hH h11 hPlus hTM hDir hFree hRat⟩
  · have e1 : 2 * ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) * Real.exp 3 =
        2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3 / X.L.Y := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_right _ hY0.le
    have h1 : (30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 ≤
        ((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by
      have : 0 ≤ (30 + CM) * Real.exp 3 := by positivity
      nlinarith
    have h2 : 0 ≤ (30 + CM) * Real.exp 3 + 5 := by positivity
    calc 2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3
        ≤ 2 * (((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1)) * Real.exp 3 := by
          apply mul_le_mul_of_nonneg_right _ he.le
          linarith
      _ = (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by ring
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := mul_le_mul_of_nonneg_right hC (by linarith)
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by
          have : 0 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) :=
            mul_nonneg (le_trans (by positivity) hC) (by linarith)
          nlinarith
  · intro aTop hT aPlus hP b hk
    have h0 : (0 : ℤ) ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.2 (mul_nonneg hY0.le hD0)
    obtain ⟨L₂, hg, hr⟩ := hBlk aTop hT aPlus hP b hk _ h0
    refine ⟨L₂, GoodSub_mono ?_ hg, hr⟩
    have := Int.floor_le (X.L.Y * D1r C0 CE1 CE2 X CM)
    linarith

def RestAllE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM C : ℝ, 0 ≤ CM ∧ 1 ≤ C ∧
    2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X

theorem rest1DAE_of (D : Formalism.BasicNotions.D7) (h : RestAllE D) : DigitClassRemainingUniform D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 Ckap Cs => by
    obtain ⟨CM, C, hCM, hC1, hC, h2⟩ := h1 Ckap Cs
    exact ⟨C, hC1, fun X hA =>
      segment_weighted_counting_bound_of_all_remaining_bounds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X hCM hC hA.2.2.2.2.2.2 (h2 X hA)⟩) h

theorem theorem_A_closed_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (h : RestAllE D) : IntegralityFromMetricForLargeConstants D :=
  counting_statement_uniform_of_digit_class D (rest1DAE_of D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem ratio_num (x y r : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) (h : (r : ℝ) * ((y : ℝ) - x) ≤ 3 * x) :
    (((y + r).choose r : ℕ) : ℝ) ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by
  have h1 := choose_ratio r x y hx hxy
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hq : (y : ℝ) / x ≤ Real.exp (((y : ℝ) - x) / x) := by
    have := Real.add_one_le_exp (((y : ℝ) - x) / x)
    have e : ((y : ℝ) - x) / x + 1 = (y : ℝ) / x := by field_simp; ring
    linarith
  have hq0 : 0 ≤ (y : ℝ) / x := by positivity
  have h2 : ((y : ℝ) / x) ^ r ≤ Real.exp 3 := by
    calc ((y : ℝ) / x) ^ r ≤ Real.exp (((y : ℝ) - x) / x) ^ r := pow_le_pow_left₀ hq0 hq r
      _ = Real.exp ((r : ℝ) * (((y : ℝ) - x) / x)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.2
          rw [← mul_div_assoc, div_le_iff₀ hx0]
          exact h
  calc (((y + r).choose r : ℕ) : ℝ) ≤ ((y : ℝ) / x) ^ r * (((x + r).choose r : ℕ) : ℝ) := h1
    _ ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by gcongr

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem topA_spec (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ X.winA ∧ ∑ c, dl.2 l c ≤ topA C0 CE1 CE2 X dl l ∧
      (X.S C0 CE1 CE2).P X.p l ∣ topA C0 CE1 CE2 X dl l - ∑ c, dl.2 l c ∧ aTop l ≤ topA C0 CE1 CE2 X dl l := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hmem : aTop l ∈ X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c := by
    simp only [Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.1 hT l, hc.2.2 l⟩
  unfold topA
  obtain ⟨x, hxF, hx⟩ := Finset.exists_mem_eq_sup _ ⟨_, hmem⟩ (id : ℕ → ℕ)
  have hle : aTop l ≤ (X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧
      (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c).sup id := Finset.le_sup (f := id) hmem
  rw [hx] at hle ⊢
  simp only [Finset.mem_filter] at hxF
  exact ⟨hxF.1, hxF.2.1, hxF.2.2, hle⟩

theorem upd_mem (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (i : Fin (X.S C0 CE1 CE2).t) :
    upd C0 CE1 CE2 X dl aTop i ∈ cbox C0 CE1 CE2 X dl := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  unfold cbox
  simp only [Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.2 fun l => ?_, ⟨hc.1, hc.2.1, fun l => ?_⟩⟩
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact hs.1
    · rw [Function.update_of_ne h]; exact Fintype.mem_piFinset.1 hT l
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact ⟨hs.2.1, hs.2.2.1⟩
    · rw [Function.update_of_ne h]; exact hc.2.2 l

theorem prod_ratio {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι) (hu : u ∈ s) (f g : ι → ℝ) (K : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hfg : ∀ l ∈ s, l ≠ u → f l = g l) (hK : f u ≤ K * g u) :
    ∏ l ∈ s, f l ≤ K * ∏ l ∈ s, g l := by
  rw [← Finset.mul_prod_erase s f hu, ← Finset.mul_prod_erase s g hu]
  have e : ∏ l ∈ s.erase u, f l = ∏ l ∈ s.erase u, g l :=
    Finset.prod_congr rfl fun l hl => hfg l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
  rw [e]
  have hP : 0 ≤ ∏ l ∈ s.erase u, g l := Finset.prod_nonneg fun l _ => hg l
  calc f u * ∏ l ∈ s.erase u, g l ≤ (K * g u) * ∏ l ∈ s.erase u, g l := mul_le_mul_of_nonneg_right hK hP
    _ = K * (g u * ∏ l ∈ s.erase u, g l) := by ring

theorem ratioCondition_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : RestRatio C0 CE1 CE2 X := by
  classical
  intro dl _ aTop ha i
  refine ⟨upd_mem dl aTop ha i, ?_⟩
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  have hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) := hc
  have hc2 := upd_mem dl aTop ha i
  have hD2 : DigitsOK X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) :=
    (mem_cbox' hc2).2
  obtain ⟨x, hx⟩ : ∃ x, x = coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2)
      (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i)
      (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  have hupdu : upd C0 CE1 CE2 X dl aTop i (uTop (X.S C0 CE1 CE2) i) = topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) := by
    unfold upd
    exact Function.update_self _ _ _
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hkb := hS.kb
  have hb0 := hS.hF.b0
  have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
  have hxP : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hx, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).1]
  have hyP : (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hy, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).1, hupdu]
  have hlow := coarseC_lower hS aTop _ hD (uTop (X.S C0 CE1 CE2) i)
  rw [← hx] at hlow
  have haw := win_ge hS aTop hT (uTop (X.S C0 CE1 CE2) i)
  have hxy : x ≤ y := by
    have h1 : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      rw [hxP, hyP]
      have : (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
        exact_mod_cast hs.2.2.2
      linarith
    have := le_of_mul_le_mul_right h1 (by linarith)
    exact_mod_cast this
  have hxP2 : (X.L.a : ℝ) * (3 / 4) ≤ (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    nlinarith
  have hx1 : 1 ≤ x := by
    have h2 : ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (X.L.a : ℝ) * (3 / 4) := by nlinarith
    have h4 : (1 : ℝ) ≤ (x : ℝ) := by
      by_contra hcn
      push Not at hcn
      have : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) <
          1 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) :=
        mul_lt_mul_of_pos_right hcn (by linarith)
      linarith
    exact_mod_cast h4
  have hnum : (X.r : ℝ) * ((y : ℝ) - x) ≤ 3 * x := by
    have htop : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have h1 := (Finset.mem_Icc.1 hs.1).2
      have h2 : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
          (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le hS.hF.win0)
    have hk : X.L.k = (X.r : ℝ) + 1 := rfl
    have hY := hS.Y1
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hrk : (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y)) ≤ X.L.a := by
      rw [hk]
      have h0 : (0 : ℝ) < ((X.r : ℝ) + 1) * X.L.Y := by nlinarith
      rw [mul_div_assoc', div_le_iff₀ h0]
      have h1 : (X.L.a : ℝ) * (((X.r : ℝ) + 1) * 1) ≤ (X.L.a : ℝ) * (((X.r : ℝ) + 1) * X.L.Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by linarith)) ha0
      linarith
    have hJ : (X.r : ℝ) * X.xa ≤ (X.L.a : ℝ) / 8 := by
      have h1 := hS.xa
      have hLa := hS.La4
      have hLa0 := hS.hF.La0
      unfold Formalism.MainNotions.ColumnSystems.Loc.J0 at h1
      rw [hk] at h1
      have hk0 : (0 : ℝ) < (X.r : ℝ) + 1 := by linarith
      have h2 : (X.r : ℝ) * X.xa ≤ ((X.r : ℝ) + 1) * X.xa := by nlinarith [hS.xa0]
      have h3 : ((X.r : ℝ) + 1) * X.xa ≤ 2 * X.L.La C0 * X.L.b' := by
        have := mul_le_mul_of_nonneg_left h1 hk0.le
        have e : ((X.r : ℝ) + 1) * (2 * (X.L.La C0 * X.L.b' / ((X.r : ℝ) + 1))) = 2 * X.L.La C0 * X.L.b' := by
          field_simp
        linarith
      have h4 : 2 * X.L.La C0 * X.L.b' ≤ ((X.r : ℝ) + 1) / 2 * X.L.b' := by nlinarith
      have h5 : ((X.r : ℝ) + 1) / 2 * X.L.b' ≤ (X.L.a : ℝ) / 8 := by nlinarith
      linarith
    have hd : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
          (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) - aTop (uTop (X.S C0 CE1 CE2) i) := by
        rw [sub_mul, hxP, hyP]; ring
      rw [this]
      linarith
    have h7 : (X.r : ℝ) * (((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) ≤
        (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y) + X.xa) := mul_le_mul_of_nonneg_left hd hr0
    have h6 : (X.r : ℝ) * ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        3 * x * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right h6 (by linarith)
  have hratio := ratio_num x y X.r hx1 hxy hnum
  have hoth : ∀ l, l ≠ uTop (X.S C0 CE1 CE2) i →
      coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l =
        coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l := by
    intro l hl
    unfold coarseC upd
    rw [Function.update_of_ne hl]
  unfold mCl Formalism.MainNotions.ColumnSystems.dimMM
  push_cast
  have hprod := prod_ratio Finset.univ (uTop (X.S C0 CE1 CE2) i) (Finset.mem_univ _)
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
        (coarseC X.L.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseC X.L.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (Real.exp 3) (fun l => by positivity)
    (fun l _ hl => by rw [hoth l hl])
    (by
      rw [← hx, ← hy, symDim_choose X.L.m y, symDim_choose X.L.m x]
      have h0 : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
          (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) := by
        positivity
      calc _ ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
              (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) *
            (Real.exp 3 * (((x + X.r).choose X.r : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hratio h0
        _ = _ := by ring)
  have hA : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p) : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hA) hB
  calc _ ≤ _ := this
    _ = _ := by ring

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOpenConditions

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem thr_mono_seg {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cc, 2 ≤ CYb → 0 ≤ CD → 1 ≤ Cb → 0 ≤ CE1 → 0 ≤ CE2 →
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 a1 a2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 a1 a2
  refine ⟨max T2 2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  have m1 := le_max_left T2 2
  have m2 := le_max_right T2 2
  exact h _ _ _ _ _ _ _ _ _ (m2.trans b1) (by linarith) (by linarith) (by linarith) (by linarith)
    (h2 CYb Cde Ck CD Cb (m1.trans b1) (m1.trans b2) (m1.trans b3) (m1.trans b4) (m1.trans b5))

def RestOpen (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpenE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM : ℝ, 0 ≤ CM ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restAllE_of_open (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : RestAllE D :=
  thr_mono_seg (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hY hD hb h1 h2 hP Ckap Cs => by
    obtain ⟨CM, hCM, hX⟩ := hP Ckap Cs
    have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
    refine ⟨CM, max (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) (18 * (1 + CM) + 20), hCM,
      le_max_of_le_right (by linarith), le_max_left _ _, fun X hA hH => ?_⟩
    obtain ⟨a, b, c, d⟩ := hX X hA hH
    have hS := segFacts hY hb hD h1 h2 hH
    exact ⟨a, b, c, d, restFree_proved hS, ratioCondition_of_segFacts hS,
      restDepth_proved CM _ (by linarith) hCM (le_max_right _ _) hH⟩) h

theorem closed_of_open_conditions (D : Formalism.BasicNotions.D7) (h : RestOpenE D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_all_remaining_bounds D (restAllE_of_open D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
