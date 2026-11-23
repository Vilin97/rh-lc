module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
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
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.FreeFamily

section

@[expose] public section

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem exists_free_family (Y : Finset ℝ) (w : List (Bool × ℝ)) (K D : ℕ)
    (hw : ∀ l ∈ w, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1))
    (hcard : w.length + K * D ≤ Y.card) :
    ∃ g : Fin K → Fin D → ℝ, (∀ a i, g a i ∈ Y) ∧
      (∀ a i a' i', g a i = g a' i' → a = a' ∧ i = i') ∧
      ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ g a i ∧ (l = (true, y) ∨ l = (false, y + 1)) := by
  classical
  choose! f hfY hf using hw
  set S : Finset ℝ := (w.map f).toFinset with hS
  have hSc : S.card ≤ w.length := by
    calc S.card ≤ (w.map f).length := List.toFinset_card_le _
      _ = w.length := List.length_map _
  have hT : K * D ≤ (Y \ S).card := by
    have h1 := Finset.le_card_sdiff S Y
    generalize K * D = m at hcard ⊢
    omega
  obtain ⟨emb⟩ : Nonempty (Fin (K * D) ↪ ↥(Y \ S)) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa using hT
  let φ : Fin K × Fin D ≃ Fin (K * D) := finProdFinEquiv
  refine ⟨fun a i => (emb (φ (a, i)) : ℝ), ?_, ?_, ?_⟩
  · intro a i
    exact (Finset.mem_sdiff.mp (emb (φ (a, i))).2).1
  · intro a i a' i' h
    have h1 := emb.injective (Subtype.ext h)
    have h2 := φ.injective h1
    simp only [Prod.mk.injEq] at h2
    exact h2
  · intro a i l hl
    refine ⟨f l, hfY l hl, ?_, hf l hl⟩
    intro heq
    have heq' : f l = (emb (φ (a, i)) : ℝ) := heq
    have hmem := (Finset.mem_sdiff.mp (emb (φ (a, i))).2).2
    apply hmem
    rw [← heq', hS, List.mem_toFinset, List.mem_map]
    exact ⟨l, hl, rfl⟩

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.GridSum

section

@[expose] public section

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem grid_sqrt_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i))
    (n : Fin K → Fin (d + 1)) :
    Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  have hmap : ∀ h : ℝ → ℝ,
      ((List.ofFn fun a => grid a (n a)).map h).prod = ∏ a, h (grid a (n a)) := by
    intro h
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  simp only [hmap]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  have hle : ∏ a, nn (grid a (n a)) * nn (grid a (n a) + 1) / Q (grid a (n a)) ≤
      ∏ _a : Fin K, β ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro a _
      have h := hpos a (n a)
      exact div_nonneg (mul_nonneg h.1.le h.2.1.le) h.2.2.le
    · intro a _
      rw [div_le_iff₀ (hpos a (n a)).2.2]
      exact hb a (n a)
  calc _ ≤ Real.sqrt (∏ _a : Fin K, β ^ 2) := Real.sqrt_le_sqrt hle
    _ = β ^ K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, pow_mul',
        Real.sqrt_sq (pow_nonneg hβ K)]

theorem grid_sum_le {K d : ℕ} (grid c : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hc : ∀ a, ∑ i, |c a i| ≤ 1)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i)) :
    ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| *
      Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  calc _ ≤ ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| * β ^ K := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (grid_sqrt_le grid nn Q β hβ hpos hb n) (abs_nonneg _)
    _ = (∏ a, ∑ i, |c a i|) * β ^ K := by
        rw [← Finset.sum_mul, Fintype.prod_sum]
        simp only [Finset.abs_prod]
    _ ≤ 1 * β ^ K := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ K)
        apply Finset.prod_le_one₀
        · intro a _
          exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
        · intro a _
          exact hc a
    _ = β ^ K := one_mul _

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.LagSum

section

@[expose] public section

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem lag_abs_term_le {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by
  rw [abs_prod]
  have hcard : ((univ : Finset (Fin (d + 1))).erase j).card = d := by
    rw [Finset.card_erase_of_mem (mem_univ j)]; simp
  calc ∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, |(y j - y i)⁻¹|
      ≤ ∏ _i ∈ (univ : Finset (Fin (d + 1))).erase j, (1 / 5 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i hi
          have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          rw [abs_inv]
          have hx : 0 < |y j - y i| := lt_of_lt_of_le (by norm_num) (h j i hij)
          simpa only [one_div] using
            (div_le_div_iff₀ (a := (1 : ℝ)) (b := |y j - y i|) (c := 1) (d := 5)
              hx (by norm_num : 0 < (5 : ℝ))).2 (by simpa using h j i hij)
    _ = (1 / 5 : ℝ) ^ d := by rw [Finset.prod_const, hcard]

theorem lag_abs_sum_le_one {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) :
    ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ 1 := by
  have hn : (d : ℝ) + 1 ≤ 5 ^ d := by
    have : d + 1 ≤ 5 ^ d := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this
  calc ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹|
      ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d :=
        Finset.sum_le_sum (fun j _ => lag_abs_term_le y h j)
    _ = ((d : ℝ) + 1) / 5 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow]
        push_cast; ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hn

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bridge

section

@[expose] public section

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset

theorem cutWord_of_list (P : M.Par) (l0 : ℕ) (L : List C.Letter)
    (hc : ∀ l ∈ L, I.OnCut P.u P.u' l0 l.2)
    (hp : L.Pairwise fun l l' => 2 < |l.2 - l'.2|) : KB.CutWord P l0 L := by
  refine ⟨fun a => hc _ (List.get_mem L a), fun a b hab => ?_⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact List.pairwise_iff_get.1 hp a b h
  · have := List.pairwise_iff_get.1 hp b a h
    rwa [abs_sub_comm] at this

theorem list_of_cutWord {P : M.Par} {l0 : ℕ} {L : List C.Letter} (h : KB.CutWord P l0 L) :
    (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise fun l l' => 2 < |l.2 - l'.2| := by
  refine ⟨fun l hl => ?_, List.pairwise_iff_get.2 fun a b hab => h.2 a b (ne_of_lt hab)⟩
  obtain ⟨a, rfl⟩ := List.get_of_mem hl
  exact h.1 a

theorem two_lt_of_five {a t : ℝ} (ha : 5 ≤ |a|) (ht : |t| ≤ 1) : 2 < |a + t| := by
  have h := abs_add_le (a + t) (-t)
  rw [add_neg_cancel_right, abs_neg] at h
  linarith

theorem free_dist {Y : Finset ℝ} (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) {y : ℝ} (hy : y ∈ Y)
    {l : C.Letter} (hl : ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) :
    2 < |y - l.2| ∧ 2 < |(y + 1) - l.2| := by
  obtain ⟨y', hy', hne, h | h⟩ := hl
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨by simp only; linarith, ?_⟩
    have e : (y + 1) - y' = (y - y') + 1 := by ring
    simp only
    rw [e]
    exact two_lt_of_five h5 (by norm_num)
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨?_, ?_⟩
    · have e : y - (y' + 1) = (y - y') + (-1) := by ring
      simp only
      rw [e]
      exact two_lt_of_five h5 (by norm_num)
    · have e : (y + 1) - (y' + 1) = y - y' := by ring
      simp only
      rw [e]
      linarith

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gridOK_of_free (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K : ℕ) (w : List C.Letter)
    (d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hw : KB.CutWord P p.l0 w)
    (hY : ∀ a i, grid a i ∈ Y)
    (hinj : ∀ a i a' i', grid a i = grid a' i' → a = a' ∧ i = i')
    (hfree : ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ grid a i ∧ (l = (true, y) ∨ l = (false, y + 1)))
    (hq : ∀ a i, (0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧
        0 < (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) ∧
        nn (grid a i) * nn (grid a i + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) :
    TBBx5.GridOK p nn Y B K w d grid := by
  have hsepg : ∀ a i a' i', (a, i) ≠ (a', i') → 5 ≤ |grid a i - grid a' i'| := by
    intro a i a' i' hne
    refine hsep _ (hY a i) _ (hY a' i') fun h => hne ?_
    obtain ⟨h1, h2⟩ := hinj a i a' i' h
    rw [h1, h2]
  obtain ⟨hwc, hwp⟩ := list_of_cutWord hw
  refine ⟨fun a i j h => (hinj a i a j h).2, hY, fun n => ?_, ?_⟩
  · have hnew : (TBBx5.ysOf grid n).Pairwise fun y y' => 2 < |y - y'| := by
      unfold TBBx5.ysOf
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hsepg a (n a) b (n b) (fun h => (ne_of_lt hab) (Prod.mk.inj h).1)
      linarith
    have hmem : ∀ y ∈ TBBx5.ysOf grid n, ∃ a, grid a (n a) = y := fun y hy => List.mem_ofFn.1 hy
    refine ⟨?_, ?_, hnew⟩
    · rw [TBBx5.plusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).1
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 hnew, hwp, fun l hl l' hl' => ?_⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
        obtain ⟨a, rfl⟩ := hmem y hy
        exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).1
    · rw [TBBx5.minusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).2
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 (hnew.imp fun h => ?_), hwp, fun l hl l' hl' => ?_⟩
        · simpa [add_sub_add_right_eq_sub] using h
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).2
  · exact GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.grid_sum_le grid (fun a i => F7.lagCo (grid a) i) nn
      (fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) B hB
      (fun a => GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_sum_le_one (grid a)
        (fun i j h => hsepg a i a j (fun h' => h (Prod.mk.inj h').2)))
      (fun a i => (hq a i).1) (fun a i => (hq a i).2)

def FreeBound (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N → ∀ y ∈ Y,
    (∀ l ∈ w, ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) →
    (0 < nn y ∧ 0 < nn (y + 1) ∧ 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) ∧
      nn y * nn (y + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re

theorem waveGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.WaveGrid p nn Y B K N := by
  intro j hj w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * j + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K (2 * j + 1)
    hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * j) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

theorem liftGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.LiftGrid p nn Y B K N := by
  intro b s hb hs hbs w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * (b + s - 1 - s) + s + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K
    (2 * (b + s - 1 - s) + s + 1) hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * (b + s - 1 - s) + s) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

end grid

end CompanionTheory.WaveGrid
end
end
