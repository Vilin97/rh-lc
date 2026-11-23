module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TailTGlueT
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypOfTypical
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WindowSmall

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DomOfStripDown

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

theorem glueT_lt (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : m.val < r - t) :
    glueT t be τ m = be := by
  unfold glueT; rw [dite_eq_left h]

theorem glueT_ge (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : r - t ≤ m.val) :
    glueT t be τ m = τ ⟨m.val - (r - t), by have := m.2; omega⟩ := by
  unfold glueT; rw [dite_eq_right (by omega), dite_eq_left]

theorem dom_of_strip_up {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hm1 : (m'.val - 1) + 1 < n := by have := m'.2; have : m.val < m'.val := hlt; omega
    have h2 := h.2.1 ⟨m'.val - 1, by have := m'.2; omega⟩ hm1
    have hme : (⟨(m'.val - 1) + 1, hm1⟩ : Fin n) = m' := Fin.ext (by simp only; have : m.val < m'.val := hlt; omega)
    rw [hme] at h2
    have h3 : ν ⟨m'.val - 1, by have := m'.2; omega⟩ ≤ ν m :=
      hν (by rw [Fin.le_def]; simp only; have : m.val < m'.val := hlt; omega)
    exact le_trans h2 (le_trans h3 (h.1 m))

theorem dom_of_strip_down {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hlt' : m.val < m'.val := hlt
    have hm1 : m.val + 1 < n := by have := m'.2; omega
    have h2 := h.2.1 m hm1
    have h3 : ν m' ≤ ν ⟨m.val + 1, hm1⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    exact le_trans (h.1 m') (le_trans h3 h2)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem tau_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (H : HypT N n0 r K LL B od bb a La p)
    (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (t s : ℕ) (hst : s + t = N) (_ht : t ≤ r) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (K + t) (tailT t (μ0 ⟨s, by omega⟩)) := by
  intro t
  induction t with
  | zero =>
    intro s hst _ μ0 hv
    have hsN : s = N := by omega
    subst hsN
    have hμ : μ0 ∈ SP (r := r) (K := K) LL n0 B := (sp_iff H μ0).2 hv
    have hA : Af hfin s μ0 = (finite_St (tanPart μ0)).toFinset.image (fun I => (μ0, I)) := by
      ext q
      unfold Af
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨⟨_, h2⟩, h3'⟩
        have hq : q.1 = μ0 := funext fun t => h3' t (by have := t.2; omega)
        exact ⟨q.2, by rw [← hq]; exact h2, Prod.ext hq.symm rfl⟩
      · rintro ⟨I, hI, rfl⟩
        exact ⟨⟨hμ, hI⟩, fun t _ => rfl⟩
    have hdom : Dominant (pEnd (tanPart μ0)) := by
      intro x y hxy
      exact hv.2.1 (Fin.last s) (by simp) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
    rw [hA, Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).2), ← Set.ncard_eq_toFinset_card _ (finite_St (tanPart μ0)),
      wt_eq D h3 _ hdom]
    show stCount K _ = stCount K _
    congr 1
    funext l
    have := tailT_apply (r := r) (K := K) 0 (Nat.zero_le r) (μ0 ⟨s, by omega⟩) l
    rw [show (tailT 0 (μ0 ⟨s, by omega⟩) : Fin (K + 0) → ℤ) l = _ from this]
    unfold pEnd tanPart
    congr 1
  | succ t ih =>
    intro s hst ht μ0 hv
    have hs : s < N := by omega
    have hN := H.hN
    have hn0 : n0 ≤ s := by omega
    have hla : ∀ m, μ0 (⟨s, hs⟩ : Fin N).castSucc m ≤ (beA n0 B : ℤ) := fun m => vp_le hv s (by omega) le_rfl m
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    generalize hlaeq : μ0 (⟨s, hs⟩ : Fin N).castSucc = la at hla hlad
    have hheads : ∀ m : Fin (r + K), m.val + 1 < r - t → la m = (beA n0 B : ℤ) := by
      intro m hm
      have hs1 : s - 1 < N := by omega
      have h1 := ((hv.2.2 ⟨s - 1, hs1⟩ (by simp only; omega)).2 (by simp only; omega)).2 m (by simp only; omega)
      have he : (⟨s - 1, hs1⟩ : Fin N).succ = (⟨s, hs⟩ : Fin N).castSucc := Fin.ext (by simp; omega)
      rw [he, hlaeq] at h1
      exact h1
    have hν : ∀ l : Fin (K + t + 1), (tailT (t + 1) la : Fin (K + t + 1) → ℤ) l =
        la ⟨(r - (t + 1)) + l.val, by have := l.2; omega⟩ := fun l => tailT_apply (t + 1) ht la l
    have hνdom : Dominant (tailT (t + 1) la : Fin (K + t + 1) → ℤ) := by
      intro x y hxy
      rw [hν, hν]
      exact hlad (by rw [Fin.le_def] at hxy ⊢; simp only; omega)
    set ν : Fin (K + t + 1) → ℤ := tailT (t + 1) la with hνdef
    set T := Fintype.piFinset (fun l : Fin (K + t) => Finset.Icc (ν l.succ) (ν l.castSucc)) with hT
    have hτ : ∀ τ ∈ T, ∀ l : Fin (K + t), ν l.succ ≤ τ l ∧ τ l ≤ ν l.castSucc := by
      intro τ hτ l
      rw [hT, Fintype.mem_piFinset] at hτ
      exact Finset.mem_Icc.mp (hτ l)
    have hinj : Set.InjOn (glueT (r := r) t (beA n0 B : ℤ)) (T : Set (Fin (K + t) → ℤ)) := by
      intro τ _ τ' _ h
      rw [← tailT_glueT (r := r) t (by omega) (beA n0 B : ℤ) τ, h, tailT_glueT (r := r) t (by omega)]
    have hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ T.image (glueT (r := r) t (beA n0 B : ℤ)) := by
      intro q hq
      obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
      rw [hlaeq] at hstq
      obtain ⟨⟨d, hS⟩, hh⟩ := hstq.2 hn0
      generalize q.1 (⟨s, hs⟩ : Fin N).succ = la' at hS hh
      rw [Finset.mem_image]
      refine ⟨tailT t la', ?_, ?_⟩
      · rw [hT, Fintype.mem_piFinset]
        intro l
        have hl := l.2
        rw [Finset.mem_Icc, hν, hν, tailT_apply t (by omega)]
        constructor
        · have := hS.1 ⟨(r - t) + l.val, by omega⟩
          have he : (⟨(r - (t + 1)) + (l.succ : Fin (K + t + 1)).val, by simp; omega⟩ : Fin (r + K)) =
              ⟨(r - t) + l.val, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact this
        · have := hS.2.1 ⟨(r - (t + 1)) + l.val, by omega⟩ (by simp only; omega)
          have he : (⟨(r - (t + 1)) + l.val + 1, by omega⟩ : Fin (r + K)) = ⟨(r - t) + l.val, by omega⟩ :=
            Fin.ext (by simp only; omega)
          rw [he] at this
          exact this
      · funext m
        by_cases hm : m.val < r - t
        · rw [glueT_lt t _ _ m hm, hh m (by simp only; omega)]
        · rw [glueT_ge t (by omega) _ _ m (by omega), tailT_apply t (by omega)]
          congr 1
          exact Fin.ext (by simp only; omega)
    have hterm : ∀ τ ∈ T, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ
        (glueT (r := r) t (beA n0 B : ℤ) τ))).card = stCount (K + t) τ := by
      intro τ hτT
      have hb := hτ τ hτT
      have hτanti : ∀ l l' : Fin (K + t), l ≤ l' → τ l' ≤ τ l := by
        intro l l' hll
        rcases eq_or_lt_of_le hll with he | hlt
        · rw [he]
        · have h1 := (hb l').2
          have h2 := (hb l).1
          have h3 : ν l'.castSucc ≤ ν l.succ := hνdom (by rw [Fin.le_def]; simp; exact hlt)
          linarith
      have hτbe : ∀ l : Fin (K + t), τ l ≤ (beA n0 B : ℤ) := by
        intro l
        refine le_trans (hb l).2 ?_
        rw [hν]; exact hla _
      have hd' : Dominant (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        intro m m' hmm
        have hmm' : m.val ≤ m'.val := hmm
        by_cases h1 : m'.val < r - t
        · rw [glueT_lt t _ _ m' h1, glueT_lt t _ _ m (by omega)]
        · rw [glueT_ge t (by omega) _ _ m' (by omega)]
          by_cases h2 : m.val < r - t
          · rw [glueT_lt t _ _ m h2]; exact hτbe _
          · rw [glueT_ge t (by omega) _ _ m (by omega)]
            exact hτanti _ _ (by rw [Fin.le_def]; simp only; omega)
      have hS1 : ∀ x, la x ≤ glueT (r := r) t (beA n0 B : ℤ) τ x := by
        intro x
        by_cases h1 : x.val < r - t
        · rw [glueT_lt t _ _ x h1]; exact hla x
        · rw [glueT_ge t (by omega) _ _ x (by omega)]
          have h2 := (hb ⟨x.val - (r - t), by have := x.2; omega⟩).1
          rw [hν] at h2
          have he : (⟨(r - (t + 1)) + ((⟨x.val - (r - t), by have := x.2; omega⟩ : Fin (K + t)).succ :
              Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
          rw [he] at h2
          exact h2
      have hst' : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        rw [hlaeq]
        refine ⟨fun h => absurd h (by simp only; omega), fun _ => ⟨⟨(∑ x, (glueT (r := r) t (beA n0 B : ℤ) τ x - la x)).toNat,
          hS1, ?_, ?_⟩, fun m hm => glueT_lt t _ _ m (by simp only at hm; omega)⟩⟩
        · intro x hx
          by_cases h1 : x.val + 1 < r - t
          · rw [glueT_lt t _ _ _ (by simp only; exact h1), hheads x h1]
          · rw [glueT_ge t (by omega) _ _ _ (by simp only; omega)]
            have h2 := (hb ⟨x.val + 1 - (r - t), by have := x.2; omega⟩).2
            rw [hν] at h2
            have he : (⟨(r - (t + 1)) + ((⟨x.val + 1 - (r - t), by have := x.2; omega⟩ : Fin (K + t)).castSucc :
                Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
            rw [he] at h2
            exact h2
        · exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => sub_nonneg.mpr (hS1 x))).symm
      have hv' := vp_update hs hv _ hd' hst'
      rw [ih (s + 1) (by omega) (by omega) _ hv']
      congr 1
      show tailT t (Function.update μ0 (⟨s, hs⟩ : Fin N).succ (glueT (r := r) t (beA n0 B : ℤ) τ)
        (⟨s, hs⟩ : Fin N).succ) = τ
      rw [Function.update_self, tailT_glueT t (by omega)]
    rw [Af_card_sum hfin s hs μ0 _ hE, Finset.sum_image hinj, Finset.sum_congr rfl hterm]
    have h4' := h4 (K + t) ν hνdom
    show _ = stCount (K + t + 1) (tailT (t + 1) (μ0 (⟨s, hs⟩ : Fin N).castSucc))
    rw [hlaeq]
    exact h4'.symm

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdFromSelfEqOne

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [if_neg he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_neg (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_pos hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_neg (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightOfTopCount

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

theorem lemT_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : LemT :=
  lemT_of (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) path_count_finite (atypical_path_small_weight D hAdm.2.2.1) typical_path_orders_small

theorem good_path_weight_of_top_count (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (h41 : TopCountLowerBounds 1088) : GoodPathWeight 1088 :=
  good_path_weight_of_parts 1088 (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) (lemT_of_adm D hAdm) (TE.letter_dictionary_bounds h41)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightAlt

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem good_path_weight (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : GoodPathWeight 1088 :=
  good_path_weight_of_top_count D hAdm (top_count_lower_bounds 1088 (by norm_num))

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end
