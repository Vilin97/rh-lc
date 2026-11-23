module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CoarseCLower
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMHypOf
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SegDistsLtG
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.WindowEntryLeTwoMulA
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
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DigitsOKOfCompat
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.UTopVal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMSizeOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}


variable (C0 CE1 CE2 X) in
def aTopPt (dl : DCl X) (a : Fin X.s → ℕ) : Fin X.s → ℕ :=
  ovr (uTop (X.S C0 CE1 CE2)) a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

theorem digits_of_idx {dl : DCl X} {a : Fin X.s → ℕ} {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    Kept X.p X.r (X.S C0 CE1 CE2) a x.1 ∧ (x.1.rz, x.1.ry) = dl ∧ x.2 ∈ lv C0 CE1 CE2 X a x.1 := by
  classical
  unfold idx at hx
  simp only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

theorem Wl_ne {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    (Wl C0 CE1 CE2 X dl l).Nonempty := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  exact ⟨a l, Fintype.mem_piFinset.1 hW l⟩

theorem topA_mem_Wl {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ Wl C0 CE1 CE2 X dl l := by
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)
  rw [topA_eq, hMe]
  exact hM

theorem aTopPt_mem {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) :
    aTopPt C0 CE1 CE2 X dl a ∈ cbox C0 CE1 CE2 X dl := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  rw [hbox]
  exact ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)

theorem setTies_top {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2 := by
  have hb : x.1.ry = dl.2 := congrArg Prod.snd (digits_of_idx hx).2.1
  have e1 := lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2
  show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _
  unfold aTopPt
  rw [e1]
  congr 1
  funext i
  rw [top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]
  unfold cm
  rw [hb]

def RestSI : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i

theorem restTMSize_of (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (hSI : RestSI (C0 := C0) (CE1 := CE1)
    (CE2 := CE2) (X := X)) : RestTMSize C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  classical
  have hT' : aTopPt C0 CE1 CE2 X dl a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) := by
    exact (Finset.mem_filter.mp ha').1
  have e := setTies_top ha hx
  refine ⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [e]
    exact lLL_deg_le hS _ hT' x.1 hK' x.2 y
  · intro i
    show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a
    have h1 := coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)
    have h2 := b_small hS
    have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
    have h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a := by nlinarith
    have h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a := by exact_mod_cast h3
    omega
  ·
    rw [e, Fin.sum_univ_castSucc]
    have hs : 2 * X.s + 2 ≤ X.r := hS.hF.s_le
    have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
    have hr5 := r5 hS
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
    have hlast := lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))
    have hone : ∀ q : Fin (2 * X.s),
        ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a := by
      intro q
      have hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s := by
        have := q.2
        simp only [Fin.val_castSucc]
        omega
      have h1 := chain_wt hS _ hT' x.1 hK' q.castSucc hq
      have h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤
          ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) := by
        exact_mod_cast lLL_deg_le_chain hS _ x.1 x.2 q.castSucc
      have h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) := by
        exact_mod_cast p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)
      calc ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) *
            ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) :=
            mul_le_mul h2 h3 hp0.le (Nat.cast_nonneg _)
        _ ≤ 2 * X.L.a := h1
    have hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) *
        X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc ∑ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ∑ _q : Fin (2 * X.s), 2 * (X.L.a : ℝ) := Finset.sum_le_sum fun q _ => hone q
        _ = (2 * X.s : ℕ) * (2 * X.L.a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p := by
      have h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast (by omega : 2 * X.s ≤ X.r)
      nlinarith
    have hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤
        2 * X.L.a := by
      have h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p := by nlinarith
      exact le_of_mul_le_mul_right (hsum.trans h1) hp0
    have hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤
        2 * X.L.a := by exact_mod_cast hsum2
    exact (Nat.add_le_add hsum3 hlast).trans (by omega)
  · exact_mod_cast hS.hF.a1

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LowerBoundInitialMultiplicity

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
