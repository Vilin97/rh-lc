module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window
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
public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore
public import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
public import Formalism.SizeWindowBrackets.SChain
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq
public import Development.AutomorphicArithmetic.PrimitiveCosets.SigALe
public import Development.AutomorphicArithmetic.PrimitiveCosets.charsA
public import Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Mathlib.Algebra.Order.Star.Real
public import Formalism.SharpRestriction.GlobalSchurBounds.TieGlobal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

-- Source module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

theorem windows_iff {eps : ℝ} (Fm : FamCore eps) (la : ℝ) : Fm.Windows la ↔ HasWindows Fm.Win la := Iff.rfl

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

def ChebyshevInequalityOnFamilyWindows {eps : ℝ} (Fm : Fam eps) (eD eL : ℝ) : Prop :=
  ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ (core Fm).Win → Tied Fm eD eL K cHH eK CL x

def ChebyshevInequalityOnWindows (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) → ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL →
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ (core Fm).Win → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityAtWindowScale (la : ℝ) (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    (core Fm).Windows la ∧ ChebyshevInequalityOnFamilyWindows @core @Tied Fm eD eL

variable {TransportedAlt : Type} (P : ∀ {eps : ℝ}, Fam eps → TransportedAlt → Prop) (HypV : ∀ {eps : ℝ}, FamCore eps → Prop)

variable {core Tied P HypV}

theorem exists_small_eps (C : ℝ) {δ ε₁ : ℝ} (hδ : 0 < δ) (h1 : 0 < ε₁) : ∃ ε : ℝ, 0 < ε ∧ ε < ε₁ ∧ C * ε ≤ δ := by
  have hp : 0 < |C| + 1 := by positivity
  have h0 : 0 < min (ε₁ / 2) (δ / (|C| + 1)) := lt_min (by linarith) (div_pos hδ hp)
  refine ⟨_, h0, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) h0.le
  have a2 : min (ε₁ / 2) (δ / (|C| + 1)) ≤ δ / (|C| + 1) := min_le_right _ _
  rw [le_div_iff₀ hp] at a2
  nlinarith

theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ) (hB : Λ.FormBAt la)
    (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel := by
  obtain ⟨eD, eL, ε₁, h1, h⟩ := h
  intro ψ hψ s hs
  have hm1 : min (s.re - 1 / 2) (1 / 2) ≤ s.re - 1 / 2 := min_le_left _ _
  have hm2 : min (s.re - 1 / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hm0 : 0 < min (s.re - 1 / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨ε, hε0, hεlt, hCe⟩ := exists_small_eps (eD + eL + 7) (half_pos hm0) h1
  obtain ⟨Fm, hE, hW, hT⟩ := h ε hε0 hεlt
  obtain ⟨x1, hx⟩ := h112 eD eL ε hε0 Fm hE hT
  refine hB (1 / 2 + min (s.re - 1 / 2) (1 / 2) / 2) (by linarith) (by linarith)
    (((windows_iff _ la).1 hW).mono (x0 := max x1 1) fun y hy hw => ?_) ψ hψ s (by linarith)
  exact (hx y (le_of_max_le_left hy) hw).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith))

theorem zeroFreeOn_of_tiedWin {Q : PChar → Prop}
    (h : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧ ChebyshevInequalityOnWindows @core @Tied Λ ∧ Λ.FormB ∧
      ChebyshevInequalityAtWindowScale @core @Tied la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => by
    obtain ⟨Λ, la, a, b, c, d, e⟩ := h ψ hψ
    exact ⟨Λ, a, level_of_tiedWin c (d la b) e⟩

theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
    (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ)) (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
    (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q :=
  zeroFreeOn_of_tiedWin fun ψ hψ => ⟨_, la, Level.mem_cyc ψ, hla, h112 ψ hψ, hB ψ hψ, h ψ hψ⟩

end

end Formalism.HC

end
end
end

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop

section

@[expose] public section

open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

lemma ch_top_main_eq {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (hId : IdentU Dd tr D N ell TT a w eT eP) (u0 : U0) :
    Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w (tr u0) j)).re := by
  obtain ⟨ha, hw, hg, hL, -⟩ := hId
  have hf : (f : ℝ) = (#(PhiSet (H := H)) : ℝ) := by
    have := Fintype.card_congr eP
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    exact_mod_cast this
  have hsum : ∀ g : E0 × H → ℝ, ∑ ρ : Fin f, g (eP ρ) = ∑ x ∈ PhiSet, g x := by
    intro g
    rw [← Finset.sum_coe_sort PhiSet]
    exact Equiv.sum_comp eP (fun x => g x)
  unfold Data.Main
  simp only [ha, hw, hg, hL, hsum, hf]
  rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort TT]
  rw [← Equiv.sum_comp eT]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  simp [MAIN, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  left
  left
  exact hsum (fun x => Real.log (w (tr u0) j x))

theorem ch_top {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (h1 : IdentU Dd tr D N ell TT a w eT eP) (h2 : SizeData₂ Dd C Xpp) (h3 : ErrWindows Dd C Xpp eK K) (h4 : BNBoundsU Dd T2)
    (h5 : LargeX Dd.x Dd.ε K C.cHH eK) (u : U0) :
    gapA D N ell TT a w (tr u) ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
  have hmain := ch_top_main_eq Dd tr D N ell TT a w eT eP h1 u
  have hask := h1.2.2.2.2 u
  have hgap : gapA D N ell TT a w (tr u) = Dd.ASK u - Dd.Main u := by
    rw [hask, hmain]
    unfold gapA
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := h2
  have hle := each_unit_bound_statement Dd C Xpp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u
  have herr : ErrX5at Dd C Xpp u ≤ Dd.x ^ (CErr C * Dd.ε) * ErrText Dd := by
    obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
      hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := h3
    obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
    obtain ⟨hlog, hbig⟩ := h5
    have hx0 : 0 < Dd.x := by linarith only [hx]
    have hy : 1 ≤ Dd.x ^ Dd.ε := Real.one_le_rpow hx hε.le
    have hyD : 1 ≤ Dd.x ^ (C.eDiv * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
    have hyL : 1 ≤ Dd.x ^ (C.eLoss * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
    have hb0 : 0 ≤ Dd.b := by linarith only [hb]
    have hbxb : Dd.b ≤ Dd.x * Dd.b := le_mul_of_one_le_left hb0 hx
    have hba : Dd.b ≤ Dd.a := hbxb.trans hxb
    have ha1 : 1 ≤ Dd.a := hb.trans hba
    have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hk : 0 < Dd.k := by linarith only [hk1]
    have hmx : (m : ℝ) ≤ Dd.x := by
      refine hm.trans ?_
      calc Dd.x ^ ((1 : ℝ) / 2 + Dd.ε / 2) ≤ Dd.x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
        _ = Dd.x := Real.rpow_one _
    have hMk : (m : ℝ) ≤ Dd.k := (le_mul_of_one_le_left hM hx).trans hxm
    have hMb : (m : ℝ) * Dd.b ≤ Dd.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
    have hsA0 : 0 ≤ Dd.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
    have hsA : Dd.sumA ≤ 2 * (Dd.nT * Dd.a) := by
      unfold Data.sumA Data.nT
      calc ∑ t, Dd.aT t ≤ ∑ _t : Top, 2 * Dd.a := Finset.sum_le_sum (fun t _ => (haT t).2)
        _ = 2 * ((Fintype.card Top : ℝ) * Dd.a) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have hlWk : Real.log (Fintype.card (W u) : ℝ) ≤ Dd.a :=
      ((hlW u).trans (sub_three_mul_log_two_le hk.le)).trans hka
    have hlk0 : 0 ≤ Real.log Dd.k := Real.log_nonneg hk1
    have hlk : Real.log Dd.k ≤ (1 + eK) * Dd.x ^ Dd.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
    have hxH : 1 ≤ Dd.x ^ C.cHH := Real.one_le_rpow hx hHH
    have hlH0 : 0 ≤ Real.log (1 + Dd.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
    have hlH : Real.log (1 + Dd.x ^ C.cHH) ≤ (1 + C.cHH) * Dd.x ^ Dd.ε :=
      log_one_add_rpow_le hx hHH hlog hy
    obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
    have hpow : Dd.x ^ (CErr C * Dd.ε)
        = Dd.x ^ (C.eDiv * Dd.ε) * Dd.x ^ (C.eLoss * Dd.ε) * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      unfold CErr
      ring
    rw [hpow]
    unfold KBig at hbig
    have := core_ineq (nT := Dd.nT) (a := Dd.a) (b := Dd.b) (b' := Dd.b') (k := Dd.k) (L := Dd.L) (La := Dd.La)
      (B0 := Dd.B0) (Nc := Dd.Nc) (M := (m : ℝ)) (sA := Dd.sumA)
      (lW := Real.log (Fintype.card (W u) : ℝ)) (lk := Real.log Dd.k)
      (lH := Real.log (1 + Dd.x ^ C.cHH)) (dI := (1 - Dd.delBar)⁻¹)
      (et := (Dd.etaBar + 4 * Real.sqrt Dd.eBar) * (Dd.x ^ C.cHH * Dd.b)) (Xpp := Xpp)
      (y := Dd.x ^ Dd.ε) (yD := Dd.x ^ (C.eDiv * Dd.ε)) (yL := Dd.x ^ (C.eLoss * Dd.ε)) (K := K)
      (h := 1 + C.cHH) (g := 1 + eK)
      hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
      hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
      (by linarith only [hHH]) (by linarith only [heK]) hbig
    unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
    exact this
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    have := Fintype.card_congr eT
    rw [Fintype.card_coe] at this
    exact_mod_cast this
  have htext : ErrText Dd ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    gcongr
    · exact h4.1
    · exact h4.2
  have hpow : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg s1.1.le _
  rw [hgap]
  calc Dd.ASK u - Dd.Main u ≤ _ := by linarith
    _ ≤ _ := herr
    _ ≤ _ := mul_le_mul_of_nonneg_left htext hpow

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm

section

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
  intro Λ eD eL K cHH eK C eps heps
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hc : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₁, hx₁⟩ := Deduction.ch_core (max (eD + eL) 0 + 3) eps C (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ))
    (by positivity) heps hc
  obtain ⟨x₂, hx₂⟩ := large_x_eventually eps K cHH eK heps
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop heps).eventually_ge_atTop (1 + 4 * (Λ.o : ℝ)))
  refine ⟨max x₁ (max x₂ x₃), fun x hx φ H TT hE hCore => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨U0, i0, tr, W, i4, i5, Top, i6, m, f, Dd, Cc, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ,
    hell, hxx, hε, heD, heL, hcHH, hcov, hId, hLed, hWin, hBN, hSz, hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx hε
  have hLX := hx₂ _ g2
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  have hLX' : LargeX Dd.x Dd.ε K Cc.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := le_trans (by positivity) w5
  have hE0 : 0 ≤ eD + eL := by linarith
  rw [max_eq_left hE0] at hx₁
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr Cc * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hmain := hx₁ _ g1 φ.A m (arith H.toHostRaw) _ ell N TT T2 a w Dd.b Dd.b' Dd.k Dd.a η X' θ φ.A0
    (keptA Λ H.toHostRaw) (hostFactsS φ H) hb ha hk w7 w8 hSz hThin hCost hRest hT2
    (charsA Λ φ H TT _ _ C ell hx0 hE hell) (fun u hu => by
      obtain ⟨v, rfl⟩ := hcov u hu
      exact le_trans (Deduction.ch_top Dd tr Cc Xpp eK K _ ell N TT T2 a w eT eP hId hLed hWin hBN hLX' v)
        (mul_le_mul_of_nonneg_right hExp hBr))
  rw [gmA_eq Λ φ H TT _ _ C ell hE hell] at hmain
  have hs := sigA_le Λ φ H TT _ _ C ell hx0 hE hell
  have h1 : Dd.x ^ ((1 : ℝ) / 2 + Dd.ε) ≤ Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) :=
    Real.rpow_le_rpow_of_exponent_le w1 (by nlinarith)
  have h2 : Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * Dd.ε)
      = Dd.x ^ Dd.ε * Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h3 := mul_le_mul_of_nonneg_right (hx₃ _ g3)
    (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε))
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * (Λ.o : ℝ) by positivity)
  rw [h2]
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.WindowInequalityOfArtinInputs

section

@[expose] public section

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

def FamCoreConstantBounds {eps : ℝ} (Fm : FamCore eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ i : Fm.Ix x, CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x

variable {Fam : ℝ → Type 1} {core : ∀ {eps : ℝ}, Fam eps → FamCore eps}
  {Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop}

theorem windowInequality_of_artinInputs
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (Λ : Level) : ChebyshevInequalityOnWindows @core @Tied Λ := by
  rintro eD eL eps he Fm ⟨C, xE, hE⟩ ⟨K, cHH, eK, CL, x0, hT⟩
  obtain ⟨x1, hx1⟩ := core_gm Λ eD eL K cHH eK C eps he
  refine ⟨max x1 (max x0 xE), fun x hx hw => ?_⟩
  have b := le_of_max_le_right hx
  obtain ⟨i, hi⟩ := h Fm _ _ _ _ _ _ _ (hT x (le_of_max_le_left b) hw)
  exact hx1 x (le_of_max_le_left hx) _ ((core Fm).D x i).host.toHostAx _ (hE x (le_of_max_le_right b) i) hi

end UpperTheory.Comparison₂

end
end
end

-- Source module: Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

section

@[expose] public section

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

theorem tiedCore_of_chainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) (h : ChainTied Fm eD eL K cHH eK CL x) :
    FamCoreConstantBounds Fm.toFamCore eD eL K cHH eK x := by
  obtain ⟨i0, m, f, pt, av, bv, Top, iT, Dd, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    -, -, -, ⟨tT, t2, -, -, hell⟩, h1, h2, h3, h4, h5, h7, h8, h9, h10, ⟨⟨s1, s2, s3, s4, s5, s6, ⟨n1, n2, n3⟩, s8⟩, th, -⟩, h12, h13⟩ := h
  have hTT : TT = (Fm.D x i0).host.TT := by
    ext t
    rw [tT t, ← Fm.TT_eq x i0, Finset.mem_image]
    exact ⟨fun ⟨s, hs, e⟩ => (Frame.A.val_injective _ e) ▸ hs, fun ht => ⟨t, ht, rfl⟩⟩
  subst hTT
  refine ⟨i0, _, inferInstance, id, fun u0 => (Fm.D x (pt u0)).what₂.Word, fun _ => inferInstance, fun _ => inferInstance, Top, iT,
    m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ, hell, h1, h2, h3, h4, h5, fun s _ => ⟨s, rfl⟩, h7, h8, h9, h10,
    ⟨s1, s2, s3, s4, s5, s6, fun u _ => n1 u, fun u _ => n2 u, fun u _ => n3 u, fun u _ => s8 u⟩, th, h12, h13, fun s hs => ?_⟩
  obtain ⟨k, -, rfl⟩ := (t2 0 s).1 hs
  exact Frame.digit_mem_cyclic_subgroup _ k

theorem level_gm_le_on_family_scales (Λ : Level) :
    ChebyshevInequalityOnWindows (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) Λ :=
  windowInequality_of_artinInputs (fun Fm => tiedCore_of_chainTied Fm) Λ

end UpperTheory.Comparison₂

end
end
end
