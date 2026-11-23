module

public import Formalism.FormalDegreeBessel.StatementG
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.HermitianCurvature.StatementI
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitFam

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def fam (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ :=
  fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then e ⟨i.val - r, by omega⟩ else bvec i

def ONb (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a, inWb k r (e a)) ∧
    ∀ a b, herm (Hpk k r) (e a) (e b) = if a = b then (if a.val = k then -1 else 1) else 0

theorem hpk_out_in {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    Hpk k r i j = 0 ∧ Hpk k r j i = 0 := by
  constructor <;> simp only [Hpk] <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_bvec (i j : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec i) (bvec j) = Hpk k r j i := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

theorem herm_bvec_w {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) (bvec i) w = 0 := by
  have hc : ∀ l, (Hpk k r *ᵥ bvec i) l = Hpk k r l i := fun l => by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [herm, dotProduct, hc]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).2, mul_zero]
  · rw [Pi.star_apply, hw l (by omega), star_zero, zero_mul]

theorem herm_w_bvec {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) w (bvec i) = 0 := by
  have hc : herm (Hpk k r) w (bvec i) = (Hpk k r *ᵥ w) i := by
    simp [herm, bvec, dotProduct, Pi.single_apply]
  rw [hc]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).1, zero_mul]
  · rw [hw l (by omega), mul_zero]

theorem fam_in {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) :
    fam k r e i = e ⟨i.val - r, by omega⟩ := by
  simp only [fam]
  rw [dite_eq_left h]

theorem fam_out {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    fam k r e i = bvec i := by
  simp only [fam]
  rw [dite_eq_right]
  omega

theorem famGram {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} (he : ONb k r e) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fam k r e i) (fam k r e j) = Hpk k r j i := by
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · rw [fam_in hi, fam_in hj, he.2]
    simp only [Hpk]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)
  · rw [fam_in hi, fam_out (i := j) (by omega), herm_w_bvec (i := j) (by omega) (he.1 _),
      (hpk_out_in (i := j) (j := i) (by omega) hi).1]
  · rw [fam_out (i := i) (by omega), fam_in hj, herm_bvec_w (i := i) (by omega) (he.1 _),
      (hpk_out_in (i := i) (j := j) (by omega) hj).2]
  · rw [fam_out (i := i) (by omega), fam_out (i := j) (by omega), herm_bvec_bvec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitPt

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def mk3 (k : ℕ) {n : ℕ} (v0 : Fin n → ℂ) (F : Fin (k - 1) → Fin n → ℂ) (zz : Fin n → ℂ) : Fin (k + 1) → Fin n → ℂ :=
  fun a => if h0 : a.val = 0 then v0 else if hk : a.val = k then zz else F ⟨a.val - 1, by have := a.isLt; omega⟩

theorem three_part_frame_zero {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h : a.val = 0) :
    mk3 k v0 F zz a = v0 := by
  unfold mk3; rw [dite_eq_left h]

theorem three_part_frame_last {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} (hk : 1 ≤ k) {a : Fin (k + 1)}
    (h : a.val = k) : mk3 k v0 F zz a = zz := by
  unfold mk3; rw [dite_eq_right (by omega), dite_eq_left h]

theorem three_part_frame_middle {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h0 : a.val ≠ 0)
    (hk : a.val ≠ k) : mk3 k v0 F zz a = F ⟨a.val - 1, by have := a.isLt; omega⟩ := by
  unfold mk3; rw [dite_eq_right h0, dite_eq_right hk]

theorem three_part_frame_orthonormal (hk : 2 ≤ k) {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hv0 : inWb k r v0) (hzz : inWb k r zz) (hF : ∀ j, inWb k r (F j))
    (h00 : herm (Hpk k r) v0 v0 = 1) (hzz1 : herm (Hpk k r) zz zz = -1) (h0z : herm (Hpk k r) v0 zz = 0)
    (hF0 : ∀ j, herm (Hpk k r) (F j) v0 = 0) (hFz : ∀ j, herm (Hpk k r) (F j) zz = 0)
    (hFF : ∀ i j, herm (Hpk k r) (F i) (F j) = if i = j then 1 else 0) : ONb k r (mk3 k v0 F zz) := by
  have hz0 : herm (Hpk k r) zz v0 = 0 := by rw [DU.hswap, h0z, map_zero]
  have h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0 := fun j => by rw [DU.hswap, hF0 j, map_zero]
  have hzF : ∀ j, herm (Hpk k r) zz (F j) = 0 := fun j => by rw [DU.hswap, hFz j, map_zero]
  constructor
  · intro a
    by_cases h0 : a.val = 0
    · rw [three_part_frame_zero h0]; exact hv0
    · by_cases hl : a.val = k
      · rw [three_part_frame_last (by omega) hl]; exact hzz
      · rw [three_part_frame_middle h0 hl]; exact hF _
  · intro a b
    by_cases ha0 : a.val = 0
    · rw [three_part_frame_zero ha0]
      by_cases hb0 : b.val = 0
      · rw [three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]
      · rw [if_neg (fun h => hb0 (by rw [← h]; exact ha0))]
        by_cases hbl : b.val = k
        · rw [three_part_frame_last (by omega) hbl, h0z]
        · rw [three_part_frame_middle hb0 hbl, h0F]
    · by_cases hal : a.val = k
      · rw [three_part_frame_last (by omega) hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]
          · rw [three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]
      · rw [three_part_frame_middle ha0 hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]
          · rw [three_part_frame_middle hb0 hbl, hFF]
            by_cases hab : a = b
            · subst hab; rw [if_pos rfl, if_pos rfl, if_neg hal]
            · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
              rw [if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem pt_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (SSn.nu0 k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) z = 0 ∧
    herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
    inWb k r (SSn.nu0' k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) z' = 0 ∧
    herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨h1, h2, h3, h4⟩ := DU.base hz hz' hT hT' hsec hζ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hνW : inWb k r (SSn.nu0 k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _
  refine ⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩
  · rw [← h1]; exact DU.prWv_perp hT hνW
  · rw [← h3]; exact DU.prWv_perp hT' hνW'

theorem mu_frame (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) :
    (∀ j, inWb k r (NF.muZ k r μsec ζ *ᵥ Fr j)) ∧
    (∀ i j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr i) (NF.muZ k r μsec ζ *ᵥ Fr j) = if i = j then 1 else 0) ∧
    (∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) z = 0) ∧
    ∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) (SSn.nu0 k r z z' μsec ζ) = 0 := by
  obtain ⟨-, -, hνν, -, -, -, hν'ν', -⟩ := pt_facts hz hz' hT hT' hsec hζ
  set μ := NF.muZ k r μsec ζ with hμ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hU : μ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (μ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r (μ⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0 := fun j => hFr.2.2 j z' (by simp)
  have hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 := fun j => hFr.2.2 j _ (by simp)

  have hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0 := by
    intro j
    rw [FrameEntries.herm_inv hU]
    set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ)
      with ht
    have hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z) := rfl
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hν', h0, zero_smul] at hν'ν'
      simp [herm] at hν'ν'
    have h1 := hFν' j
    rw [hν', DU.hsmul_r] at h1
    have h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0
      · exact h
    rw [DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero] at h2
    exact h2
  refine ⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩
  intro j
  set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)
  have hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z') := rfl
  rw [hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]
  simp

theorem frame'_exists (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr := by
  obtain ⟨-, -, -, -, hW', hz'0, h11, -⟩ := pt_facts hz hz' hT hT' hsec hζ
  exact Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11

end pt

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end
end
