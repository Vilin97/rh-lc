module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRank

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool)

def twistedJump (y : ℤ) : ℤ :=
  if s then -(⌊P.e j⌋ + y + ((R.t : ℤ) + 1) / 2) else ⌊P.e j⌋ + y - ((R.t : ℤ) + 1) / 2

theorem twistedDualJumps_eq_hodgeTateJump_images : jT2 P j s =
    (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => twistedJump P j s ⌊P.v i⌋) +
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
  obtain ⟨q, hq⟩ := R.t_odd
  cases s <;>
    simp only [jT2, jW, cloud, lows, twistedJump, Multiset.map_add (f := _), Multiset.map_map,
      Function.comp_def, ↓reduceIte, Bool.false_eq_true] <;>
    congr 1 <;>
    refine Multiset.map_congr rfl fun i _ => ?_ <;>
    omega

theorem twistedJump_low_small (η : ℝ) (h : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) (i : Fin R.m) :
    |twistedJump P j s (-⌊P.b i⌋)| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  obtain ⟨zb, hzb⟩ := P.b_int i
  obtain ⟨ze, hze⟩ := P.e_int j
  obtain ⟨q, hq⟩ := R.t_odd
  have hb : ⌊P.b i⌋ = zb := by rw [hzb]; exact Int.floor_intCast zb
  have he : ⌊P.e j⌋ = ze := by rw [hze]; exact Int.floor_intCast ze
  have hr : (((zb - ze : ℤ) : ℝ)) = (((P.b i - P.e j : ℚ) : ℝ)) := by
    rw [hzb, hze]; push_cast; ring
  have hn : (zb - ze).natAbs ≤ ⌊η⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs, hr]
    exact h i
  have habs : |zb - ze| ≤ (⌊η⌋₊ : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  rw [abs_le] at habs ⊢
  unfold twistedJump
  rw [hb, he]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> constructor <;> omega

theorem twistedJump_cloud_large (n : ℕ) (hv : ∀ i, 0 ≤ P.v i) (h : (n : ℤ) < szT P j s)
    (i : Fin (R.k - 1)) : ¬ |twistedJump P j s ⌊P.v i⌋| ≤ (n : ℤ) := by
  obtain ⟨q, hq⟩ := R.t_odd
  have hV : 0 ≤ ⌊P.v i⌋ := Int.floor_nonneg.mpr (hv i)
  unfold twistedJump
  unfold szT at h
  rw [abs_le]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

end Count

theorem card_small_twistedDualJumps_eq_rank {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ)
    (hv : ∀ i, 0 ≤ P.v i) (hb : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η)
    (hs : ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s) :
    ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  rw [twistedDualJumps_eq_hodgeTateJump_images, Multiset.filter_add, Multiset.card_add]
  have hc : ((Finset.univ : Finset (Fin (R.k - 1))).val.map
      (fun i => twistedJump P j s ⌊P.v i⌋)).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_cloud_large P j s _ hv hs i
  have hl : ((Finset.univ : Finset (Fin R.m)).val.map
      (fun i => twistedJump P j s (-⌊P.b i⌋))).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) =
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
    rw [Multiset.filter_eq_self]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_low_small P j s η hb i
  rw [hc, hl]
  simp

end GlobalTheory.HTW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRankStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.card_filter_abs_le_jT2_eq_rank : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ), (∀ i, 0 ≤ P.v i) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s → ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  first | exact @GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | exact GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | (intros; apply GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCard

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem block_map_reflect (R : Ranks) :
    (block R).map (fun u => (R.t : ℤ) - 1 - u) = block R := by
  have hnd : (block R).Nodup := by
    unfold block
    exact (Multiset.nodup_range R.t).map (fun a b h => by exact_mod_cast h)
  have hmem : ∀ x : ℤ, x ∈ block R ↔ 0 ≤ x ∧ x < R.t := by
    intro x
    unfold block
    simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by positivity, by exact_mod_cast hc⟩
    · rintro ⟨h0, h1⟩
      exact ⟨x.toNat, by omega, by omega⟩
  refine (Multiset.Nodup.ext (hnd.map (fun a b h => by simpa using h)) hnd).2 ?_
  · intro x
    rw [Multiset.mem_map, hmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hmem] at hy
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨(R.t : ℤ) - 1 - x, by rw [hmem]; omega, by ring⟩

theorem jR_symm_card {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧
      (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hW : ∀ s, (jW P j s).card = R.r := by
    intro s
    have h : (cloud P j + lows P j).card = R.r := by
      simp only [Multiset.card_add, cloud, lows, Multiset.card_map, Finset.card_val,
        Finset.card_univ, Fintype.card_fin, Ranks.r]
      omega
    cases s
    · simp only [jW, Bool.false_eq_true, if_false, Multiset.card_map, h]
    · simp only [jW, if_true, h]
  refine ⟨?_, fun s => ?_⟩
  · simp only [jR, jW, if_true, Bool.false_eq_true, if_false, Multiset.map_add (f := _), block_map_reflect]
  · have hR : (jR P j s).card = R.nV := by
      simp only [jR, Multiset.card_add, hW s, block, Multiset.card_map, Multiset.card_range, Ranks.nV]
    refine ⟨hW s, hR, ?_, ?_⟩
    · simp only [jT2, Multiset.card_map, hW s]
    · unfold jT2 jT1 jR
      exact Multiset.map_le_map (Multiset.le_add_right _ _)

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCardStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cloudLowJumps_reflect_and_card : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m), jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧ (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  first | exact @GlobalTheory.HTW.jR_symm_card | exact GlobalTheory.HTW.jR_symm_card | (intros; apply GlobalTheory.HTW.jR_symm_card <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCard

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem twistedDualPageWord_small_jumps_card : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  intro D L C j ε τ φ hR
  have hbox := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2
  have hcount : ∀ i, (((pageWord L j ε τ φ).J2 i).filter
      fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
    intro i
    refine GlobalTheory.T.card_filter_abs_le_jT2_eq_rank (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.etaSz ?_ ?_ (hbox i)
    · intro a
      have h := (L.cloud_v (D.eTau.symm ⟨plc (letter τ φ i), plc_mem _⟩) a).1
      exact_mod_cast h
    · intro a
      exact L.be_close _ a j
  refine ⟨fun i => ⟨fun u hu => ?_, (hcount i).le⟩, fun i => ⟨?_, hcount i⟩⟩
  · exact Multiset.mem_of_le
      ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.2 hu
  · exact ((GlobalTheory.T.cloudLowJumps_reflect_and_card (hcAt D (letter τ φ i)) j).2 (pos ε (letter τ φ i))).2.2.1

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCardStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  first | exact @GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | exact GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | (intros; apply GlobalTheory.HTW.twistedDualPageWord_small_jumps_card <;> assumption)
end
end
