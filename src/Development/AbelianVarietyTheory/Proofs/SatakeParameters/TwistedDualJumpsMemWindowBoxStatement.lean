module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCardStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMH

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMHStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.jumps_mem_box_neg_M_h : ∀ {n : ℕ} (W : WordData n), (∀ i, 0 ≤ W.sz i) → W.T1 → ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  first | exact @GlobalTheory.HTW.WordData.jumps_mem_box | exact GlobalTheory.HTW.WordData.jumps_mem_box | (intros; apply GlobalTheory.HTW.WordData.jumps_mem_box <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindows

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem jT1_mem_window_of_bounded_v : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ),
    (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) →
    (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s,
    (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ)
      else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨
    |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  intro R P j s S η hv hb u hu
  obtain ⟨c, hc⟩ := R.t_odd
  have ht1 : ((R.t : ℤ) - 1) / 2 = c := by rw [hc]; push_cast; omega
  have ht2 : ((R.t : ℤ) + 1) / 2 = c + 1 := by rw [hc]; push_cast; omega
  have htc : (R.t : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨E, hE⟩ := P.e_int j
  have hEf : ⌊P.e j⌋ = E := by rw [hE]; simp
  have hV : ∀ i, 0 ≤ ⌊P.v i⌋ ∧ ⌊P.v i⌋ ≤ ((⌊S⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨V, hVi⟩ := P.v_int i
    obtain ⟨h0, h1⟩ := hv i
    rw [hVi] at h0 h1 ⊢
    simp only [Int.floor_intCast]
    push_cast at h0 h1
    have h0' : (0:ℤ) ≤ V := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have h2 : ((V.toNat : ℕ) : ℝ) ≤ S := by
      have : ((V.toNat : ℕ) : ℝ) = (V : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0'
      rw [this]; exact h1
    have := Nat.le_floor h2
    omega
  have hB : ∀ i, -((⌊η⌋₊ : ℕ) : ℤ) ≤ ⌊P.b i⌋ - E ∧ ⌊P.b i⌋ - E ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨B, hBi⟩ := P.b_int i
    have h1 := hb i
    rw [hBi, hE] at h1
    rw [hBi]
    simp only [Int.floor_intCast]
    have h2 : (((B - E).natAbs : ℕ) : ℝ) ≤ η := by
      rw [Nat.cast_natAbs]; push_cast at h1 ⊢; exact h1
    have h3 := Nat.le_floor h2
    have h4 : |B - E| ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    exact abs_le.mp h4
  simp only [jT1, jR, jW, cloud, lows, block, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
    Finset.mem_univ, true_and, Multiset.mem_range] at hu
  cases s with
  | true =>
    simp only [szT, if_true, Bool.not_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [if_true, Multiset.mem_map, Multiset.mem_add, Finset.mem_val, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, (hx | hx) | hx, rfl⟩ := hu
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hV i
      left; rw [hEf, ht1]; constructor <;> omega
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hB i
      right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega
  | false =>
    simp only [szT, Bool.not_false, if_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [Bool.false_eq_true, if_false, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
      Finset.mem_univ, true_and] at hu
    obtain ⟨x, hx | hx, rfl⟩ := hu
    · obtain ⟨y, hy | hy, rfl⟩ := hx
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hV i
        left; rw [hEf, ht1]; constructor <;> omega
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hB i
        right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowsStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualJumps_mem_windows : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ), (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s, (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ) else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨ |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.jT1_mem_window_of_bounded_v | exact GlobalTheory.jT1_mem_window_of_bounded_v | (intros; apply GlobalTheory.jT1_mem_window_of_bounded_v <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindows

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_T1_and_J1_mem_window_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  intro D L C j ε τ φ hR
  have hT : (pageWord L j ε τ φ).T1 := by
    intro i u hu
    exact GlobalTheory.T.twistedDualJumps_mem_windows (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.Sc L.etaSz
      (fun a => L.cloud_v _ a) (fun a => L.be_close _ a j) u hu
  refine ⟨hT, GlobalTheory.T.jumps_mem_box_neg_M_h _ (fun i => ?_) hT⟩
  have h := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2 i
  exact le_trans (Int.natCast_nonneg _) h.le

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindowsStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_jumps_in_windows : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  first | exact @GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | exact GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | (intros; apply GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBox

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem sum_count_Icc (s : Multiset ℤ) (η : ℕ) :
    ∑ u ∈ Finset.Icc (-(η : ℤ)) η, ((s.count u : ℕ) : ℤ) =
      ((s.filter fun u : ℤ => |u| ≤ (η : ℤ)).card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    by_cases hx : |x| ≤ (η : ℤ)
    · have hm : x ∈ Finset.Icc (-(η : ℤ)) η := Finset.mem_Icc.2 (abs_le.1 hx)
      rw [Multiset.filter_cons_of_pos (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, Multiset.card_cons, ← Finset.add_sum_erase _ _ hm,
        Multiset.count_cons_self]
      have he : ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u (x ::ₘ s) : ℕ) : ℤ) =
          ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u s : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun u hu => by
          rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hu)]
      rw [he]
      push_cast
      rw [← ih, ← Finset.add_sum_erase _ _ hm]
      ring
    · have hm : x ∉ Finset.Icc (-(η : ℤ)) η := fun h => hx (abs_le.2 (Finset.mem_Icc.1 h))
      rw [Multiset.filter_cons_of_neg (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, ← ih]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Multiset.count_cons_of_ne (fun h => hm (by rw [← h]; exact hu))]

theorem letter_one_zero {φ : Formalism.HC.Frame} (τ : φ.GG) : letter τ 1 (0 : ZMod (orderOf (1 : φ.GG))) = τ := by
  simp [letter]

theorem recWord_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  intro D L C j ε n g hR a
  obtain ⟨hT1, hbox⟩ := GlobalTheory.T.twistedDualPageWord_jumps_in_windows L C j ε (g a) 1 hR
  obtain ⟨hT2, hcard⟩ := GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy L C j ε (g a) 1 hR
  obtain ⟨hsz, hMi, hhi, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g a) 1 hR 0
  have hl := letter_one_zero (g a)
  have t1 := hT1 0
  have t2 := hT2 0
  have bx := hbox 0
  have cd := (hcard 0).2
  simp only [pageWord, recWord, WordData.Mi, WordData.hi, hl] at t1 t2 bx cd hsz hMi hhi
  refine ⟨fun u hu => ?_, fun u hu => (t2.1 u hu), ?_⟩
  · have h1 := t1 u hu
    have h2 := bx u hu
    refine ⟨?_, ?_⟩
    · simp only [NWord.win, recWord, Set.mem_setOf_eq]
      rw [hsz]
      exact h1
    · simp only [recWord, Set.mem_Icc]
      rw [hMi, hhi]
      exact h2
  · rw [sum_count_Icc, cd]

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBoxStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualJumps_mem_window_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  first | exact @GlobalTheory.HTW.Rec.recWord_jumps | exact GlobalTheory.HTW.Rec.recWord_jumps | (intros; apply GlobalTheory.HTW.Rec.recWord_jumps <;> assumption)
end
end
