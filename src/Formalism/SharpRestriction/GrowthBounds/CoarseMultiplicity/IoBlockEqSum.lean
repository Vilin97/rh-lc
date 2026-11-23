module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ExpFactIoExp
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne

-- Source module: Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Imports

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def ωoL (l0 : Fin (X.seg C0 CE1 CE2 j).t) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if (a : ℕ) = 2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ) then 1 else 0

def ωo (l0 : Fin (X.seg C0 CE1 CE2 j).t) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωoL C0 CE1 CE2 X j l0 a
  | Sum.inr (l, β) => if (l : ℕ) = (l0 : ℕ) ∧ β = true then 1 else 0

def ωpL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => if (a : ℕ) = 2 * segS X.TT j then 1 else 0

def ωp : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωpL X j a
  | Sum.inr (l, β) => if (l : ℕ) = (X.seg C0 CE1 CE2 j).t ∧ β = true then 1 else 0

theorem ωo_bal (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    Balanced X.m (X.seg C0 CE1 CE2 j) (ωo C0 CE1 CE2 X j l0) (ωoL C0 CE1 CE2 X j l0) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have hu : ∀ l' : Fin (X.seg C0 CE1 CE2 j).t, ((uTop (X.seg C0 CE1 CE2 j) l' : Fin _) : ℕ) =
        (X.seg C0 CE1 CE2 j).sigma + l' := fun _ => rfl
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωo, ωoL, v0, v1, Fin.val_castSucc]
    by_cases hl : (l : ℕ) = (l0 : ℕ)
    · rw [if_neg (by simp), if_pos (by simp [hl]), if_pos (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
    · rw [if_neg (by simp), if_neg (by simp [hl]), if_neg (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
    simp only [ωo, ωoL, Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by simp), if_neg (by intro h; have := l0.2; omega), if_neg (by omega), if_neg (by omega)]

theorem ωp_bal : Balanced X.m (X.seg C0 CE1 CE2 j) (ωp C0 CE1 CE2 X j) (ωpL X j) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωp, ωpL, v0, v1, Fin.val_castSucc]
    rw [if_neg (by simp), if_neg (by intro h; have := l.2; omega), if_neg (by omega), if_neg (by omega)]
  · simp only [ωp, ωpL, Fin.val_castSucc, Fin.val_last]
    simp

theorem omB_ωo (b : SegBlock (segS X.TT j) X.m) (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωo C0 CE1 CE2 X j l0)
      (ωoL C0 CE1 CE2 X j l0) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
  classical
  have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωo]
  have s2 : ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.last _, false)) = 0 := by simp [ωo]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωoL C0 CE1 CE2 X j l0 (Fin.castSucc a) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
    rw [Finset.sum_eq_single (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ), by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωoL, Fin.val_castSucc, if_true, mul_one]
      rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ (uTop (X.seg C0 CE1 CE2 j) l0) rfl,
        if_neg (by show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma); omega)]
    · intro a _ ha
      simp only [ωoL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωoL C0 CE1 CE2 X j l0 (Fin.last _) = 0 := by
    simp only [ωoL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

theorem omB_ωp (b : SegBlock (segS X.TT j) X.m) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωp C0 CE1 CE2 X j) (ωpL X j) = b.oPlus := by
  classical
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωp C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωp]
  have s2 : ωp C0 CE1 CE2 X j (Sum.inr (Fin.last _, false)) = 0 := by simp [ωp]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωpL X j (Fin.castSucc a) = b.oPlus := by
    rw [Finset.sum_eq_single (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωpL, Fin.val_castSucc, if_true, mul_one]
      exact chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl
    · intro a _ ha
      simp only [ωpL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωpL X j (Fin.last _) = 0 := by
    simp only [ωpL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LevOfSymVar

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem lev_of_symVar (v : BV C0 CE1 CE2 X j) (i : Fin (segS X.TT j)) (h : (symVar C0 CE1 CE2 X j v).1.1 = topOdd X j i) :
    symLev X.p C0 CE1 CE2 X j v = (X.seg C0 CE1 CE2 j).P X.p i := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · by_cases ha : (a : ℕ) < 2 * segS X.TT j
    · simp only [symVar, symLev, dif_pos ha] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg ha] at h
      exact absurd h.symm (topOdd_ne_end X j i)
  · by_cases hl : (l : ℕ) < (X.seg C0 CE1 CE2 j).t
    · simp only [symVar, symLev, dif_pos hl] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg hl] at h
      exact absurd h.symm (topOdd_ne_end X j i)

theorem coarse_dvd (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    (X.seg C0 CE1 CE2 j).P X.p i ∣
      (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) ((topOdd X j i, β), c) := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.dvd_sum fun v _ => ?_
  show _ ∣ (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), c)
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [lev_of_symVar C0 CE1 CE2 X j v i (by rw [h])]
    exact dvd_mul_right _ _
  · exact dvd_zero _

theorem coarse_spec (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool)
    (hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      ((topOdd X j i, β), 0) = 0 := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  show (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), 0) = 0
  rw [Finsupp.single_apply, if_neg]
  intro h
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · simp only [symVar] at h
    split_ifs at h <;> exact Fin.succ_ne_zero _ (congrArg Prod.snd h)
  · simp only [symVar] at h
    split_ifs at h with hl
    · have e := topOdd_inj X j (congrArg (fun z => z.1.1) h)
      have : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (i : ℕ) := congrArg Fin.val e
      omega
    · exact topOdd_ne_end X j i (congrArg (fun z => z.1.1) h).symm

theorem ioExp_mod (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    ioExp C0 CE1 CE2 X j b μ ((topOdd X j i, β), c) % (X.seg C0 CE1 CE2 j).P X.p i =
      if β then b.rz i c else b.ry i c := by
  unfold ioExp
  rw [Finsupp.add_apply, baseExp_odd]
  obtain ⟨k, hk⟩ := coarse_dvd C0 CE1 CE2 X j μ i β c
  rw [hk]
  have hlt : (if β then b.rz i c else b.ry i c) < (X.seg C0 CE1 CE2 j).P X.p i := by
    split_ifs
    · exact (hb.1.1 i c).1
    · exact (hb.1.1 i c).2
  set P := (X.seg C0 CE1 CE2 j).P X.p i
  have e1 : ∀ (cond : Prop) [Decidable cond] (T : ℕ), (if cond then P * T else 0) = P * (if cond then T else 0) := by
    intro cond _ T
    split_ifs <;> simp
  rw [e1, add_assoc, ← mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockEqSum

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem hom_of_ssz {O : Type} [CommRing O] [IsDomain O] (b : SegBlock (segS X.TT j) X.m) (mm : ℝ)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (hu : u ∈ sszB O C0 CE1 CE2 X j mm b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : μ ∈ u.support) : HomExp C0 CE1 CE2 X j b μ := by
  intro ω ωL hB
  obtain ⟨h1, h2, h3⟩ := hB
  have hw := ssz_wh O X.p _ _ _ mm b ω ωL h1 h2 h3 u hu (mem_support_iff.1 hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω i) (fun _ => zero_smul _ _)] at hw
  simpa [smul_eq_mul] using hw

theorem sep (hp : 0 < X.p) (b b' : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (hb' : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b') (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : HomExp C0 CE1 CE2 X j b μ) (hμ' : HomExp C0 CE1 CE2 X j b' μ')
    (he : ioExp C0 CE1 CE2 X j b μ = ioExp C0 CE1 CE2 X j b' μ') : b = b' := by
  classical
  have hrz : ∀ i c, b.rz i c = b'.rz i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i true c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i true c
    rw [he, if_pos rfl] at h1
    rw [if_pos rfl] at h2
    exact h1.symm.trans h2
  have hry : ∀ i c, b.ry i c = b'.ry i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i false c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i false c
    rw [he, if_neg Bool.false_ne_true] at h1
    rw [if_neg Bool.false_ne_true] at h2
    exact h1.symm.trans h2
  have hrz' : b.rz = b'.rz := funext fun i => funext fun c => hrz i c
  have hry' : b.ry = b'.ry := funext fun i => funext fun c => hry i c
  have hA : ∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) b i = coarseA X.p (X.seg C0 CE1 CE2 j) b' i := by
    intro i; unfold coarseA; rw [hrz']
  have hC : ∀ i, coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
      coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i := by
    intro i; unfold coarseC; rw [hry']
  have hS : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → b.w i = b'.w i ∧ b.sg i = b'.sg i := by
    intro i hi
    have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := pow_pos hp _
    have k1 := hb.2.2.1 i hi
    have k1' := hb'.2.2.1 i hi
    have v1 := congrArg (fun e => e ((topOdd X j i, true), (0 : Fin (X.m + 1)))) he
    have v2 := congrArg (fun e => e ((topOdd X j i, false), (0 : Fin (X.m + 1)))) he
    simp only [ioExp, Finsupp.add_apply] at v1 v2
    rw [coarse_spec C0 CE1 CE2 X j μ i true hi, coarse_spec C0 CE1 CE2 X j μ' i true hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_pos rfl, if_pos rfl, if_pos (⟨hi, rfl⟩ : _ ∧ _), if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos rfl, if_pos rfl, hrz i 0, hA i] at v1
    rw [coarse_spec C0 CE1 CE2 X j μ i false hi, coarse_spec C0 CE1 CE2 X j μ' i false hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos (⟨hi, rfl⟩ : _ ∧ _), if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hry i 0] at v2
    have w1 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v1)
    have w2 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v2)
    have a1 := k1.2.1
    have a2 := k1'.2.1
    rw [hA i] at a1
    exact ⟨by omega, w2⟩
  have hbase : baseExp C0 CE1 CE2 X j b = baseExp C0 CE1 CE2 X j b' := by
    unfold baseExp
    rw [hrz', hry']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(hS i hi).1, (hS i hi).2, hA i]
    · rfl
  have hμμ : μ = μ' := by
    unfold ioExp at he
    rw [hbase] at he
    have h' := add_left_cancel he
    ext v0
    have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
    rw [coarse_eval, coarse_eval] at this
    exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this
  subst hμμ
  have ho : ∀ l, b.o (uTop (X.seg C0 CE1 CE2 j) l) = b'.o (uTop (X.seg C0 CE1 CE2 j) l) := by
    intro l
    rw [← omB_ωo C0 CE1 CE2 X j b l, ← omB_ωo C0 CE1 CE2 X j b' l, ← hμ _ _ (ωo_bal C0 CE1 CE2 X j l),
      ← hμ' _ _ (ωo_bal C0 CE1 CE2 X j l)]
  have hoP : b.oPlus = b'.oPlus := by
    rw [← omB_ωp C0 CE1 CE2 X j b, ← omB_ωp C0 CE1 CE2 X j b', ← hμ _ _ (ωp_bal C0 CE1 CE2 X j),
      ← hμ' _ _ (ωp_bal C0 CE1 CE2 X j)]
  have hofun : b.o = b'.o := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [(hb.2.2.1 i hi).1, (hb'.2.2.1 i hi).1]
    · have hl : (i : ℕ) - (X.seg C0 CE1 CE2 j).sigma < (X.seg C0 CE1 CE2 j).t := by
        have := i.2; unfold SegData.t; omega
      have e : uTop (X.seg C0 CE1 CE2 j) ⟨(i : ℕ) - (X.seg C0 CE1 CE2 j).sigma, hl⟩ = i :=
        Fin.ext (by show (X.seg C0 CE1 CE2 j).sigma + ((i : ℕ) - (X.seg C0 CE1 CE2 j).sigma) = i; omega)
      rw [← e]
      exact ho _
  have hwfun : b.w = b'.w := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).1
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.1, (hb'.2.1 i (not_lt.1 hi)).2.2.1]
  have hsgfun : b.sg = b'.sg := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).2
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.2, (hb'.2.1 i (not_lt.1 hi)).2.2.2]
  cases b
  cases b'
  simp only at hrz' hry' hofun hwfun hsgfun hoP
  rw [hrz', hry', hofun, hwfun, hsgfun, hoP]

theorem ioBlock_eq_sum (K : Type) [Field K] (b : SegBlock (segS X.TT j) X.m) (t : MvPolynomial (BV C0 CE1 CE2 X j) K) :
    ioBlock K X.p C0 CE1 CE2 X j b t = ∑ μ ∈ t.support, monomial (ioExp C0 CE1 CE2 X j b μ) (t.coeff μ) := by
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  have hf : ∀ t, ioBlock K X.p C0 CE1 CE2 X j b t = f t := fun _ => rfl

  conv_lhs => rw [hf, ← t.support_sum_monomial_coeff, map_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [← hf, ioBlock_monomial]

end

theorem orthAt (C0 CE1 CE2 : ℝ) : OrthAt C0 CE1 CE2 := by
  classical
  intro X _ O _ _ mm hD1 j b b' hb hb' hne s hs s' hs'
  have hp : 0 < X.p := hD1.1.pos
  rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b s, Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ (support_sum)]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨μ, hμ, he'⟩ := Finset.mem_biUnion.1 he
  have hem := support_monomial_subset he'
  rw [Finset.mem_singleton] at hem
  subst hem
  have h0 : AddMonoidAlgebra.coeff (ioBlock (KK O) X.p C0 CE1 CE2 X j b' s') (ioExp C0 CE1 CE2 X j b μ) = 0 := by
    rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b' s', coeff_sum]
    refine Finset.sum_eq_zero fun μ' hμ' => ?_
    rw [coeff_monomial, if_neg]
    intro h
    exact hne (sep C0 CE1 CE2 X j hp b' b hb' hb μ' μ (hom_of_ssz C0 CE1 CE2 X j b' mm s' hs' μ' hμ')
      (hom_of_ssz C0 CE1 CE2 X j b mm s hs μ hμ) h).symm
  rw [h0, mul_zero, zero_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end
