module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMulStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexOneUnitsMulEqCardQuotient

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_oneUnits_iff_exists_eq_one_add {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  unfold oneUnits
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 ↔ _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx]; ring⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx]; ring⟩

theorem relIndex_oneUnits_mul_eq_card_quotient :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t →
      Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) →
      (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  intro O _ _ t s ht hst hJ
  have hex : ∀ u : oneUnits t, ∃ x : O, ((u : Oˣ) : O) = 1 + t * x := fun u =>
    (mem_oneUnits_iff_exists_eq_one_add t u).1 u.2
  choose c hc using hex
  have huniq : ∀ (u : oneUnits t) (x : O), ((u : Oˣ) : O) = 1 + t * x → c u = x := by
    intro u x hx
    have h := hc u
    rw [hx] at h
    exact (mul_left_cancel₀ ht (add_left_cancel h)).symm
  let f : oneUnits t →* Multiplicative (O ⧸ Ideal.span {s}) :=
    { toFun := fun u => Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u))
      map_one' := by
        rw [huniq 1 0 (by simp)]
        simp
      map_mul' := by
        intro u v
        rw [huniq (u * v) (c u + c v + t * (c u * c v)) (by
          rw [Subgroup.coe_mul, Units.val_mul, hc u, hc v]; ring), ← ofAdd_add, ← map_add (f := _)]
        congr 1
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        have : c u + c v + t * (c u * c v) - (c u + c v) = t * (c u * c v) := by ring
        rw [this]
        exact hst.mul_right _ }
  have hf : ∀ u, f u = Multiplicative.ofAdd (Ideal.Quotient.mk (Ideal.span {s}) (c u)) :=
    fun _ => rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd y)
    have hu : IsUnit (t * x + 1) :=
      Ideal.mem_jacobson_bot.1 (hJ (Ideal.mem_span_singleton_self t)) x
    have hval : ((hu.unit : Oˣ) : O) = 1 + t * x := by rw [hu.unit_spec, add_comm]
    refine ⟨⟨hu.unit, (mem_oneUnits_iff_exists_eq_one_add t _).2 ⟨x, hval⟩⟩, ?_⟩
    rw [hf, huniq _ x hval, hx]
    rfl
  have hker : (oneUnits (s * t)).subgroupOf (oneUnits t) = f.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hf, mem_oneUnits_iff_exists_eq_one_add,
      ofAdd_eq_one, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, huniq u _ (by rw [hx]; ring)⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hc u, hx]; ring⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
    Subgroup.card_top]
  rfl

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexOneUnitsMulEqCardQuotientStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' : ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t → Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) → (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  first | exact @GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | exact GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | (intros; apply GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicComp

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem deep_smod_iff {O : Type} [CommRing O] (π a b : O) (n : ℕ) :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule O O)] ↔ π ^ n ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem deep_exists_solution {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (h : O[X]) (y : O) :
    ∃ x : O, x + π * h.eval x = y := by
  let T : O → O := fun x => y - π * h.eval x
  have hT : ∀ (n : ℕ) (a b : O), π ^ n ∣ a - b → π ^ (n + 1) ∣ T a - T b := by
    intro n a b hab
    have h1 : π ^ n ∣ h.eval a - h.eval b := hab.trans (Polynomial.sub_dvd_eval_sub a b h)
    obtain ⟨c, hc⟩ := h1
    refine ⟨-c, ?_⟩
    simp only [T]
    linear_combination (-π) * hc
  let s : ℕ → O := fun n => T^[n] 0
  have hs : ∀ n, s (n + 1) = T (s n) := fun n => Function.iterate_succ_apply' T n 0
  have h1 : ∀ n, π ^ n ∣ s n - s (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hT n _ _ ih
      rwa [← hs, ← hs] at this
  have h2 : ∀ m n, m ≤ n → π ^ m ∣ s m - s n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_add ih ((pow_dvd_pow π hmn).trans (h1 n))
      simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) (M := O) inferInstance (f := s)
    (fun {m n} hmn => (deep_smod_iff π _ _ m).2 (h2 m n hmn))
  have hL' : ∀ n, π ^ n ∣ s n - L := fun n => (deep_smod_iff π _ _ n).1 (hL n)
  have h0 : L - T L = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {π}) (M := O) inferInstance _ (fun n => ?_)
    rw [deep_smod_iff]
    have a1 := hT n _ _ (hL' n)
    rw [← hs] at a1
    have a2 := dvd_sub a1 (hL' (n + 1))
    have a3 := (pow_dvd_pow π (Nat.le_succ n)).trans a2
    convert a3 using 1
    ring
  refine ⟨L, ?_⟩
  simp only [T] at h0
  linear_combination h0

theorem deep_binomial {O : Type} [CommRing O] (t : O) (n : ℕ) :
    ∃ g : O[X], ∀ x : O, (1 + t * x) ^ n = 1 + n * t * x + t ^ 2 * x ^ 2 * g.eval x := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g * (1 + C t * X) + C (n : O), fun x => ?_⟩
    rw [pow_succ, hg]
    simp only [eval_add, eval_mul, eval_one, eval_C, eval_X, Nat.cast_succ]
    ring

theorem deep_mem_oneUnits {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  rw [oneUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  have : ((Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t}) (u : O) = 1) ↔
      Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 := Iff.rfl
  rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩

theorem deep_isUnit {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (x : O) : IsUnit (1 + π * x) := by
  have h : π ∈ (⊥ : Ideal O).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {π}) (Ideal.mem_span_singleton_self π)
  have := Ideal.mem_jacobson_bot.1 h x
  rwa [add_comm] at this

theorem deep_units_pows :
    ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 →
      IsAdicComplete (Ideal.span {π}) O →
      pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧
        pTor p (oneUnits ((p : O) * π)) = 1 := by
  intro p O _ _ _ π hp hπ hc
  obtain ⟨g, hg⟩ := deep_binomial ((p : O) * π) p
  have key : ∀ x : O, (1 + (p : O) * π * x) ^ p =
      1 + (p : O) ^ 2 * π * (x + π * (X ^ 2 * g).eval x) := by
    intro x
    rw [hg]
    simp only [eval_mul, eval_pow, eval_X]
    ring
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  constructor
  · ext u
    rw [pows, Subgroup.mem_map, deep_mem_oneUnits]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hv
      exact ⟨_, by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hx, key]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := deep_exists_solution π (X ^ 2 * g) y
      obtain ⟨v, hv⟩ := deep_isUnit π ((p : O) * x)
      have hv' : (v : O) = 1 + (p : O) * π * x := by rw [hv]; ring
      refine ⟨v, (deep_mem_oneUnits _ _).2 ⟨x, hv'⟩, Units.ext ?_⟩
      rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hv', key, hx, hy]
  · rw [pTor, Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_mem _, one_pow _⟩, ?_⟩
    rintro ⟨u, hu, hu1⟩
    obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hu
    have h1 : (u : O) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]
    rw [hx, key] at h1
    have h2 : (p : O) ^ 2 * π * (x * (1 + π * (x * g.eval x))) = 0 := by
      simp only [eval_mul, eval_pow, eval_X] at h1
      linear_combination h1
    have h3 : x = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) hπ)
      · exact (mul_eq_zero.1 h).resolve_right (deep_isUnit π _).ne_zero
    refine Subtype.ext (Units.ext ?_)
    simp [hx, h3]

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧ pTor p (oneUnits ((p : O) * π)) = 1 := by
  first | exact @GlobalTheory.CNorm.deep_units_pows | exact GlobalTheory.CNorm.deep_units_pows | (intros; apply GlobalTheory.CNorm.deep_units_pows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicComplete

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]

theorem pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  intro p O _ _ _ π hp hπ hc hfin
  haveI : Finite (O ⧸ Ideal.span {(p : O) * π}) := Nat.finite_of_card_ne_zero hfin
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete p O π hp hπ hc
  have hle : Ideal.span {(p : O) * π} ≤ Ideal.span {π} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro_left _ rfl)
  have hle' : Ideal.span {(p : O) * π} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ rfl)
  have hs := GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' O ((p : O) * π) p (mul_ne_zero hp0 hπ) (Dvd.intro _ rfl)
    (hle.trans (IsAdicComplete.le_jacobson_bot _))
  have hk : pIdx p (oneUnits ((p : O) * π)) = Nat.card (O ⧸ Ideal.span {(p : O)}) := by
    unfold pIdx
    rw [hd1, ← hs, sq, mul_assoc]
  haveI : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle')
  have hk0 : Nat.card (O ⧸ Ideal.span {(p : O)}) ≠ 0 := Nat.card_pos.ne'
  let g : Oˣ →* (O ⧸ Ideal.span {(p : O) * π})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(p : O) * π}) : O →* O ⧸ Ideal.span {(p : O) * π})
  have hker : g.ker = oneUnits ((p : O) * π) := rfl
  obtain ⟨hr1, hr2⟩ := pIdx_eq_pTor_of_finite_group p g.range
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p _ _ g (by rw [hker, hk]; exact hk0)
    (by rw [hker, hd2]; exact one_ne_zero) (by rw [hr2]; exact hr1) hr1
  refine ⟨h2, ?_⟩
  rw [hker, hd2, hk, hr2, mul_one, mul_right_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr1) h3

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | exact GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | (intros; apply GlobalTheory.CNorm.pIdx_units_of_isAdicComplete <;> assumption)
end
end
