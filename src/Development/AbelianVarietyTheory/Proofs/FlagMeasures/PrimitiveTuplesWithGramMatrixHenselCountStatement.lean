module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Index
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HenselStepCardComap

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory

theorem henselStep_card_comap {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by
  have hsup : d.range ⊔ T2 = T1 := by
    apply le_antisymm
    · refine sup_le ?_ h21
      rintro _ ⟨w, rfl⟩
      exact hd1 w
    · intro t ht
      obtain ⟨w, hw⟩ := hd2 t ht
      have : t = d w + -(d w - t) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)
  have h1 : (T2.comap d).index = T2.relIndex T1 := by
    rw [AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]
  have h2 := AddSubgroup.card_mul_index (T2.comap d)
  have h3 := AddSubgroup.card_mul_index (T2.addSubgroupOf T1)
  have h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2 :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv
  rw [h4] at h3
  rw [← h2, ← h3, h1]
  unfold AddSubgroup.relIndex
  ring

theorem henselStep_count {V W T : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Finite V] [Finite W] [Finite T] (ι : W →+ V) (f : V → T) (P : Set V)
    (T1 T2 : AddSubgroup T) (τ : T) (h21 : T2 ≤ T1) (hP : ∀ y ∈ P, ∀ w, y + ι w ∈ P)
    (hd : ∀ y ∈ P, ∃ d : W →+ T, (∀ w, d w ∈ T1) ∧ (∀ t ∈ T1, ∃ w, d w - t ∈ T2) ∧
      ∀ w, f (y + ι w) - f y - d w ∈ T2) :
    Set.ncard {y | y ∈ P ∧ f y - τ ∈ T1} * Nat.card T2 =
      Set.ncard {y | y ∈ P ∧ f y - τ ∈ T2} * Nat.card T1 := by
  set S1 : Set V := {y | y ∈ P ∧ f y - τ ∈ T1} with hS1
  set S2 : Set V := {y | y ∈ P ∧ f y - τ ∈ T2} with hS2

  have ha : Nat.card (Σ y : S1, {w : W // (y : V) + ι w ∈ S2}) = S2.ncard * Nat.card W := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1 + ι p.2.1, p.2.2⟩, p.2.1)
        invFun := fun q => ⟨⟨q.1.1 + ι (-q.2), ?_⟩, ⟨q.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨⟨u, hu, hu2⟩, w⟩ := q
      refine ⟨hP u hu _, ?_⟩
      obtain ⟨d, h1, -, h3⟩ := hd u hu
      have : f (u + ι (-w)) - τ = (f (u + ι (-w)) - f u - d (-w)) + d (-w) + (f u - τ) := by
        abel
      simp only
      rw [this]
      exact T1.add_mem (T1.add_mem (h21 (h3 _)) (h1 _)) (h21 hu2)
    · simp
    · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
      have : y + ι w + ι (-w) = y := by simp
      refine Sigma.subtype_ext ?_ rfl
      exact Subtype.ext this
    · rintro ⟨⟨u, hu⟩, w⟩
      simp
  have hb : ∀ y : S1, Nat.card {w : W // (y : V) + ι w ∈ S2} * Nat.card T1 =
      Nat.card W * Nat.card T2 := by
    rintro ⟨y, hy, hy1⟩
    obtain ⟨d, h1, h2, h3⟩ := hd y hy
    rw [← henselStep_card_comap T1 T2 h21 d h1 h2]
    congr 1
    obtain ⟨w0, hw0⟩ := h2 _ (T1.neg_mem hy1)
    refine Nat.card_congr ((Equiv.subRight w0).subtypeEquiv ?_)
    intro w
    simp only [hS2, Set.mem_setOf_eq, Equiv.subRight_apply, AddSubgroup.mem_comap, map_sub]
    have key : f (y + ι w) - τ =
        (f (y + ι w) - f y - d w) + (d w0 - -(f y - τ)) + (d w - d w0) := by abel
    rw [key]
    constructor
    · rintro ⟨-, h⟩
      exact (T2.add_mem_cancel_left (T2.add_mem (h3 w) hw0)).1 h
    · intro h
      exact ⟨hP y hy w, T2.add_mem (T2.add_mem (h3 w) hw0) h⟩
  haveI := Fintype.ofFinite S1
  rw [Nat.card_sigma] at ha
  have hc : S2.ncard * Nat.card W * Nat.card T1 = S1.ncard * (Nat.card W * Nat.card T2) := by
    rw [← ha, Finset.sum_mul, Finset.sum_congr rfl (fun y _ => hb y), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hW : 0 < Nat.card W := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hW
  linarith [hc]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesWithGramMatrixHenselCount

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def henselHerm (c : A →+* A) (m : ℕ) (q : A) : AddSubgroup (Matrix (Fin m) (Fin m) A) where
  carrier := {H | (∀ a b, c (H b a) = H a b) ∧ ∀ a b, q ∣ H a b}
  zero_mem' := ⟨fun a b => by simp, fun a b => by simp⟩
  add_mem' := fun {H K} hH hK =>
    ⟨fun a b => by simp [Matrix.add_apply, hH.1, hK.1],
      fun a b => by simpa [Matrix.add_apply] using dvd_add (hH.2 a b) (hK.2 a b)⟩
  neg_mem' := fun {H} hH =>
    ⟨fun a b => by simp [Matrix.neg_apply, hH.1],
      fun a b => by simpa [Matrix.neg_apply] using hH.2 a b⟩

def henselGram (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Matrix (Fin m) (Fin m) A :=
  Matrix.of fun a b => ip c (x b) (x a)

def henselDiff (c : A →+* A) {m n : ℕ} (q : A) (x : Fin m → Fin n → A) :
    (Fin m → Fin n → A) →+ Matrix (Fin m) (Fin m) A where
  toFun w := Matrix.of fun a b => q * (ip c (w b) (x a) + ip c (x b) (w a))
  map_zero' := by
    ext a b
    simp [ip_zero_left, ip_zero_right]
  map_add' w w' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, ip_add_left, ip_add_right]
    ring

theorem hensel_step [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (i : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 1))} *
      Nat.card (henselHerm c m (p ^ (i + 2))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 2))} *
      Nat.card (henselHerm c m (p ^ (i + 1))) := by
  obtain ⟨θ, -, hθ, -, -⟩ := exists_trace_one c hc hω
  have hq : c (p ^ (i + 1)) = p ^ (i + 1) := by rw [map_pow, hp]
  refine GlobalTheory.henselStep_count (DistribSMul.toAddMonoidHom (Fin m → Fin n → A) (p ^ (i + 1)))
    (henselGram c) _ _ _ G ?_ ?_ ?_
  · intro H hH
    exact ⟨hH.1, fun a b => (pow_dvd_pow p (by omega)).trans (hH.2 a b)⟩
  · rintro x ⟨y, hy⟩ w
    refine prim_of_sub_mem c hc (Ideal.span {p}) ?_ _ y fun a b => ?_
    · intro u hu
      obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hu
      exact IsNilpotent.isUnit_one_add ((Commute.all _ _).isNilpotent_mul_right hn)
    · rw [Ideal.mem_span_singleton]
      refine ⟨p ^ i * ip c (w a) (y b), ?_⟩
      simp only [Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, ip_add_left,
        ip_smul_left, hy]
      ring
  · rintro x ⟨y, hy⟩
    refine ⟨henselDiff c (p ^ (i + 1)) x, fun w => ⟨fun a b => ?_, fun a b => ?_⟩, ?_, fun w => ⟨fun a b => ?_, fun a b => ?_⟩⟩
    · simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, map_mul,
        map_add, hq, cj_ip c hc]
      ring
    · exact Dvd.intro _ rfl
    · intro H hH
      choose u hu using hH.2
      have hy' : ∀ a b, ip c (y b) (x a) = if a = b then 1 else 0 := by
        intro a b
        rw [← cj_ip c hc, hy]
        split_ifs <;> simp
      refine ⟨fun b => ∑ e, (θ * u e b) • y e, ?_⟩
      have : henselDiff c (p ^ (i + 1)) x (fun b => ∑ e, (θ * u e b) • y e) = H := by
        ext a b
        have h1 : p ^ (i + 1) * c (u b a) = H a b := by
          rw [← hH.1 a b, hu b a, map_mul, hq]
        simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
          ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, hy, hy', mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
        linear_combination (c θ) * h1 - θ * hu a b + H a b * hθ
      rw [this, sub_self]
      exact zero_mem _
    · simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, map_mul, map_sub, map_add, hq, cj_ip c hc]
      ring
    · refine ⟨p ^ i * ip c (w b) (w a), ?_⟩
      simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply,
        ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, hq]
      ring

theorem hensel_iter [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (k : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (0 + 1))} *
      Nat.card (henselHerm c m (p ^ (k + 1))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (k + 1))} *
      Nat.card (henselHerm c m (p ^ (0 + 1))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := hensel_step c hc hω hp hn m n G k
    have hpos : 0 < Nat.card (henselHerm c m (p ^ (k + 1))) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [show k + 1 + 1 = k + 2 from rfl]
    rw [mul_right_comm, ih, mul_right_comm, h, mul_right_comm]

theorem hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  intro A _ _ c hc ω hω p hp hn m n G hG
  obtain ⟨k, hk⟩ := id hn
  have h := hensel_iter c hc hω hp hn m n G k
  have hk' : p ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hbot : henselHerm c m (p ^ (k + 1)) = ⊥ := by
    rw [hk', eq_bot_iff]
    intro H hH
    rw [AddSubgroup.mem_bot]
    ext a b
    simpa using hH.2 a b
  rw [hbot, zero_add, pow_one, AddSubgroup.card_bot, mul_one] at h
  have e1 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m p} =
      {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
    ext x
    refine and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨fun a b => ?_, h⟩⟩
    simp only [henselGram, Matrix.sub_apply, Matrix.of_apply, map_sub, cj_ip c hc, hG]
  have e2 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ (⊥ : AddSubgroup (Matrix (Fin m) (Fin m) A))} = sols c n G := by
    ext x
    refine and_congr_right fun _ => ?_
    rw [AddSubgroup.mem_bot, sub_eq_zero, ← Matrix.ext_iff]
    rfl
  rw [e1, e2] at h
  exact h.symm

end GlobalTheory.GramCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesWithGramMatrixHenselCountStatement

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  first | exact @GlobalTheory.GramCount.hensel_count | exact GlobalTheory.GramCount.hensel_count | (intros; apply GlobalTheory.GramCount.hensel_count <;> assumption)
end
end
