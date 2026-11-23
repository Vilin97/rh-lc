module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOfSmulMkEqZero
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImageStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoinStatement
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerDOfPowEq

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kaehler_D_of_pow_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) (m : ℕ) (h : a ^ m = b) :
    a • KaehlerDifferential.D R S b = ((m : S) * b) • KaehlerDifferential.D R S a := by
  subst h
  rw [Derivation.leibniz_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [smul_comm a, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_pow (T : Tower p Ω) (n k : ℕ) : zS T (n + k) ^ (p ^ k) = zS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (zS T (n + (k + 1)) : Ω) ^ p = (zS T (n + k) : Ω) := T.ζpow (n + k)
    have h2 : (zS T (n + k) : Ω) ^ (p ^ k) = (zS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem qS_pow (T : Tower p Ω) (n k : ℕ) : qS T (n + k) ^ (p ^ k) = qS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (qS T (n + (k + 1)) : Ω) ^ p = (qS T (n + k) : Ω) := T.qpow (n + k)
    have h2 : (qS T (n + k) : Ω) ^ (p ^ k) = (qS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem dlog_transition : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n k : ℕ), zS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * zS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T (n + k)) ∧ qS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * qS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T (n + k)) := by
  intro p _ Ω _ _ T n k
  constructor
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (zS_pow T n k)
    simpa [Nat.cast_pow] using this
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (qS_pow T n k)
    simpa [Nat.cast_pow] using this

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValuesStatement

section

@[expose] public section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.almostDualTrace_derivation_mem_span_values : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C, (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  first | exact @GlobalTheory.AlmostEt.derOn_mem_span_of_trData | exact GlobalTheory.AlmostEt.derOn_mem_span_of_trData | (intros; apply GlobalTheory.AlmostEt.derOn_mem_span_of_trData <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PSqSmulKaehlerMemSpan

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

section Klc

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_eq_pow (T : Tower p Ω) (k j : ℕ) : zS T k = zS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.ζpow (k + j)).symm

theorem qS_eq_pow (T : Tower p Ω) (k j : ℕ) : qS T k = qS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.qpow (k + j)).symm

theorem D_zS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [zS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem D_qS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [qS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Klc


theorem p_sq_smul_kaehler_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω))
    (n : ℕ), ∃ m, n ≤ m ∧ ∃ x y : (integralClosure (O0 p) Ω), (p : (integralClosure (O0 p) Ω)) ^ 2 • η =
      x • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m) +
        y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m) := by
  intro p _ Ω _ _ hp2 hclo T η n
  let 𝒮 := integralClosure (O0 p) Ω
  let 𝒟 := KaehlerDifferential.D (O0 p) 𝒮
  let N : ℕ → Submodule 𝒮 (KaehlerDifferential (O0 p) 𝒮) :=
    fun m => Submodule.span 𝒮 {𝒟 (zS T m), 𝒟 (qS T m)}
  have hmono : Monotone N := fun k m h => Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [D_zS_mem_span T h, D_qS_mem_span T h])
  have hder : ∀ B : Subalgebra (O0 p) 𝒮, IsDerOn B (fun x => 𝒟 x) := fun B =>
    ⟨fun x _ y _ => map_add 𝒟 x y, fun x _ y _ => Derivation.leibniz 𝒟 x y,
      fun a => (𝒟).map_algebraMap a⟩
  have hgen : ∀ t : 𝒮, (p : 𝒮) ^ 2 • 𝒟 t ∈ ⨆ m, N m := by
    intro t
    obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T {t}
    have h1 := GlobalTheory.T.almostDualTrace_derivation_mem_span_values (O0 p) 𝒮 _ (towerAlg T) C tr k a b _ htr (fun x => 𝒟 x) (hder C) t
      (hF (by simp))
    have h2 : Submodule.span 𝒮 ((fun x => 𝒟 x) '' (towerAlg T : Set 𝒮)) ≤ ⨆ m, N m := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h3 := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) 𝒮 _ (Set.range (zS T) ∪ Set.range (qS T)) (fun x => 𝒟 x)
        (hder _) x hx
      refine Submodule.span_le.2 ?_ h3
      rintro _ ⟨y, (⟨k, rfl⟩ | ⟨k, rfl⟩), rfl⟩
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
    rw [pow_two]
    exact h2 h1
  have hall : ∀ ω ∈ Submodule.span 𝒮 (Set.range 𝒟), (p : 𝒮) ^ 2 • ω ∈ ⨆ m, N m := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hgen t
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hη : (p : 𝒮) ^ 2 • η ∈ ⨆ m, N m :=
    hall η (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed N hmono.directed_le).1 hη
  refine ⟨max m n, le_max_right _ _, ?_⟩
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.1 (hmono (le_max_left m n) hm)
  exact ⟨x, y, hxy.symm⟩

end GlobalTheory.AlmostEt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionKaehlerSpanDlogIndep

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5

namespace GlobalTheory.K5.TorsionDiff

theorem dlog_descend {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (a ai b bi P : S) (da db : M) (ha : a * ai = 1) (hb : b * bi = 1)
    (h : b • da = (P * a) • db) : (P * bi) • db = ai • da := by
  have h2 := congrArg (fun m => (ai * bi) • m) h
  simp only [smul_smul] at h2
  have e1 : ai * bi * b = ai := by linear_combination ai * hb
  have e2 : ai * bi * (P * a) = P * bi := by linear_combination (P * bi) * ha
  rw [e1, e2] at h2
  exact h2.symm

theorem exists_inv_zS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ zi, zS T n * zi = 1 := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine ⟨zS T n ^ (p ^ n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel hpos]
  exact Subtype.ext (T.prim n).pow_eq_one

theorem exists_inv_qS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ qi, qS T n * qi = 1 := by
  have hne : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h1 : qS T n ^ (p ^ n) = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (GlobalTheory.AlmostEt.qq_pow T n)
  have h2 : IsUnit (qS T n ^ (p ^ n)) := by
    rw [h1]; exact (GlobalTheory.K5.Basic.isUnit_qO p).map _
  exact ((isUnit_pow_iff hne).1 h2).exists_right_inv

theorem span_core {S M : Type*} [CommRing S] [IsDomain S] [AddCommGroup M] [Module S M]
    (P : S) (hP : P ≠ 0) (n k : ℕ) (hn : 1 ≤ n) (η dz dq dzm dqm : M)
    (zi qi zm qm zim qim x y : S) (hz : zm * zim = 1) (hq : qm * qim = 1)
    (hη : P ^ n • η = 0) (hs : P ^ 2 • η = x • dzm + y • dqm)
    (hdz : (P ^ k * zim) • dzm = zi • dz) (hdq : (P ^ k * qim) • dqm = qi • dq)
    (hind : ∀ x y : S, (x * zim) • dzm + (y * qim) • dqm = 0 →
      (∃ t, P ^ 3 * x = P ^ (n + k - 1) * t) ∧ (∃ t, P ^ 3 * y = P ^ (n + k) * t)) :
    ∃ x y : S, P ^ 6 • η = (x * zi) • dz + (y * qi) • dq := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : (P ^ (n + 1) * x * zm * zim) • dzm + (P ^ (n + 1) * y * qm * qim) • dqm = 0 := by
    rw [mul_assoc _ zm, hz, mul_assoc _ qm, hq, mul_one, mul_one, mul_smul, mul_smul, ← smul_add,
      ← hs, smul_comm, hη, smul_zero]
  obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := hind _ _ h0
  have e : n + 1 + k - 1 = n + k := by omega
  rw [e] at ht
  have hx : P ^ 4 * x = t * (P ^ k * zim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination zim * ht - P ^ (n + 4) * x * hz
  have hy : P ^ 4 * y = P * u * (P ^ k * qim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination qim * hu - P ^ (n + 4) * y * hq
  refine ⟨t, P * u, ?_⟩
  have e6 : P ^ 6 = P ^ 4 * P ^ 2 := by ring
  rw [e6, mul_smul, hs, smul_add, smul_smul, smul_smul, hx, hy, mul_smul t, mul_smul (P * u),
    hdz, hdq, smul_smul, smul_smul]

theorem torsion_span_and_indep : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ z qn zi qi : integralClosure (O0 p) Ω,
  (z : Ω) = T.ζ n → (qn : Ω) = T.qq n → z * zi = 1 → qn * qi = 1 →
  (∀ η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω), (p ^ n : ℕ) • η = 0 →
     ∃ x y : integralClosure (O0 p) Ω, (p ^ c : ℕ) • η =
       (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn) ∧
  (∀ x y : integralClosure (O0 p) Ω,
     (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn = 0 →
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * x = (p : integralClosure (O0 p) Ω) ^ (n - 1) * t) ∧
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * y = (p : integralClosure (O0 p) Ω) ^ n * t)) := by
  intro p _ hp2
  refine ⟨6, ?_⟩
  intro Ω _ _ hΩ T n hn z qn zi qi hz hq hzi hqi
  obtain rfl : z = zS T n := Subtype.ext hz
  obtain rfl : qn = qS T n := Subtype.ext hq
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hΩ
  have hP : (p : integralClosure (O0 p) Ω) ≠ 0 := by
    intro h
    have h2 : (p : Ω) = 0 := by simpa using congrArg Subtype.val h
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  refine ⟨?_, ?_⟩
  · intro η hη
    obtain ⟨m, hm, x, y, hs⟩ := GlobalTheory.AlmostEt.p_sq_smul_kaehler_mem_span p Ω hp2 hΩ T η n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨zim, hzim⟩ := exists_inv_zS T (n + k)
    obtain ⟨qim, hqim⟩ := exists_inv_qS T (n + k)
    obtain ⟨hdz, hdq⟩ := GlobalTheory.AlmostEt.dlog_transition p Ω T n k
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), Nat.cast_pow] at hη ⊢
    exact span_core _ hP n k hn η _ _ _ _ zi qi _ _ zim qim x y hzim hqim hη hs
      (dlog_descend _ _ _ _ _ _ _ hzi hzim hdz) (dlog_descend _ _ _ _ _ _ _ hqi hqim hdq)
      (fun x y h => GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T (n + k) (by omega) x y zim qim hzim hqim h)
  · intro x y h
    obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T n hn x y zi qi hzi hqi h
    exact ⟨⟨(p : integralClosure (O0 p) Ω) ^ 3 * t, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * ht⟩,
      ⟨(p : integralClosure (O0 p) Ω) ^ 3 * u, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * hu⟩⟩

end GlobalTheory.K5.TorsionDiff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionKaehlerSpanDlogIndepStatement

section

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.torsion_kaehler_span_dlog_indep : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ z qn zi qi : integralClosure (O0 p) Ω,
  (z : Ω) = T.ζ n → (qn : Ω) = T.qq n → z * zi = 1 → qn * qi = 1 →
  (∀ η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω), (p ^ n : ℕ) • η = 0 →
     ∃ x y : integralClosure (O0 p) Ω, (p ^ c : ℕ) • η =
       (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn) ∧
  (∀ x y : integralClosure (O0 p) Ω,
     (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn = 0 →
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * x = (p : integralClosure (O0 p) Ω) ^ (n - 1) * t) ∧
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * y = (p : integralClosure (O0 p) Ω) ^ n * t)) := by
  first | exact @GlobalTheory.K5.TorsionDiff.torsion_span_and_indep | exact GlobalTheory.K5.TorsionDiff.torsion_span_and_indep | (intros; apply GlobalTheory.K5.TorsionDiff.torsion_span_and_indep <;> assumption)
end
end
