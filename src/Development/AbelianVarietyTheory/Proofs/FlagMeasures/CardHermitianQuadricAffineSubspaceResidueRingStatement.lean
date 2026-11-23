module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLe

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_unit_mul_ip_eq_zero {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {n : ℕ} {s : B}
    (hs : IsUnit s) {z : Fin n → B} (hz : z ≠ 0) :
    ∑ y : Fin n → B, χ (s * ip c y z) = 0 := by
  let ψ : AddChar (Fin n → B) ℂ :=
    { toFun := fun y => χ (s * ip c y z)
      map_zero_eq_one' := by simp [ip_zero_left]
      map_add_eq_mul' := fun x y => by rw [ip_add_left, mul_add, AddChar.map_add_eq_mul] }
  have hψ : ψ ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    have hne : s * c (z i) ≠ 0 := by
      intro h0
      have h1 : c (z i) = 0 := (hs.mul_right_eq_zero).1 h0
      apply hi
      have := congrArg c h1
      simpa [hc] using this
    apply hχ hne
    ext u
    have h2 : χ (s * ip c (Pi.single i u) z) = 1 := DFunLike.congr_fun h (Pi.single i u)
    have h3 : ip c (Pi.single i u) z = u * c (z i) := by
      unfold ip
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [h3] at h2
    rw [AddChar.mulShift_apply, AddChar.one_apply, ← h2]
    congr 1
    ring
  exact AddChar.sum_eq_zero_of_ne_one hψ

theorem norm_gauss_sum_ip_le {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ
  set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS
  have key : ∀ y z : Fin n → B,
      χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z) := by
    intro y z
    have h1 : χ (a * ip c z y) = χ (c a * ip c y z) := by
      rw [← hinv, map_mul, cj_ip c hc]
    have h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y := by
      simp only [hQ, ip_add_left, ip_add_right]
      ring
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1,
      add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]
  have hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
    calc S * (starRingEnd ℂ) S
        = ∑ y : Fin n → B, S * (starRingEnd ℂ) (χ (Q y)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [hS, map_sum, ← hS, Finset.mul_sum]
      _ = ∑ y : Fin n → B, ∑ z : Fin n → B, χ (Q z) * χ ((a + c a) * ip c y z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => key y z
      _ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin n → B)]
          · simp [hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]
          · intro z _ hz
            rw [sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]
          · simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hsq
  have h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2 := by exact_mod_cast hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le

end GlobalTheory.GramCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLeStatement

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRing

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B] [Fintype B]

theorem quad_sum_char_pi (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {m : ℕ} (w : Fin m → B) :
    ∑ s : Fin m → B, χ (∑ i, s i * w i) =
      if w = 0 then (Fintype.card B : ℂ) ^ m else 0 := by
  have h1 : ∀ s : Fin m → B, χ (∑ i, s i * w i) = ∏ i, χ (s i * w i) := by
    intro s
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset B))
    (fun i b => χ (b * w i))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp only [AddChar.sum_mulShift _ hχ]
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [show w i ≠ 0 from hi])


omit [Fintype B] in
theorem quad_char_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (χ : AddChar B ℂ) (hχc : ∀ u, χ (c u) = χ u) {a w : B} (ha : c a = -a) (hw : c w = w) :
    χ (a * w) = 1 := by
  obtain ⟨θ, e, hθ, -, -⟩ := exists_trace_one c hc hω
  have h1 : a * w = θ * (a * w) + c (θ * (-(a * w))) := by
    simp only [map_mul, map_neg, ha, hw]
    linear_combination (-(a * w)) * hθ
  rw [h1, AddChar.map_add_eq_mul, hχc, ← AddChar.map_add_eq_mul]
  simp

theorem quad_count {B : Type} [CommRing B] [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u)
    (ω : B) (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive)
    (hχc : ∀ u, χ (c u) = χ u) (k n : ℕ) (hkn : 2 * k + 1 ≤ 2 * n) (x : Fin k → Fin n → B)
    (hx : Prim c x) (g : Fin k → B) (t : B) (ht : c t = t) :
    |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ)
      - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  set N := Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hN
  let F : B × (Fin k → B) → ℂ := fun z => ∑ y : Fin n → B,
    χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i))
  let G : B × (Fin k → B) → ℂ := fun z =>
    if c z.1 = -z.1 ∧ z.2 = 0 then (q : ℂ) ^ (2 * n) else 0
  have hF : ∑ z, F z = (N : ℂ) * (q : ℂ) ^ (2 * k + 2) := by
    simp only [F]
    rw [Finset.sum_comm]
    have h1 : ∀ y : Fin n → B, ∑ z : B × (Fin k → B),
        χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i)) =
        if (∀ i, ip c y (x i) = g i) ∧ ip c y y = t then (q : ℂ) ^ (2 * k + 2) else 0 := by
      intro y
      rw [Fintype.sum_prod_type]
      simp only
      rw [← Finset.sum_mul_sum, AddChar.sum_mulShift _ hχ,
        quad_sum_char_pi χ hχ (fun i => ip c y (x i) - g i)]
      have h2 : ((fun i => ip c y (x i) - g i) = 0) ↔ ∀ i, ip c y (x i) = g i := by
        simp [funext_iff, sub_eq_zero]
      simp only [h2, sub_eq_zero, hB]
      by_cases h3 : (∀ i, ip c y (x i) = g i) <;> by_cases h4 : ip c y y = t <;> simp [h3, h4]
      ring
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hN, ← Set.ncard_coe_finset]
    congr 3
    ext y
    simp
  have hG : ∑ z, G z = (q : ℂ) ^ (2 * n + 1) := by
    have h1 := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc
      (fun a u => by simp)).2
    rw [Nat.card_eq_fintype_card (α := B), hB] at h1
    have h2 := (Nat.pow_left_injective two_ne_zero) h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
    simp only [G]
    rw [Fintype.sum_prod_type]
    have h3 : ∀ a : B, (∑ s : Fin k → B,
        if c a = -a ∧ s = 0 then (q : ℂ) ^ (2 * n) else 0) =
        if c a = -a then (q : ℂ) ^ (2 * n) else 0 := by
      intro a
      by_cases h : c a = -a <;> simp [h]
    simp only [h3]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : (Finset.univ.filter fun a : B => c a = -a).card = q := by
      rw [← h2]; congr 1
    rw [h4]; ring
  have hFG : ∀ z, ‖F z - G z‖ ≤ (q : ℝ) ^ n := by
    rintro ⟨a, s⟩
    have hv : ∀ y : Fin n → B, ∑ i, s i * (ip c y (x i) - g i) =
        ip c y (∑ i, c (s i) • x i) - ∑ i, s i * g i := by
      intro y
      simp [ip_sum_right, ip_smul_right, hc, mul_sub, Finset.sum_sub_distrib]
    by_cases ha : c a = -a
    · have h0 : F (a, s) = G (a, s) := by
        have h1 : ∀ y : Fin n → B, χ (a * (ip c y y - t)) = 1 := fun y =>
          quad_char_skew c hc hω χ hχc ha (by rw [map_sub, cj_ip c hc, ht])
        simp only [F, G, h1, one_mul, ha, true_and]
        split_ifs with hs
        · simp [hs, hB, ← pow_mul]
        · simp only [hv]
          simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
          rw [← Finset.sum_mul]
          have h2 := quad_sum_char_pi χ hχ (fun j => c ((∑ i, c (s i) • x i) j))
          rw [if_neg] at h2
          · simp only [ip]
            rw [h2, zero_mul]
          · intro h3
            apply hs
            have h4 : ∑ i, c (s i) • x i = 0 := by
              funext j
              have := congrArg c (congrFun h3 j)
              simpa only [hc, Pi.zero_apply, map_zero] using this
            have h5 := hx.eq_zero c (fun i => c (s i)) h4
            funext i
            have := congrArg c (congrFun h5 i)
            simpa only [hc, Pi.zero_apply, map_zero] using this
      rw [h0, sub_self, norm_zero]
      positivity
    · have hu : IsUnit (a + c a) := hf _ (by rw [map_add (f := _), hc, add_comm])
        (fun h => ha (by linear_combination h))
      have h1 := GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le c hc q hq hB χ hχ hχc n a hu (∑ i, c (s i) • x i)
      have h2 : F (a, s) = χ (-(a * t + ∑ i, s i * g i)) *
          ∑ y : Fin n → B, χ (a * ip c y y + ip c y (∑ i, c (s i) • x i)) := by
        simp only [F, hv, Finset.mul_sum, ← AddChar.map_add_eq_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        ring
      have h3 : G (a, s) = 0 := by simp [G, ha]
      rw [h3, sub_zero, h2, norm_mul, AddChar.norm_apply, one_mul]
      exact h1
  have hS : ‖∑ z, F z - ∑ z, G z‖ ≤ (q : ℝ) ^ (2 * k + 2) * (q : ℝ) ^ n := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le_of_le _ fun z _ => hFG z).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, hB, nsmul_eq_mul]
    push_cast
    ring
  have hE : (q : ℂ) ^ (2 * n + 1) = (q : ℂ) ^ (2 * n - (2 * k + 1)) * (q : ℂ) ^ (2 * k + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hF, hG, hE, ← sub_mul, norm_mul] at hS
  have hq' : (0 : ℝ) < (q : ℝ) ^ (2 * k + 2) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h5 : ‖(q : ℂ) ^ (2 * k + 2)‖ = (q : ℝ) ^ (2 * k + 2) := by simp
  have h6 : ‖(N : ℂ) - (q : ℂ) ^ (2 * n - (2 * k + 1))‖ =
      |(N : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [h5, h6, mul_comm] at hS
  exact le_of_mul_le_mul_left hS hq'

end GlobalTheory.GramCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRingStatement

section

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (k n : ℕ), 2 * k + 1 ≤ 2 * n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.quad_count | exact GlobalTheory.GramCount.quad_count | (intros; apply GlobalTheory.GramCount.quad_count <;> assumption)
end
end
