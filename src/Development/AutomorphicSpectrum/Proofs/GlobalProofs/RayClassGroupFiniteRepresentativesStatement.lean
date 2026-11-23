module

public import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

-- Source module: Formalism.UnipotentAdelicQuotients.ClassNumberQuad

section

@[expose] public section

universe u

open NumberField Module

namespace HeckeCharacterZeroLocus.ClassNumberQuad

def ClassNumberLe : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], finrank ℚ K = 2 → IsTotallyComplex K →
    (classNumber K : ℝ) ≤ Real.sqrt (|discr K| : ℝ) * (Real.log (|discr K| : ℝ) + 2) / Real.pi

end HeckeCharacterZeroLocus.ClassNumberQuad
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL2.TotallyComplexOfNoReal

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ShortIntervalPrimes NumberField

section Ray

variable {K0 : Type} [Field K0] [NumberField K0]

lemma exists_mem_sub_one_mem (qq I : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) :
    ∃ b ∈ I, b ≠ 0 ∧ b - 1 ∈ qq := by
  obtain ⟨i, hi, t, ht, hit⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 K0) ∈ I ⊔ qq by rw [hI.2]; trivial)
  by_cases h0 : i = 0
  · subst h0
    have ht1 : t = 1 := by simpa using hit
    have hq : qq = ⊤ := (Ideal.eq_top_iff_one qq).2 (ht1 ▸ ht)
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
    exact ⟨b, hb, hb0, by rw [hq]; trivial⟩
  · refine ⟨i, hi, h0, ?_⟩
    have : i - 1 = -t := by rw [← hit]; ring
    rw [this]
    exact qq.neg_mem ht

lemma exists_rel_of_class (qq I J : Ideal (𝓞 K0)) (hI : CoprimeTo K0 qq I) (hJ : CoprimeTo K0 qq J)
    (x y : 𝓞 K0) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ qq ∧ Ideal.span {a} ⊔ qq = ⊤ ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨b, hbI, hb0, hb1⟩ := exists_mem_sub_one_mem qq I hI
  have hxb : x * b ∈ Ideal.span {y} := by
    have : x * b ∈ Ideal.span {x} * I := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hbI
    rw [hxy] at this
    exact Ideal.mul_le_left this
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hxb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact mul_ne_zero hx hb0 ha.symm
  have hy' : Ideal.span {y} ≠ (0 : Ideal (𝓞 K0)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have key : Ideal.span {a} * I = Ideal.span {b} * J := by
    apply mul_left_cancel₀ hy'
    calc Ideal.span {y} * (Ideal.span {a} * I) = Ideal.span {a * y} * I := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm y a]
      _ = Ideal.span {b} * (Ideal.span {x} * I) := by
          rw [ha, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, mul_comm b x]
      _ = Ideal.span {y} * (Ideal.span {b} * J) := by
          rw [hxy, mul_left_comm]
  have hbq : Ideal.span {b} ⊔ qq = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K0) = b - (b - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)) (Ideal.mem_sup_right hb1)
  have hcop : Ideal.span {b} * J ⊔ qq = ⊤ := by
    have h1 : IsCoprime (Ideal.span {b}) qq := Ideal.isCoprime_iff_sup_eq.2 hbq
    have h2 : IsCoprime J qq := Ideal.isCoprime_iff_sup_eq.2 hJ.2
    exact Ideal.isCoprime_iff_sup_eq.1 (h1.mul_left h2)
  have haq : Ideal.span {a} ⊔ qq = ⊤ := by
    rw [← key] at hcop
    refine top_unique ?_
    calc (⊤ : Ideal (𝓞 K0)) = Ideal.span {a} * I ⊔ qq := hcop.symm
      _ ≤ Ideal.span {a} ⊔ qq := sup_le_sup_right Ideal.mul_le_left qq
  exact ⟨a, b, ha0, hb0, hb1, haq, key⟩

variable (hCN : HeckeCharacterZeroLocus.ClassNumberQuad.ClassNumberLe.{0})
include hCN

end Ray

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentatives

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmbeddings : Finite (F →+* ℝ) := by
  infer_instance

theorem rayRel_of_signs (𝔣 I J R : Ideal (𝓞 F)) (a a' b b' : 𝓞 F) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb0 : b ≠ 0) (hb0' : b' ≠ 0)
    (hb1 : b - 1 ∈ 𝔣) (hb1' : b' - 1 ∈ 𝔣) (haq : Ideal.span {a} ⊔ 𝔣 = ⊤) (haa : a - a' ∈ 𝔣)
    (hs : ∀ σ : F →+* ℝ, 0 < σ ((a * b : 𝓞 F) : F) ↔ 0 < σ ((a' * b' : 𝓞 F) : F))
    (e1 : Ideal.span {a} * I = Ideal.span {b} * R) (e2 : Ideal.span {a'} * J = Ideal.span {b'} * R) :
    RayRel F 𝔣 I J := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : 𝓞 F, c ≠ 0 ∧ c * a - 1 ∈ 𝔣 := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔣 := by rw [haq]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    by_cases h : c = 0
    · subst h
      have hz1 : (1 : 𝓞 F) ∈ 𝔣 := by rw [← hyz]; simpa using hz
      exact ⟨1, one_ne_zero, by simpa using 𝔣.mul_mem_left (1 * a - 1) hz1⟩
    · refine ⟨c, h, ?_⟩
      have : c * a - 1 = -z := by rw [← hyz]; ring
      rw [this]; exact 𝔣.neg_mem hz
  have qb : Ideal.Quotient.mk 𝔣 b = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1
  have qb' : Ideal.Quotient.mk 𝔣 b' = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1'
  have qa : Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a := (Ideal.Quotient.eq.2 haa).symm
  have qc : Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hc
  have same : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (0 < x ↔ 0 < y) → 0 < x * y := by
    intro x y hx hy hxy
    rcases lt_or_gt_of_ne hx with h | h
    · have hy' : y < 0 := lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hxy.2 h') (not_lt.2 h.le))) hy
      exact mul_pos_of_neg_of_neg h hy'
    · exact mul_pos h (hxy.1 h)
  have coe0 : ∀ x : 𝓞 F, x ≠ 0 → ∀ σ : F →+* ℝ, σ (x : F) ≠ 0 := by
    intro x hx σ
    exact (map_ne_zero σ).2 (by exact_mod_cast hx)
  refine ⟨(a * b' * c) ^ 2, a' * b * a * b' * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0') hc0)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0' hb0) ha0) hb0') (pow_ne_zero 2 hc0)
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb']
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb, qb', qa]
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · intro σ
    constructor
    · have hx := coe0 _ (mul_ne_zero (mul_ne_zero ha0 hb0') hc0) σ
      have : σ (((a * b' * c) ^ 2 : 𝓞 F) : F) = (σ ((a * b' * c : 𝓞 F) : F)) ^ 2 := by
        push_cast; simp only [map_pow]
      rw [this]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
    · have h1 := coe0 _ (mul_ne_zero ha0 hb0) σ
      have h2 := coe0 _ (mul_ne_zero ha0' hb0') σ
      have h3 := coe0 _ hc0 σ
      have : σ ((a' * b * a * b' * c ^ 2 : 𝓞 F) : F) =
          σ ((a * b : 𝓞 F) : F) * σ ((a' * b' : 𝓞 F) : F) * (σ (c : F)) ^ 2 := by
        push_cast; simp only [map_mul, map_pow]; ring
      rw [this]
      exact mul_pos (same _ _ h1 h2 (hs σ)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3)))
  · calc Ideal.span {(a * b' * c) ^ 2} * I
        = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {a} * I) := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 2; ring_nf
      _ = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {b} * R) := by rw [e1]
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {b'} * R) := by
          rw [← mul_assoc, ← mul_assoc, Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]; congr 3; ring
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {a'} * J) := by rw [e2]
      _ = Ideal.span {a' * b * a * b' * c ^ 2} * J := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 3; ring

theorem finRay (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  classical
  haveI : Finite (F →+* ℝ) := finite_realEmbeddings
  haveI : Finite (𝓞 F ⧸ 𝔣) :=
    (Ideal.absNorm_ne_zero_iff 𝔣).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have key : ∀ A : Ideal (𝓞 F), A ≠ ⊥ → ∃ B : Ideal (𝓞 F), B ≠ ⊥ ∧ B ⊔ 𝔣 = ⊤ ∧
      ∃ r : 𝓞 F, r ≠ 0 ∧ A * B = Ideal.span {r} := by
    intro A hA
    have hA' : A ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    have h𝔣' : 𝔣 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    have hM0 : M ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
    have hAg : A * (𝔣 * M) ≠ 0 := mul_ne_zero hA' (mul_ne_zero h𝔣' hM0)
    obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : A * (𝔣 * M) ≤ A) hAg
    obtain ⟨B, hB⟩ : A ∣ Ideal.span {r} :=
      Ideal.dvd_iff_le.2 ((le_sup_right : Ideal.span {r} ≤ A * (𝔣 * M) ⊔ Ideal.span {r}).trans hr.le)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hr
      have h1 : 𝔣 * M = ⊤ := by
        apply mul_left_cancel₀ hA'
        rw [hr, Ideal.mul_top]
      have h2 : 𝔣 * M ≤ M := Ideal.mul_le_inf.trans inf_le_right
      rw [h1] at h2
      exact hM.ne_top (top_le_iff.1 h2)
    refine ⟨B, ?_, ?_, r, hr0, hB.symm⟩
    · rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hB
      exact hr0 hB
    · have h1 : A * (𝔣 * M ⊔ B) = A * ⊤ := by
        rw [Ideal.mul_sup, ← hB, hr, Ideal.mul_top]
      have h2 : 𝔣 * M ⊔ B = ⊤ := mul_left_cancel₀ hA' h1
      rw [eq_top_iff, ← h2]
      exact sup_le ((Ideal.mul_le_inf.trans inf_le_left).trans le_sup_right) le_sup_left
  have rep : ∀ c : ClassGroup (𝓞 F), ∃ P : Ideal (𝓞 F), ∃ hP : P ∈ nonZeroDivisors (Ideal (𝓞 F)),
      P ⊔ 𝔣 = ⊤ ∧ ClassGroup.mk0 ⟨P, hP⟩ = c := by
    intro c
    obtain ⟨⟨A, hA⟩, hAc⟩ := ClassGroup.mk0_surjective c⁻¹
    have hA0 : A ≠ ⊥ := by
      have := nonZeroDivisors.ne_zero hA
      rwa [Ne, Ideal.zero_eq_bot] at this
    obtain ⟨B, hB0, hBf, r, hr0, hAB⟩ := key A hA0
    have hBm : B ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])
    refine ⟨B, hBm, hBf, ?_⟩
    have hABm : A * B ∈ nonZeroDivisors (Ideal (𝓞 F)) := Submonoid.mul_mem _ hA hBm
    have h1 : ClassGroup.mk0 ⟨A * B, hABm⟩ = 1 := (ClassGroup.mk0_eq_one_iff hABm).2 ⟨⟨r, hAB⟩⟩
    have h2 : ClassGroup.mk0 ⟨A * B, hABm⟩ = ClassGroup.mk0 ⟨A, hA⟩ * ClassGroup.mk0 ⟨B, hBm⟩ := by
      rw [← map_mul]; rfl
    rw [h2, hAc] at h1
    exact (inv_mul_eq_one.1 h1).symm
  choose P hPm hPf hPc using rep
  have hPcop : ∀ c, CoprimeTo F 𝔣 (P c) := by
    intro c
    have := nonZeroDivisors.ne_zero (hPm c)
    rw [Ne, Ideal.zero_eq_bot] at this
    exact (show P c ≠ ⊥ ∧ P c ⊔ 𝔣 = ⊤ from ⟨this, hPf c⟩)
  have hcov : ∀ I : Ideal (𝓞 F), CoprimeTo F 𝔣 I → ∃ (c : ClassGroup (𝓞 F)) (a b : 𝓞 F),
      a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ 𝔣 ∧ Ideal.span {a} ⊔ 𝔣 = ⊤ ∧
        Ideal.span {a} * I = Ideal.span {b} * P c := by
    intro I hI
    have hI' : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ := hI
    have hIm : I ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact hI'.1)
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hPc (ClassGroup.mk0 ⟨I, hIm⟩)).symm
    obtain ⟨a, b, ha, hb, hb1, haq, he⟩ :=
      Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.exists_rel_of_class 𝔣 I (P (ClassGroup.mk0 ⟨I, hIm⟩)) hI (hPcop _) x y hx hy hxy
    exact ⟨_, a, b, ha, hb, hb1, haq, he⟩
  choose cl a b ha hb hb1 haq he using hcov
  obtain ⟨κ, hκ⟩ : ∃ κ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} →
      ClassGroup (𝓞 F) × (𝓞 F ⧸ 𝔣) × Set (F →+* ℝ),
      κ = fun I => (cl I.1 I.2, Ideal.Quotient.mk 𝔣 (a I.1 I.2),
        {σ : F →+* ℝ | 0 < σ ((a I.1 I.2 * b I.1 I.2 : 𝓞 F) : F)}) := ⟨_, rfl⟩
  have hrel : ∀ I J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = κ J → RayRel F 𝔣 I.1 J.1 := by
    intro I J h
    rw [hκ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hq, hs⟩ := h
    refine rayRel_of_signs 𝔣 I.1 J.1 (P (cl I.1 I.2)) (a I.1 I.2) (a J.1 J.2) (b I.1 I.2) (b J.1 J.2)
      (ha _ _) (ha _ _) (hb _ _) (hb _ _) (hb1 _ _) (hb1 _ _) (haq _ _) (Ideal.Quotient.eq.1 hq)
      (fun σ => Set.ext_iff.1 hs σ) (he _ _) ?_
    rw [hc]; exact he _ _
  haveI : Nonempty {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} :=
    ⟨⟨⊤, show (⊤ : Ideal (𝓞 F)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 F)) ⊔ 𝔣 = ⊤ from ⟨top_ne_bot, top_sup_eq _⟩⟩⟩
  have hfin : (Set.range κ).Finite := Set.toFinite _
  have hne : ∀ d ∈ Set.range κ, ∃ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = d := fun d hd => hd
  choose! g hg using hne
  obtain ⟨T, hTc, hTcov⟩ : ∃ T : Finset (Ideal (𝓞 F)), (∀ t ∈ T, CoprimeTo F 𝔣 t) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ t ∈ T, RayRel F 𝔣 I t := by
    refine ⟨hfin.toFinset.image (fun d => (g d).1), ?_, ?_⟩
    · intro t ht
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 ht
      exact (g d).2
    · intro I hI
      have hd : κ ⟨I, hI⟩ ∈ Set.range κ := ⟨_, rfl⟩
      refine ⟨(g (κ ⟨I, hI⟩)).1, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hd), ?_⟩
      exact hrel ⟨I, hI⟩ (g (κ ⟨I, hI⟩)) (hg _ hd).symm
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 F) → Ideal (𝓞 F),
      f = fun t => Classical.epsilon (fun s => s ∈ T ∧ RayRel F 𝔣 t s) := ⟨_, rfl⟩
  have hfT : ∀ t ∈ T, f t ∈ T ∧ RayRel F 𝔣 t (f t) := by
    intro t ht
    rw [hf]
    exact Classical.epsilon_spec (p := fun s => s ∈ T ∧ RayRel F 𝔣 t s) ⟨t, ht, rayRel_refl t⟩
  have hfeq : ∀ t t', RayRel F 𝔣 t t' → f t = f t' := by
    intro t t' h
    simp only [hf]
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans (rayRel_symm h) h'⟩
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans h h'⟩
  refine ⟨T.image f, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact hTc _ (hfT t ht).1
  · intro s hs s' hs' h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
    apply hfeq
    exact rayRel_trans (hfT t ht).2 (rayRel_trans h (rayRel_symm (hfT t' ht').2))
  · intro I hI
    obtain ⟨t, ht, hIt⟩ := hTcov I hI
    exact ⟨f t, Finset.mem_image_of_mem _ ht, rayRel_trans hIt (hfT t ht).2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentativesStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.ray_class_group_finite_representatives : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
    ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay <;> assumption)
end
end
