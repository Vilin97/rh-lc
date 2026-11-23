module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MulVecMapInjective
import Mathlib.RingTheory.WittVector.IsPoly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MulVecMapInjective
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Lemmata.GeneralBFactThirdExtra.Imports

section

@[expose] public section

namespace Bl.general_b_fact_third_extra

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (v : S.V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro E _ _ _ S Λ hspan v
  have hv : v ∈ Submodule.span E (SetLike.coe Λ) := by
    rw [hspan]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • x = d₂ • (d₁ • x) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • y = d₁ • (d₂ • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ h₁) (Λ.smul_mem _ h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) a
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hm' : algebraMap (NumberField.RingOfIntegers E) E m ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
    have key : (m * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul E (m * d), ← algebraMap_smul E n, ← algebraMap_smul E d,
        smul_smul, smul_smul, ← hnm]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact Λ.smul_mem n h

end Bl.general_b_fact_third_extra
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.FiniteOfIntegralBound

section

@[expose] public section

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_extra.goal1 .. | (apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> first | assumption | infer_instance)

theorem finite_of_integral_bound (t : E) (ht : t ≠ 0) (C : ℝ) :
    {a : E | IsIntegral ℤ (t * a) ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}.Finite := by
  set K : ℝ := ∑ τ : E →+* ℂ, ‖τ t‖
  apply Set.Finite.of_finite_image (f := fun a => t * a)
  · apply (Embeddings.finite_of_norm_le E ℂ (K * C)).subset
    rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
    refine ⟨ha1, fun τ => ?_⟩
    rw [map_mul, norm_mul]
    have h1 : ‖τ t‖ ≤ K := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ t‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
    have h2 := ha2 τ
    have h3 : 0 ≤ ‖τ a‖ := norm_nonneg _
    nlinarith [norm_nonneg (τ t)]
  · intro a _ b _ hab
    exact mul_left_cancel₀ ht hab

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MjSmulRight

section

@[expose] public section

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def mj (z x y : S.V) : E := S.hT x y - 2 / S.hT z z * (S.hT x z * S.hT z y)

variable {S}

theorem mj_add_left (z x x' y : S.V) : mj S z (x + x') y = mj S z x y + mj S z x' y := by
  simp only [mj, map_add (f := _), LinearMap.add_apply]
  ring

theorem mj_smul_left (z : S.V) (c : E) (x y : S.V) : mj S z (c • x) y = star c * mj S z x y := by
  simp only [mj, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  ring

theorem mj_add_right (z x y y' : S.V) : mj S z x (y + y') = mj S z x y + mj S z x y' := by
  simp only [mj, map_add (f := _)]
  ring

theorem mj_smul_right (z : S.V) (c : E) (x y : S.V) : mj S z x (c • y) = c * mj S z x y := by
  simp only [mj, map_smul, smul_eq_mul]
  ring

theorem mj_swap (z x y : S.V) : mj S z y x = star (mj S z x y) := by
  have hs : ∀ a b : S.V, star (S.hT a b) = S.hT b a := fun a b => by
    have h := S.herm.eq a b
    rwa [starRingEnd_apply] at h
  simp only [mj, star_sub, star_mul', star_div₀, hs, star_ofNat]
  ring

theorem mj_self_star (z x : S.V) : star (mj S z x x) = mj S z x x := (mj_swap z x x).symm

theorem tau_real {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) {a : E}
    (ha : star a = a) : τ a = ((τ a).re : ℂ) := by
  have h := hstar a
  rw [ha] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm

theorem tau_normSq {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (c : E) :
    τ (star c * c) = (Complex.normSq (τ c) : ℂ) := by
  rw [map_mul, hstar, Complex.normSq_eq_conj_mul_self]

section Pos

variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos

theorem mj_pos (y : S.V) (hy : y ∈ P) :
    0 ≤ (τ (mj S z y y)).re ∧ ((τ (mj S z y y)).re = 0 → y ∈ X) := by
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  set c := S.hT z y / S.hT z z with hc
  set y0 := y - c • z with hy0def
  have h1 : S.hT z y0 = 0 := by
    simp only [y0, map_sub, LinearMap.map_smul, smul_eq_mul, c]
    field_simp; ring
  have hy0 : y0 ∈ P := P.sub_mem hy (P.smul_mem c hzP)
  have h2 : S.hT y0 z = 0 := by rw [herm_swap, h1, star_zero]
  have hm : mj S z y y = S.hT y0 y0 - star c * c * S.hT z z := by
    have hyy : y = y0 + c • z := by simp [y0]
    rw [hyy]
    simp only [mj, map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, h1, h2, starRingEnd_apply, RingHom.id_apply]
    field_simp
    ring
  have hq : 0 ≤ (τ (S.hT y0 y0)).re ∧ ((τ (S.hT y0 y0)).re = 0 → y0 ∈ X) := by
    by_cases hX : y0 ∈ X
    · have : S.hT y0 y0 = 0 := hPX y0 hX y0 hy0
      simp [this, hX]
    · have := hpos y0 hy0 h1 hX
      exact ⟨this.le, fun h => absurd h this.ne'⟩
  have hτ : (τ (mj S z y y)).re = (τ (S.hT y0 y0)).re - Complex.normSq (τ c) * (τ (S.hT z z)).re := by
    rw [hm, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re, Complex.re_ofReal_mul]
  have hns := Complex.normSq_nonneg (τ c)
  refine ⟨by rw [hτ]; nlinarith, fun h0 => ?_⟩
  rw [hτ] at h0
  have hA : Complex.normSq (τ c) * (τ (S.hT z z)).re = 0 := by nlinarith
  have hB : (τ (S.hT y0 y0)).re = 0 := by nlinarith
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact τ.injective (by rw [Complex.normSq_eq_zero.mp h, map_zero])
    · exact absurd h hzz.ne
  have : y = y0 := by simp [y0, hc0]
  rw [this]; exact hq.2 hB

theorem mj_cs (x y : S.V) (hx : x ∈ P) (hy : y ∈ P) :
    Complex.normSq (τ (mj S z x y)) ≤ (τ (mj S z x x)).re * (τ (mj S z y y)).re := by
  have hnn : ∀ s : E, 0 ≤ (τ (mj S z (s • x + y) (s • x + y))).re := fun s =>
    (mj_pos hstar τ X P hPX z hzP hzz hpos _ (P.add_mem (P.smul_mem s hx) hy)).1
  have hexp : ∀ s : E, mj S z (s • x + y) (s • x + y) =
      star s * s * mj S z x x + star s * mj S z x y + s * star (mj S z x y) + mj S z y y := by
    intro s
    rw [mj_add_left, mj_add_right, mj_add_right, mj_smul_left, mj_smul_left, mj_smul_right,
      mj_smul_right, mj_swap z x y]
    ring
  have hareal := tau_real (hstar τ) (mj_self_star z x)
  have ha0 := (mj_pos hstar τ X P hPX z hzP hzz hpos x hx).1
  rcases ha0.lt_or_eq with hapos | hazero
  · have hane : mj S z x x ≠ 0 := by
      intro h; rw [h, map_zero] at hapos; simp at hapos
    have h := hnn (-(mj S z x y) / mj S z x x)
    rw [hexp] at h
    have hval : star (-(mj S z x y) / mj S z x x) * (-(mj S z x y) / mj S z x x) * mj S z x x +
        star (-(mj S z x y) / mj S z x x) * mj S z x y +
        (-(mj S z x y) / mj S z x x) * star (mj S z x y) + mj S z y y =
        mj S z y y - (star (mj S z x y) * mj S z x y) / mj S z x x := by
      rw [star_div₀, star_neg, mj_self_star]
      field_simp
      ring
    rw [hval, map_sub, map_div₀, tau_normSq (hstar τ), hareal, Complex.sub_re] at h
    rw [← Complex.ofReal_div, Complex.ofReal_re] at h
    rw [sub_nonneg, div_le_iff₀ hapos] at h
    linarith
  · have hτa : τ (mj S z x x) = 0 := by rw [hareal, ← hazero]; simp
    have ha : mj S z x x = 0 := τ.injective (by rw [hτa, map_zero])
    rw [← hazero, zero_mul]
    by_contra hlt
    have hpos' : 0 < Complex.normSq (τ (mj S z x y)) := lt_of_not_ge hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ (mj S z y y)).re / (2 * Complex.normSq (τ (mj S z x y))))
    have h := hnn (-(N : E) * mj S z x y)
    rw [hexp, ha] at h
    have hval : star (-(N : E) * mj S z x y) * (-(N : E) * mj S z x y) * 0 +
        star (-(N : E) * mj S z x y) * mj S z x y +
        (-(N : E) * mj S z x y) * star (mj S z x y) + mj S z y y =
        mj S z y y - (2 * (N : E)) * (star (mj S z x y) * mj S z x y) := by
      rw [star_mul, star_neg, star_natCast]
      ring
    rw [hval, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re] at h
    have h2 : (τ (2 * (N : E))) = ((2 * (N : ℝ) : ℝ) : ℂ) := by
      rw [map_mul, map_natCast, map_ofNat]; push_cast; ring
    rw [h2, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith

end Pos

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.IndSetFinite

section

@[expose] public section

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def indSet (X P : Submodule E S.V) (z : S.V) (Λ : Submodule (𝓞 E) S.V) :
    Set ((P ⧸ X.comap P.subtype) → (P ⧸ X.comap P.subtype)) :=
  {φ | ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ γ z = z ∧ (∀ x ∈ Λ, γ x ∈ Λ) ∧
    (∀ x ∈ P, γ x ∈ P) ∧
    ∀ (x : P) (hx : γ x.1 ∈ P), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, hx⟩}

theorem indSet_finite (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
    (hzz : ∀ τ : E →+* ℂ, (τ (S.hT z z)).re < 0)
    (hpos : ∀ τ : E →+* ℂ, ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT x y)) (hzΛ : z ∈ Λ) :
    (indSet X P z Λ).Finite := by
  classical
  set Xc := X.comap P.subtype
  have hzz0 : S.hT z z ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h; have := hzz τ; rw [h, map_zero] at this; simp at this

  set bB := Module.finBasis E P
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • (bB i : S.V) ∈ Λ := fun i => exists_smul_mem Λ hΛ _
  choose d hd0 hdΛ using hd
  have hd0' : ∀ i, algebraMap (𝓞 E) E (d i) ≠ 0 := fun i => by
    rw [ne_eq, ← map_zero (algebraMap (𝓞 E) E), (IsFractionRing.injective (𝓞 E) E).eq_iff]
    exact hd0 i
  set b := bB.unitsSMul (fun i => Units.mk0 _ (hd0' i))
  have hbΛ : ∀ i, ((b i : P) : S.V) ∈ Λ := by
    intro i
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0,
      algebraMap_smul]
    exact hdΛ i

  set cf : Fin (Module.finrank E P) → ℝ := fun i =>
    ∑ τ : E →+* ℂ, |(τ (mj S z (b i : S.V) (b i : S.V))).re| with hcf
  set C : ℝ := ∑ i, cf i with hCdef
  have hC : ∀ i (τ : E →+* ℂ), (τ (mj S z (b i : S.V) (b i : S.V))).re ≤ C := by
    intro i τ
    have h1 : |(τ (mj S z (b i : S.V) (b i : S.V))).re| ≤ cf i :=
      Finset.single_le_sum (f := fun (τ : E →+* ℂ) => |(τ (mj S z (b i : S.V) (b i : S.V))).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have h2 : cf i ≤ C := Finset.single_le_sum (f := cf)
      (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans (h1.trans h2)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

  set Y : Set (P ⧸ Xc) := {q | ∃ y : P, (y : S.V) ∈ Λ ∧
    (∀ τ : E →+* ℂ, (τ (mj S z y y)).re ≤ C) ∧ q = Submodule.Quotient.mk y}

  let mjR : Fin (Module.finrank E P) → S.V →ₗ[E] E := fun j =>
    S.hT (b j : S.V) - (2 / S.hT z z * S.hT (b j : S.V) z) • S.hT z
  have hmjR : ∀ j y, mjR j y = mj S z (b j : S.V) y := by
    intro j y; simp only [mjR, mj, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
  let Pm : P →ₗ[E] (Fin (Module.finrank E P) → E) := LinearMap.pi fun j => (mjR j).comp P.subtype
  have hPm : ∀ (y : P) j, Pm y j = mj S z (b j : S.V) y := by
    intro y j; simp [Pm, hmjR]
  have hker : Xc ≤ LinearMap.ker Pm := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext j
    rw [hPm]
    have h1 : S.hT (b j : S.V) y = 0 := by
      rw [herm_swap, hPX (y : S.V) hy _ (b j).2, star_zero]
    have h2 : S.hT z y = 0 := by rw [herm_swap, hPX (y : S.V) hy _ hzP, star_zero]
    simp [mj, h1, h2]
  let g : (P ⧸ Xc) →ₗ[E] (Fin (Module.finrank E P) → E) := Xc.liftQ Pm hker
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq
    have hw : ∀ j, mj S z (b j : S.V) w = 0 := fun j => by rw [← hPm, hq]; rfl
    have hall : ∀ v : P, mj S z v w = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range b) := by rw [b.span_eq]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hw j
      | zero => simpa using mj_smul_left (S := S) z 0 (0 : S.V) w
      | add x y _ _ h1 h2 => rw [Submodule.coe_add, mj_add_left, h1, h2, add_zero]
      | smul c x _ h => rw [Submodule.coe_smul, mj_smul_left, h, mul_zero]
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hw0 := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) w w.2).2 (by rw [hall w]; simp)
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hw0
  have hYfin : Y.Finite := by
    apply Set.Finite.of_finite_image (f := g) _ hg.injOn
    apply (Set.Finite.pi (t := fun _ => {a : E | IsIntegral ℤ (S.hT z z * a) ∧
      ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}) fun _ => finite_of_integral_bound _ hzz0 C).subset
    rintro _ ⟨q, ⟨y, hyΛ, hyC, rfl⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    have hgj : g (Submodule.Quotient.mk y) j = mj S z (b j : S.V) y := by
      simp only [g, Submodule.liftQ_apply]; exact hPm y j
    rw [hgj]
    constructor
    · have e1 : S.hT z z * mj S z (b j : S.V) y =
          S.hT z z * S.hT (b j : S.V) y - (S.hT (b j : S.V) z * S.hT z y + S.hT (b j : S.V) z * S.hT z y) := by
        simp only [mj]; field_simp; ring
      rw [e1]
      refine IsIntegral.sub (IsIntegral.mul (hint _ hzΛ _ hzΛ) (hint _ (hbΛ j) _ hyΛ))
        (IsIntegral.add (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ))
          (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)))
    · intro τ
      have hcs := mj_cs hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ _ (b j).2 y.2
      have ha := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ (b j).2).1
      have hb := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ y.2).1
      have h1 := hC j τ
      have h2 := hyC τ
      have hsq : ‖τ (mj S z (b j : S.V) y)‖ ^ 2 ≤ C ^ 2 := by
        rw [Complex.sq_norm]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp hsq

  apply Set.Finite.of_finite_image (f := fun φ i => φ (Submodule.Quotient.mk (b i)))
  · apply (Set.Finite.pi (t := fun _ => Y) fun _ => hYfin).subset
    rintro _ ⟨φ, ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨⟨γ (b i : S.V), hγP _ (b i).2⟩, hγΛ _ (hbΛ i), fun τ => ?_, hφ _ _⟩
    have e1 : ∀ x : S.V, S.hT (γ x) z = S.hT x z := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso x z
    have e2 : ∀ x : S.V, S.hT z (γ x) = S.hT z x := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso z x
    have : mj S z (γ (b i : S.V)) (γ (b i : S.V)) = mj S z (b i : S.V) (b i : S.V) := by
      simp only [mj, hiso, e1, e2]
    simp only [this]
    exact hC i τ
  · rintro φ ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩ φ' ⟨γ', hiso', hγz', hγΛ', hγP', hφ'⟩ heq
    let ψ : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ : S.V →ₗ[E] S.V).restrict hγP
    let ψ' : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ' : S.V →ₗ[E] S.V).restrict hγP'
    have hψ : ∀ x : P, φ (Submodule.Quotient.mk x) = ψ x := fun x => by
      rw [hφ x (hγP _ x.2)]; rfl
    have hψ' : ∀ x : P, φ' (Submodule.Quotient.mk x) = ψ' x := fun x => by
      rw [hφ' x (hγP' _ x.2)]; rfl
    have hψψ : ψ = ψ' := b.ext fun i => by
      rw [← hψ, ← hψ']; exact congrFun heq i
    funext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψ, hψ', hψψ]

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end
end
