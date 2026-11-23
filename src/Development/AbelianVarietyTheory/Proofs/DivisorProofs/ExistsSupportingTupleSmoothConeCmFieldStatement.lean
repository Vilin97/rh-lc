module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionalPosOnSquaresEqSumOfSquaresStatement
import Mathlib.Algebra.AffineMonoid.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedForms

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_avg_proj_balForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  intro O _ bar X _ _ n c b T hc hT hint hsum hpos
  let f : Fin n → X →ₗ[ℤ] X := fun s => DistribSMul.toLinearMap ℤ X (b s)
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := fun β => ∑ s, ∑ t, T s t • β.compl₁₂ (f s) (f t)
      map_add' := fun β γ => by
        ext x y
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun m β => by
        ext x y
        simp [Finset.mul_sum, mul_left_comm] }
  have hP : ∀ β x y, P β x y = ∑ s, ∑ t, T s t * β (b s • x) (b t • y) := by
    intro β x y
    simp [P, f, LinearMap.sum_apply]

  let sp : X → O →ₗ[ℤ] X := fun y => (LinearMap.toSpanSingleton O X y).restrictScalars ℤ
  have hsp : ∀ y u, sp y u = u • y := fun y u => rfl
  have hsumL : ∀ L : O →ₗ[ℤ] ℤ, ∑ s, ∑ t, T s t * L (bar (b s) * b t) = c * L 1 := by
    intro L
    have := congrArg L hsum

    simp only [map_sum, map_zsmul, smul_eq_mul] at this
    rw [this]
    have hc1 : (c : O) = c • (1 : O) := (nsmul_one c).symm
    rw [hc1, map_nsmul, nsmul_eq_mul]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro β hβ
    have key : (∀ y z, P β y z = P β z y) ∧ ∀ (a : O) y z, P β (a • y) z = P β y (bar a • z) := by
      constructor
      · intro x y
        rw [hP, hP, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [hT, hβ]
      · intro a x y
        rw [hP, hP]
        have := hint a (β.compl₁₂ (sp x) (sp y))
        simp only [LinearMap.compl₁₂_apply, hsp, mul_smul] at this
        exact this
    exact key
  · intro β hβ
    obtain ⟨h1, h2⟩ := hβ
    ext x y
    rw [hP]
    have e : ∀ s t, β (b s • x) (b t • y) = (β x ∘ₗ sp y) (bar (b s) * b t) := by
      intro s t
      rw [h2]
      simp [hsp, mul_smul]
    simp only [e]
    rw [hsumL]
    simp [hsp]
  · intro l hl
    have hQ : ∀ x, P (GlobalTheory.PolFan.sqForm l) x x = ∑ s, ∑ t, T s t * (fun s => l (b s • x)) s * (fun s => l (b s • x)) t := by
      intro x
      rw [hP]
      simp [GlobalTheory.PolFan.sqForm_apply, mul_assoc]
    have hnn : ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
      intro x
      rw [hQ]
      by_cases hv : (fun s => l (b s • x)) = 0
      · rw [hv]; simp
      · exact (hpos _ hv).le
    refine ⟨fun h0 => ?_, hnn⟩
    have hv : ∀ y t, l (b t • y) = 0 := by
      intro y t
      by_contra hne
      have hv : (fun s => l (b s • y)) ≠ 0 := fun h => hne (congrFun h t)
      have := hpos _ hv
      rw [← hQ, h0] at this
      simp at this
    obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hl (LinearMap.ext h)
    have := hsumL (l ∘ₗ sp x)
    have hz : ∀ s t, (l ∘ₗ sp x) (bar (b s) * b t) = 0 := by
      intro s t
      simp only [LinearMap.comp_apply, hsp]
      rw [mul_comm, mul_smul]
      exact hv _ _
    simp only [hz, mul_zero, Finset.sum_const_zero] at this
    simp [hsp] at this
    omega

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedFormsStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.exists_averaging_projection_balancedForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  first | exact @GlobalTheory.Poinc.exists_avg_proj_balForms | exact GlobalTheory.Poinc.exists_avg_proj_balForms | (intros; apply GlobalTheory.Poinc.exists_avg_proj_balForms <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmIntegralAveragingTraceTensor

section

@[expose] public section

set_option autoImplicit false

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open NumberField

namespace GlobalTheory

namespace TraceTensor

variable {E : Type} [Field E] [NumberField E]

theorem exists_integral_orthogonal (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (e : Module.Basis (Fin n) ℚ E), (∀ i, e i = (b i : E)) ∧
      ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0 := by
  classical
  let B : LinearMap.BilinForm ℚ E := (Algebra.traceForm ℚ E).comp σ.toLinearMap LinearMap.id
  have hB : ∀ x y, B x y = Algebra.trace ℚ E (σ x * y) := fun _ _ => rfl
  have hs : LinearMap.IsSymm B := ⟨fun x y => by
    rw [RingHom.id_apply, hB, hB, ← Algebra.trace_eq_of_algEquiv σ, map_mul, hσ, mul_comm]⟩
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hint : ∀ y : E, ∃ (m : ℕ) (b : 𝓞 E), m ≠ 0 ∧ (m : ℚ) • y = (b : E) := by
    intro y
    have halg : IsAlgebraic ℤ y :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, b, hm, hb⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    exact ⟨m, b, hm, by rw [Nat.cast_smul_eq_nsmul, hb]⟩
  choose m b hm hb using hint
  have hu : ∀ i, IsUnit ((m (e i) : ℕ) : ℚ) := fun i => IsUnit.mk0 _ (Nat.cast_ne_zero.2 (hm _))
  refine ⟨_, fun i => b (e i), e.isUnitSMul hu, fun i => ?_, fun i j hij => ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, hb]
  · have h : Algebra.trace ℚ E (σ (e i) * e j) = 0 := he hij
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, Rat.smul_def (m (e i) : ℚ), map_mul σ,
      map_ratCast, ← Rat.smul_def, smul_mul_assoc,
      mul_smul_comm, map_smul, map_smul, h, smul_zero, smul_zero]

theorem trace_mul_eq_repr (σ : E ≃ₐ[ℚ] E) {ι : Type} [Fintype ι] (e : Module.Basis ι ℚ E)
    (ho : ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0) (y : E) (i : ι) :
    Algebra.trace ℚ E (σ (e i) * y) = e.repr y i * Algebra.trace ℚ E (σ (e i) * e i) := by

  conv_lhs => rw [← e.sum_repr y, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [mul_smul_comm, map_smul, smul_eq_mul]
  · intro j _ hj
    rw [mul_smul_comm, map_smul, ho i j hj.symm, smul_zero]
  · simp

end TraceTensor


open TraceTensor in
theorem exists_cm_trace_tensor : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (n c : ℕ) (b : Fin n → NumberField.RingOfIntegers E) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c ∧ (∀ s t, T s t = T t s) ∧ (∀ (a : NumberField.RingOfIntegers E) (g : NumberField.RingOfIntegers E →ₗ[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * H.bar a)) ∧ ∑ s, ∑ t, T s t • (H.bar (b s) * b t) = (c : NumberField.RingOfIntegers E) ∧ ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t := by
  intro E _ _ _ H
  classical
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hbar : ∀ x : 𝓞 E, ((H.bar x : 𝓞 E) : E) = σ (x : E) := fun x => H.bar_eq x
  obtain ⟨n, b, e, heb, ho⟩ := exists_integral_orthogonal σ hσσ
  have htr : ∀ x y : 𝓞 E, ((Algebra.trace ℤ (𝓞 E) (H.bar x * y) : ℤ) : ℚ)
      = Algebra.trace ℚ E (σ (x : E) * (y : E)) := by
    intro x y
    rw [Algebra.coe_trace_int, ← hbar]
    rfl
  let d : Fin n → ℤ := fun i => Algebra.trace ℤ (𝓞 E) (H.bar (b i) * b i)
  have hdq : ∀ i, (d i : ℚ) = Algebra.trace ℚ E (σ (e i) * e i) := fun i => by
    rw [heb]; exact htr _ _
  have hdq0 : ∀ i, 0 < Algebra.trace ℚ E (σ (e i) * e i) := fun i =>
    StarNormBound.trace_conj_mul_pos _ (e.ne_zero i)
  have hd : ∀ i, 0 < d i := fun i => by
    have := hdq0 i
    rw [← hdq] at this
    exact_mod_cast this
  let t : Fin n → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  let C : ℤ := ∏ j, d j
  have hC : 0 < C := Finset.prod_pos fun j _ => hd j
  have ht : ∀ i, 0 < t i := fun i => Finset.prod_pos fun j _ => hd j
  have htd : ∀ i, d i * t i = C := fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have htq : ∀ i, (t i : ℚ) = C * (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ := fun i => by
    rw [← hdq, ← htd i]
    have : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    push_cast
    field_simp
  have hexp : ∀ x : 𝓞 E, C • x = ∑ j, (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * x)) • b j := by
    intro x
    apply RingOfIntegers.coe_injective

    rw [map_zsmul, map_sum]
    have hx := e.sum_repr (x : E)
    change C • (x : E) = _
    conv_lhs => rw [← hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    change _ = _ • (b j : E)
    rw [← heb, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_mul, htr, ← heb, trace_mul_eq_repr σ e ho, htq]
    have := (hdq0 j).ne'
    field_simp
  have hsym : ∀ x y a : 𝓞 E, Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a))
      = Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) := by
    intro x y a
    have : ((Algebra.trace ℤ (𝓞 E) (H.bar x * (y * H.bar a)) : ℤ) : ℚ)
      = ((Algebra.trace ℤ (𝓞 E) (H.bar y * (x * a)) : ℤ) : ℚ) := by
      rw [htr, htr, ← Algebra.trace_eq_of_algEquiv σ]
      congr 1
      have h1 : ((y * H.bar a : 𝓞 E) : E) = (y : E) * σ (a : E) := by rw [← hbar]; rfl
      have h2 : ((x * a : 𝓞 E) : E) = (x : E) * (a : E) := rfl
      rw [h1, h2, map_mul, map_mul, hσσ, hσσ]
      ring
    exact_mod_cast this
  refine ⟨n, C.toNat, b, Matrix.diagonal t, by omega, fun s u => ?_, fun a g => ?_, ?_, fun v hv => ?_⟩
  · by_cases h : s = u
    · rw [h]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply mul_left_cancel₀ hC.ne'
    have h1 : ∀ i, C * (t i * g (b i * a) (b i)) =
        ∑ j, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro i
      have : C * g (b i * a) (b i) = g (C • (b i * a)) (b i) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

      rw [mul_left_comm, this, hexp, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ j, C * (t j * g (b j) (b j * H.bar a)) =
        ∑ i, t i * (t j * Algebra.trace ℤ (𝓞 E) (H.bar (b j) * (b i * a))) * g (b j) (b i) := by
      intro j
      have : C * g (b j) (b j * H.bar a) = g (b j) (C • (b j * H.bar a)) := by
        rw [map_smul, smul_eq_mul]

      rw [mul_left_comm, this, hexp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hsym]
      ring
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [h1, h2]
    exact Finset.sum_comm
  · simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hc := StarNormBound.casimir σ e ho fun i => (hdq0 i).ne'
    apply RingOfIntegers.coe_injective

    rw [map_sum, map_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg hC.le, ← mul_one (C : E), ← hc,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_mul]
    change t i • (((H.bar (b i) : 𝓞 E) : E) * (b i : E)) = _
    rw [hbar, ← heb, ← Int.cast_smul_eq_zsmul ℚ, htq, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  · simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [mul_assoc]; exact mul_nonneg (ht j).le (mul_self_nonneg _)
    · rw [mul_assoc]; exact mul_pos (ht i) (mul_self_pos.2 hi)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmIntegralAveragingTraceTensorStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.exists_cm_integral_averaging_traceTensor : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (n c : ℕ) (b : Fin n → NumberField.RingOfIntegers E) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c ∧ (∀ s t, T s t = T t s) ∧ (∀ (a : NumberField.RingOfIntegers E) (g : NumberField.RingOfIntegers E →ₗ[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * H.bar a)) ∧ ∑ s, ∑ t, T s t • (H.bar (b s) * b t) = (c : NumberField.RingOfIntegers E) ∧ ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t := by
  first | exact @GlobalTheory.exists_cm_trace_tensor | exact GlobalTheory.exists_cm_trace_tensor | (intros; apply GlobalTheory.exists_cm_trace_tensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmField

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc NumberField

namespace GlobalTheory.Poinc

theorem exists_supports_cm : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X]
    [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X]
    [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X →
    ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  intro E _ _ _ H φ X _ _ _ _ hP r γ hγ
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  haveI : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨n, c, b, T, hc, hT, hbal, hsum0, hTpos⟩ := GlobalTheory.T.exists_cm_integral_averaging_traceTensor E H
  obtain ⟨P, hPbal, hPc, hPsq⟩ := GlobalTheory.T.exists_averaging_projection_balancedForms (𝓞 E) H.bar X n c b T hc hT hbal hsum0 hTpos
  have hpos : ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < (ℓ ∘ₗ P) (sqForm l) := by
    intro l hl
    obtain ⟨hne, hpsd⟩ := hPsq l hl
    have hb := hPbal (sqForm l) fun x y => by simp [mul_comm]
    have h4 := hP.pos _ hb hpsd hne
    have h5 := h2 _ hb hpsd
    have h6 : (0 : ℝ) < ℓ (P (sqForm l)) := lt_of_lt_of_le (by positivity) h5
    exact_mod_cast h6
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := GlobalTheory.T.functional_pos_on_squares_eq_sum_of_squares X (ℓ ∘ₗ P) hpos
  have key : ∀ β ∈ balForms H.bar X, ∑ i, β (a i) (a i) = ((D * c : ℕ) : ℤ) * ℓ β := by
    intro β hβ
    rw [hsum β hβ.1, LinearMap.comp_apply, hPc β hβ, map_zsmul, smul_eq_mul]
    push_cast; ring
  have hDc : (0 : ℝ) < ((D * c : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hD hc
  refine ⟨N * (D * c), m, a, Nat.mul_pos hN (Nat.mul_pos hD hc),
    ⟨hspan, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩⟩
  · rw [key β hβ]
    have := h2 β hβ hp
    push_cast at this hDc ⊢
    nlinarith
  · rw [key _ (hγ.mem j)]
    push_cast
    rw [h1 j]; ring
  · rw [key β hβ] at he
    refine h3 β hβ hp ?_
    push_cast at he hDc
    have : ((D : ℝ) * c) * (N * φ.evalZ β) = ((D : ℝ) * c) * ℓ β := by rw [← he]; ring
    exact mul_left_cancel₀ hDc.ne' this

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmFieldStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_supportingTuple_smoothCone_cmField : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X] [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  first | exact @GlobalTheory.Poinc.exists_supports_cm | exact GlobalTheory.Poinc.exists_supports_cm | (intros; apply GlobalTheory.Poinc.exists_supports_cm <;> assumption)
end
end
