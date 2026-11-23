module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVB
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.MeanInequalities

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVA

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_dual (φ : 𝓞 E →+ ℤ) :
    ∃ y : E, ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * y) = φ β := by
  classical
  let bZ := NumberField.RingOfIntegers.basis E
  let bQ := NumberField.integralBasis E
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let dB := (Algebra.traceForm ℚ E).dualBasis hnd bQ
  refine ⟨∑ i, (φ (bZ i) : ℚ) • dB i, fun β => ?_⟩
  let f₁ : 𝓞 E →ₗ[ℤ] ℚ :=
    ((Algebra.trace ℚ E).restrictScalars ℤ).comp
      ((LinearMap.mulRight ℚ (∑ i, (φ (bZ i) : ℚ) • dB i)).restrictScalars ℤ ∘ₗ
        (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)
  let f₂ : 𝓞 E →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ.toIntLinearMap
  have hf : f₁ = f₂ := by
    refine bZ.ext fun j => ?_
    simp only [f₁, f₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.mulRight_apply, Algebra.linearMap_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom]

    rw [Finset.mul_sum, map_sum]
    have hb : (algebraMap (𝓞 E) E) (bZ j) = bQ j := (NumberField.integralBasis_apply E j).symm
    rw [hb]
    simp_rw [mul_smul_comm, map_smul]
    have h : ∀ i, Algebra.trace ℚ E (bQ j * dB i) = if j = i then 1 else 0 := fun i => by
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hnd bQ i j
    simp [h]
  have := congrArg (fun g => g β) hf
  simpa [f₁, f₂] using this

abbrev Dual1 (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_dual_of (y : E) (hy : ∀ β : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((β : E) * y) = k) :
    y ∈ Dual1 E := by
  rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  intro a ha
  obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hy β
  refine ⟨k, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, hk]
  simp

theorem one_le_norm_mul (l : E) (hl : l ≠ 0) (hmem : l ∈ Dual1 E * Dual1 E) :
    (1 : ℚ) ≤ |Algebra.norm ℚ l| * ((NumberField.discr E).natAbs : ℚ) ^ 2 := by
  classical
  have hD0 : Dual1 E ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  set dI : FractionalIdeal (𝓞 E)⁰ E :=
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdI
  have hdD : dI * Dual1 E = 1 := by
    rw [hdI, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
    exact inv_mul_cancel₀ hD0
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ Dual1 E * Dual1 E :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hJ : dI * dI * FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ 1 := by
    calc _ ≤ dI * dI * (Dual1 E * Dual1 E) := by first | exact mul_le_mul' le_rfl hle | gcongr
      _ = (dI * Dual1 E) * (dI * Dual1 E) := by ring
      _ = 1 := by rw [hdD, one_mul]
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hn := congrArg FractionalIdeal.absNorm hJe
  rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdI, FractionalIdeal.coeIdeal_absNorm (K := E),
    FractionalIdeal.coeIdeal_absNorm (K := E), NumberField.absNorm_differentIdeal (K := E) (𝒪 := 𝓞 E)] at hn
  have hN0 : Algebra.norm ℚ l ≠ 0 := Algebra.norm_ne_zero_iff.mpr hl
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hpos : ((NumberField.discr E).natAbs : ℚ) * (NumberField.discr E).natAbs
      * |Algebra.norm ℚ l| ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)) (abs_ne_zero.mpr hN0)
  have hJ1 : 1 ≤ Ideal.absNorm J := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm J) with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hn; exact hpos hn.symm
    · exact h0
  have h1 : (1 : ℚ) ≤ Ideal.absNorm J := by exact_mod_cast hJ1
  rw [hn] at h1
  calc (1 : ℚ) ≤ _ := h1
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVC

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem amgm_sum_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ℝ) (hP : 0 ≤ P) (hprod : P ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, a i := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) a (fun _ _ => zero_le_one)
    (by simpa using hn') (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ hn'] at h
  have h2 : P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
    Real.rpow_le_rpow hP hprod (by positivity)
  calc (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹)
      ≤ (Fintype.card ι : ℝ) * (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hn'.le
    _ = (∏ i, a i) ^ ((Fintype.card ι : ℝ)⁻¹) * Fintype.card ι := mul_comm _ _
    _ ≤ ∑ i, a i := h

theorem inv_sq_rpow_inv (D : ℝ) (hD : 0 < D) (n : ℝ) :
    ((D ^ 2)⁻¹) ^ n⁻¹ = ((D ^ n⁻¹) ^ 2)⁻¹ := by
  rw [Real.inv_rpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (D ^ n⁻¹), ← Real.rpow_mul hD.le,
    ← Real.rpow_mul hD.le, mul_comm]

theorem sum_ge_of_prod_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : ℝ) (hD : 0 < D) (hprod : (D ^ 2)⁻¹ ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) / (D ^ ((Fintype.card ι : ℝ)⁻¹)) ^ 2 ≤ ∑ i, a i := by
  have h := amgm_sum_ge a ha _ (by positivity) hprod hn
  rwa [inv_sq_rpow_inv D hD, ← div_eq_mul_inv] at h

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section SlopeTestRemainingChoices
variable {dim : (E →+* ℂ) → ℕ}

theorem smul_add_scalar (β β' : 𝓞 E) (v : Vsp dim) : act (β + β') v = act β v + act β' v := by
  ext i
  simp [act, add_mul]

theorem Hf_add_rightSquareIntegrability (x w w' : Vsp dim) : Hf x (w + w') = Hf x w + Hf x w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left_conj [IsCMField E] (α : 𝓞 E) (v w : Vsp dim) :
    Hf (act α v) w = Hf v (act (IsCMField.ringOfIntegersComplexConj E α) w) := by
  simp only [Hf, act, PiLp.toLp_apply, IsCMField.coe_ringOfIntegersComplexConj,
    IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

end SlopeTestRemainingChoices

theorem sum_sq_norm_ge_of_span [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp X.dim} (hξ : ξ ∈ I) (hξ0 : ξ ≠ 0)
    (k : ℕ) (x u : Fin k → Vsp X.dim) (hxu : ∀ j, x j ∈ X.L ∧ IsU I (x j) (u j))
    (hspan : Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I) :
    2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
  classical

  have hint : ∀ j (β : 𝓞 E), ∃ n : ℤ, (Hf (x j) (act β ξ)).im = n := fun j β =>
    X.integral _ _ (hxu j).1 (hle (hst β ξ hξ))
  let φ : Fin k → 𝓞 E →+ ℤ := fun j => AddMonoidHom.mk' (fun β => (hint j β).choose) (by
    intro β β'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← (hint j (β + β')).choose_spec, ← (hint j β).choose_spec, ← (hint j β').choose_spec,
      smul_add_scalar, Hf_add_rightSquareIntegrability, Complex.add_im])
  have hφ : ∀ j β, ((φ j β : ℤ) : ℝ) = (Hf (x j) (act β ξ)).im := fun j β =>
    ((hint j β).choose_spec).symm

  choose y hy using fun j => exists_dual (φ j)
  have hyR : ∀ j (β : 𝓞 E), ((Algebra.trace ℚ E ((β : E) * y j) : ℚ) : ℝ) = (Hf (x j) (act β ξ)).im := by
    intro j β
    rw [hy j β, ← hφ j β]
    push_cast
    rfl
  have hcs : ∀ j, 2 * ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u j‖ ^ 2 := fun j =>
    cs_bound I hst hξ (x j) (u j) (hxu j).2 (y j) (hyR j)

  set l : E := ∑ j, y j * IsCMField.complexConj E (y j) with hldef
  set a : (E →+* ℂ) → ℝ := fun σ => ∑ j, ‖σ (y j)‖ ^ 2 with hadef
  have ha0 : ∀ σ, 0 ≤ a σ := fun σ => Finset.sum_nonneg fun _ _ => by positivity
  have hσl : ∀ σ : E →+* ℂ, σ l = (a σ : ℂ) := by
    intro σ

    simp only [hldef, hadef, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj']

  have hl : l ≠ 0 := by
    intro hl0
    obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : a σ₀ = 0 := by
      have := hσl σ₀
      rw [hl0, map_zero] at this
      exact_mod_cast this.symm
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
        (Finset.mem_univ j)
      have h3 : σ₀ (y j) = 0 := by simpa using h2
      exact (map_eq_zero_iff σ₀ σ₀.injective).1 h3
    have horth : ∀ w ∈ IR I, inner ℝ w ξ = 0 := by
      intro w hw
      rw [← hspan] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, α, hU⟩ := hw
        rw [hU.2 ξ (Submodule.subset_span hξ), herm_smul_left_conj, ← hyR, hy0 j, mul_zero, map_zero]
        simp
      | zero => simp
      | add w w' _ _ h h' => rw [inner_add_left, h, h', add_zero]
      | smul r w _ h => rw [real_inner_smul_left, h, mul_zero]
    have h4 := horth ξ (Submodule.subset_span hξ)
    rw [real_inner_self_eq_norm_sq] at h4
    have h5 : ‖ξ‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
    exact hξ0 (norm_eq_zero.1 h5)

  have hmemD : ∀ j, y j ∈ Dual1 E := fun j => mem_dual_of (y j) fun β => ⟨φ j β, hy j β⟩
  have htr : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have hmemD' : ∀ j, IsCMField.complexConj E (y j) ∈ Dual1 E := fun j =>
    mem_dual_of _ fun β => by
      refine ⟨φ j (IsCMField.ringOfIntegersComplexConj E β), ?_⟩
      rw [← hy j, IsCMField.coe_ringOfIntegersComplexConj, ← htr, map_mul,
        IsCMField.complexConj_apply_apply]
  have hmem : l ∈ Dual1 E * Dual1 E := by
    rw [hldef, ← FractionalIdeal.mem_coe]
    exact Submodule.sum_mem _ fun j _ =>
      (FractionalIdeal.mem_coe).2 (FractionalIdeal.mul_mem_mul (hmemD j) (hmemD' j))
  have hnorm := one_le_norm_mul l hl hmem

  have hprodC : ((Algebra.norm ℚ l : ℚ) : ℂ) = ((∏ σ, a σ : ℝ) : ℂ) := by
    rw [norm_prod_emb]
    push_cast
    exact Finset.prod_congr rfl fun σ _ => hσl σ
  have hprodR : ((Algebra.norm ℚ l : ℚ) : ℝ) = ∏ σ, a σ := by exact_mod_cast hprodC
  have hP0 : 0 ≤ ∏ σ, a σ := Finset.prod_nonneg fun σ _ => ha0 σ
  set D : ℝ := ((NumberField.discr E).natAbs : ℝ) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact_mod_cast Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  have hprod : (D ^ 2)⁻¹ ≤ ∏ σ, a σ := by
    have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ l : ℚ) : ℝ)| * D ^ 2 := by
      have h1' := (Rat.cast_le (K := ℝ)).2 hnorm
      push_cast at h1'
      rw [hDdef]
      exact h1'
    rw [hprodR, abs_of_nonneg hP0] at h1
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith
  have hcard : Fintype.card (E →+* ℂ) = 2 * PT.f E := by
    rw [NumberField.Embeddings.card, PT.f, IsTotallyComplex.finrank]
    omega
  have hcpos : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have hsum := sum_ge_of_prod_ge a ha0 D hD hprod hcpos
  have hrd : D ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹) = PT.rd E := by
    rw [PT.rd, NumberField.Embeddings.card, one_div, hDdef]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hrd, hcard] at hsum
  push_cast at hsum

  have hξpos : 0 < ‖ξ‖ ^ 2 := by
    have := norm_pos_iff.2 hξ0
    positivity
  have hj : ∀ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 ≤ ‖u j‖ ^ 2 / 2 := by
    intro j
    rw [div_le_iff₀ hξpos]
    linarith [hcs j]
  have hsw : ∑ σ, a σ = ∑ j, ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 := by
    rw [hadef]
    exact Finset.sum_comm
  calc 2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) = (2 * PT.f E / PT.rd E ^ 2) / ‖ξ‖ ^ 2 := by
        rw [div_div]
    _ ≤ (∑ σ, a σ) / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right hsum hξpos.le
    _ = ∑ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 := by
        rw [hsw, Finset.sum_div]
    _ ≤ ∑ j, ‖u j‖ ^ 2 / 2 := Finset.sum_le_sum fun j _ => hj j

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end
