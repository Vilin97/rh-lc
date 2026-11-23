module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGDiff
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGTheta
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
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGXi

section

@[expose] public section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem xi_den (E : Type) [Field E] [NumberField E] : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ η : E,
    (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (η * a) = z) → ∃ b : 𝓞 E, (b : E) = c * η := by
  obtain ⟨c, hc, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)).prop
  refine ⟨c, nonZeroDivisors.ne_zero hc, fun η hη => ?_⟩
  have hm : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := hη b
    exact ⟨z, hz.symm⟩
  obtain ⟨b, hb⟩ := h η hm
  exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb⟩

theorem xi_rep (E : Type) [Field E] [NumberField E] (lam : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ η : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (η * a) = lam a := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (lam (RingOfIntegers.basis E i) : ℚ)
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f, fun a => ?_⟩
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  have h : (f.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 E) E).toLinearMap
      = (Algebra.linearMap ℤ ℚ).comp lam := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    show f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [← integralBasis_apply]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun h a

theorem tw_g_xi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ ξ : E, IsCMField.complexConj E ξ = -ξ ∧ (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (ξ * a) = z) ∧ ∀ lam : 𝓞 E →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : 𝓞 E), ¬ (p : ℤ) ∣ m ∧ ∀ a : 𝓞 E, ((m * lam a : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * b * a) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨c0, hc0, hden⟩ := xi_den E
  have hbb := bar_bar bar hbar
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  set c : 𝓞 E := c0 * bar c0 with hc
  have hc' : c ≠ 0 := mul_ne_zero hc0 (by simpa using hc0)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc'
  have hcb : IsCMField.complexConj E (c : E) = c := by
    rw [← hbar, hc, map_mul, hbb, mul_comm]
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z}
      add_mem' := fun {x y} hx hy a => by
        obtain ⟨z, hz⟩ := hx a
        obtain ⟨w, hw⟩ := hy a
        exact ⟨z + w, by push_cast; rw [add_div, add_mul, map_add (f := _), hz, hw]⟩
      zero_mem' := fun a => ⟨0, by simp⟩
      smul_mem' := fun r y hy a => by
        obtain ⟨z, hz⟩ := hy (r * a)
        refine ⟨z, ?_⟩
        rw [← hz]
        congr 1
        rw [smul_eq_mul]
        push_cast
        ring }
  have hmem : ∀ y : 𝓞 E, y ∈ I ↔ ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z :=
    fun _ => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : c ∈ I := (hmem c).2 fun a => ⟨Algebra.trace ℤ (𝓞 E) a, by
      rw [div_self hcE, one_mul, Algebra.coe_trace_int]⟩
    rw [h] at this
    exact hc' this
  have hI : ∀ y ∈ I, bar y ∈ I := by
    intro y hy
    refine (hmem _).2 fun a => ?_
    obtain ⟨z, hz⟩ := (hmem y).1 hy (bar a)
    refine ⟨z, ?_⟩
    rw [← hz, ← htr ((y : E) / c * _), map_mul (IsCMField.complexConj E), map_div₀, hcb, ← hbar, ← hbar, hbb]
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨x, hxI, hx⟩ := anti_ded bar hbb I hI0 hI (tw_g_diff E bar hbar hun) (p : 𝓞 E) hp0
  have hxI' : x - bar x ∈ I := sub_mem hxI (hI x hxI)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x - bar x} := Ideal.dvd_span_singleton.2 hxI'
  have hm : ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ (m : 𝓞 E) ∈ J := by
    by_contra hne
    push Not at hne
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨Q, hJQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E)
      (Ideal.span {(p : ℤ)}) J (by
        intro m hm
        rw [Ideal.mem_span_singleton]
        by_contra h
        exact hne m h (by simpa using hm))
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQp]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp0 hpQ
    refine hx Q (hQ.isMaximal hQ0) hpQ ?_
    have : x - bar x ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self _
    rw [mul_comm Q]
    exact Ideal.mul_mono_right hJQ this
  obtain ⟨m, hmp, hmJ⟩ := hm
  refine ⟨((x - bar x : 𝓞 E) : E) / c, ?_, (hmem _).1 hxI', fun lam => ?_⟩
  · rw [map_div₀, hcb, ← hbar, map_sub, hbb]
    push_cast
    ring
  · obtain ⟨η, hη⟩ := xi_rep E lam
    obtain ⟨b, hb⟩ := hden η fun a => ⟨lam a, hη a⟩
    have hy : ((bar c0 * b : 𝓞 E) : E) / c = η := by
      rw [div_eq_iff hcE, hc]
      have e1 : ((bar c0 * b : 𝓞 E) : E) = (bar c0 : 𝓞 E) * (b : E) := rfl
      have e2 : ((c0 * bar c0 : 𝓞 E) : E) = (c0 : E) * (bar c0 : 𝓞 E) := rfl
      rw [e1, e2, hb]
      ring
    have hyI : bar c0 * b ∈ I := (hmem _).2 fun a => ⟨lam a, by rw [hy, hη]⟩
    have h2 : bar c0 * b * m ∈ Ideal.span {x - bar x} := hJ ▸ Ideal.mul_mem_mul hyI hmJ
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.1 h2
    refine ⟨m, β, hmp, fun a => ?_⟩
    have h3 : ((x - bar x : 𝓞 E) : E) / c * β * a = (m : ℚ) • (η * a) := by
      have h4 : ((bar c0 * b : 𝓞 E) : E) * m = ((x - bar x : 𝓞 E) : E) * β := by
        have := congrArg (algebraMap (𝓞 E) E) hβ
        rw [map_mul _ (bar c0 * b), map_intCast, map_mul _ _ β] at this
        exact this
      rw [← hy, Int.cast_smul_eq_zsmul, zsmul_eq_mul, div_mul_eq_mul_div, ← h4]
      ring
    rw [h3, map_smul, hη]
    simp

end PositivityTheory.UnitarySelfGeneration
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGLam

section

@[expose] public section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem trace_form_mulLeft_bijective (B Z : Type) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B] [CommRing Z]
    (l : B →ₗ[ℤ] ℤ) (h : ∀ f : B →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : B), IsUnit (m : Z) ∧ ∀ a, m * f a = l (b * a))
    (L : Z ⊗[ℤ] B →ₗ[Z] Z) (hL : ∀ z a, L (z ⊗ₜ a) = z * l a) :
    Function.Bijective (fun r : Z ⊗[ℤ] B => L.comp (LinearMap.mulLeft Z r)) := by
  classical
  let T : Z ⊗[ℤ] B →ₗ[Z] Module.Dual Z (Z ⊗[ℤ] B) := (LinearMap.mul Z (Z ⊗[ℤ] B)).compr₂ L
  show Function.Bijective T
  let b := Module.Free.chooseBasis ℤ B
  let bZ := Algebra.TensorProduct.basis Z b
  have hs : Function.Surjective T := by
    intro f
    choose m β hu hm using fun i => h (b.coord i)
    refine ⟨∑ i, (f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i, bZ.ext fun j => ?_⟩

    rw [map_sum, LinearMap.sum_apply]
    have h1 : ∀ i, T ((f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i) (bZ j) = if j = i then f (bZ i) else 0 := by
      intro i
      have h2 : bZ j = 1 ⊗ₜ b j := Algebra.TensorProduct.basis_apply _ _
      show L (_ * bZ j) = _
      rw [h2, Algebra.TensorProduct.tmul_mul_tmul, hL, ← hm, mul_one, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · rw [mul_one, mul_assoc, IsUnit.val_inv_mul, mul_one]
      · simp
    simp [h1]
  refine ⟨?_, hs⟩
  have := OrzechProperty.injective_of_surjective_endomorphism (bZ.toDualEquiv.symm.toLinearMap.comp T)
    (bZ.toDualEquiv.symm.surjective.comp hs)
  exact Function.Injective.of_comp this

theorem tw_g_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime], ∃ lam : (ℤ_[p] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[p]] ℤ_[p], (∀ r, lam (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = -lam r) ∧ Function.Bijective (fun r : ℤ_[p] ⊗[ℤ] 𝓞 E => lam.comp (LinearMap.mulLeft ℤ_[p] r)) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨ξ, h1, h2, h3⟩ := tw_g_xi E bar hbar hun p hp.out
  choose l0 hl0 using h2
  let l : 𝓞 E →ₗ[ℤ] ℤ := (AddMonoidHom.mk' l0 fun a b => by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← hl0, ← hl0, ← hl0, ← map_add (f := _), ← mul_add]
    rfl).toIntLinearMap
  have hl : ∀ a, (l a : ℚ) = Algebra.trace ℚ E (ξ * a) := fun a => (hl0 a).symm
  let L : ℤ_[p] ⊗[ℤ] 𝓞 E →ₗ[ℤ_[p]] ℤ_[p] :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap.comp (l.baseChange ℤ_[p])
  have hL : ∀ z a, L (z ⊗ₜ a) = z * l a := by
    intro z a
    simp [L, mul_comm]
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  have hlb : ∀ a, l (bar a) = -l a := by
    intro a
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hl, hl, ← htr, map_mul, h1, hbar, IsCMField.complexConj_apply_apply, neg_mul, map_neg]
  refine ⟨L, fun r => ?_, trace_form_mulLeft_bijective _ _ l (fun f => ?_) L hL⟩
  · induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, hL, hL]
      show z * (l (bar a) : ℤ_[p]) = _
      rw [hlb]
      push_cast
      ring
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, neg_add]
  · obtain ⟨m, b, hm, hb⟩ := h3 f
    refine ⟨m, b, ?_, fun a => ?_⟩
    · rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hm ((PadicInt.norm_int_lt_one_iff_dvd m).1 h))
    · apply Int.cast_injective (α := ℚ)
      rw [hb, hl, mul_assoc]
      rfl

end PositivityTheory.UnitarySelfGeneration
end
end
