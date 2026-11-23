module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGLStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuationsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompact

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharpolyInt

theorem charpoly_coeff_det_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) :
    (∀ k, A.charpoly.coeff k ∈ w.adicCompletionIntegers E) ∧ A.det ∈ w.adicCompletionIntegers E := by
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hMA : M.map (w.adicCompletionIntegers E).subtype = A := by ext i j; rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hMA, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff k).2
  · have hdet : A.det = ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) := by
      rw [← hMA]; exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M).symm
    rw [hdet]; exact M.det.2

theorem entries_int_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    (∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (g⁻¹).1 i j ∈ w.adicCompletionIntegers E := by
  simp only [GlobalTheory.LFun.KGL] at hg
  unfold GLint at hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (bc (Ov E w).subtype h).1 i j = ((h.1 i j : Ov E w) : w.adicCompletion E) := rfl
    rw [this]; exact (h.1 i j).2
  · have : ((bc (Ov E w).subtype h)⁻¹).1 i j = (((h⁻¹).1 i j : Ov E w) : w.adicCompletion E) := by
      rw [← map_inv]; rfl
    rw [this]; exact ((h⁻¹).1 i j).2

theorem kint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    g ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  intro E _ _ _ n w g hg
  obtain ⟨h1, h2⟩ := entries_int_of_mem_KGL w n g hg
  obtain ⟨hc, hd⟩ := charpoly_coeff_det_int w g.val h1
  obtain ⟨-, hd'⟩ := charpoly_coeff_det_int w (g⁻¹).val h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd hd'
  refine ⟨fun k => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc k), ?_⟩
  have hprod : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by rw [← map_mul, hprod, map_one]
  have hdet : Valued.v g.val.det = 1 := by
    refine le_antisymm hd ?_
    calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := hv.symm
      _ ≤ Valued.v g.val.det * 1 := mul_le_mul' le_rfl hd'
      _ = Valued.v g.val.det := mul_one _
  have h0 : g.val.charpoly.coeff 0 = (-1) ^ Fintype.card (Fin n) * g.val.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hdet]

end GlobalTheory.CharpolyInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompactStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w), g ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  first | exact @GlobalTheory.CharpolyInt.kint | exact GlobalTheory.CharpolyInt.kint | (intros; apply GlobalTheory.CharpolyInt.kint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

theorem ell_coeff_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  intro E _ _ _ n P hP
  have hdeg : P.natDegree = n := hP.2.1
  obtain ⟨h0, hid⟩ := ell_conj_selfRecip E n P hP
  refine ⟨h0, fun k hk => ?_⟩
  have hc := congrArg (fun Q : E[X] => Q.coeff k) hid
  simp only [coeff_C_mul, coeff_reverse] at hc
  have hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]
  rw [hnd, revAt_le hk, coeff_map] at hc
  have hc2 := congrArg (IsCMField.complexConj E) hc
  simpa [map_mul] using hc2

end GlobalTheory.ConjSelfRecip
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeffStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  first | exact @GlobalTheory.ConjSelfRecip.ell_coeff_conj | exact GlobalTheory.ConjSelfRecip.ell_coeff_conj | (intros; apply GlobalTheory.ConjSelfRecip.ell_coeff_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEq

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  first | exact @GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq | exact GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq | (intros; apply GlobalTheory.BCT.valuation_eq_or_eq_conj_of_under_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSection

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinChar

theorem norm_coeff_le_of_mem_ell (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) (k : ℕ) :
    ‖τ (P.coeff k)‖ ≤ (2 : ℝ) ^ n := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) k hm (IsAlgClosed.splits _) (fun z hz => (hr τ z hz).le)
  rw [Polynomial.coeff_map, one_pow, one_mul, hd] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow n k)

theorem finite_ell_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ n S hS C hC hK
  set T := {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P} with hT
  choose σ hσ using fun w => (hS w).exists
  choose B hB using fun w => GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL E n w (C w) (hC w)
  have loc : ∀ P ∈ T, ∀ u ∈ S, (∀ k, u.valuation E (P.coeff k) ≤ B u) ∧ u.valuation E (P.coeff 0)⁻¹ ≤ B u ∧
      (C u ⊆ GlobalTheory.LFun.KGL u (n := n) → (∀ k, u.valuation E (P.coeff k) ≤ 1) ∧ u.valuation E (P.coeff 0) = 1) := by
    intro P hP u hu
    obtain ⟨g, hg, hgP⟩ := hP.2 u hu
    have e : ∀ k, u.valuation E (P.coeff k) = Valued.v (g.val.charpoly.coeff k) := fun k => by
      rw [hgP, Polynomial.coeff_map]; exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).symm
    refine ⟨fun k => (e k).trans_le ((hB u g hg).1 k), ?_, fun hsub => ?_⟩
    · rw [map_inv₀, e, ← map_inv₀]; exact (hB u g hg).2
    · have := GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact E n u g (hsub hg)
      exact ⟨fun k => (e k).trans_le (this.1 k), (e 0).trans this.2⟩
  have glob : ∀ P ∈ T, ∀ w : Pl E, ∀ k, w.valuation E (P.coeff k) ≤ max (B (σ w)) (B (σ w) * B (σ w)) ∧
      (C (σ w) ⊆ GlobalTheory.LFun.KGL (σ w) (n := n) → w.valuation E (P.coeff k) ≤ 1) := by
    intro P hP w k
    have hu := loc P hP (σ w) (hσ w).1
    obtain ⟨h0, hc⟩ := GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff E n P hP.1
    rcases GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq E w (σ w) (hσ w).2 with h | h
    · rw [h]
      exact ⟨(hu.1 k).trans (le_max_left _ _), fun hs => (hu.2.2 hs).1 k⟩
    · rw [h]
      by_cases hk : k ≤ n
      · have e : IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) * (P.coeff 0)⁻¹ := by
          rw [← hc k hk]; field_simp
        rw [e, map_mul]
        refine ⟨(mul_le_mul' (hu.1 _) hu.2.1).trans (le_max_right _ _), fun hs => ?_⟩
        rw [map_inv₀, (hu.2.2 hs).2, inv_one, mul_one]; exact (hu.2.2 hs).1 _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega), map_zero, map_zero]
        exact ⟨zero_le', fun _ => zero_le'⟩
  set A := {x : E | ∃ P ∈ T, ∃ k, P.coeff k = x} with hA
  have hAfin : A.Finite := by
    refine GlobalTheory.T.finite_of_bounded_embeddings_and_valuations E A ((2 : ℝ) ^ n) ?_ ?_ ?_
    · rintro _ ⟨P, hP, k, rfl⟩ τ; exact norm_coeff_le_of_mem_ell E n P hP.1 τ k
    · intro w; exact ⟨_, by rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).1⟩
    · have hbad : {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)}.Finite := Filter.eventually_cofinite.1 hK
      have : {w : Pl E | ¬ ∀ x ∈ A, w.valuation E x ≤ 1} ⊆ ⋃ u ∈ {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)},
          {w : Pl E | w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))} := by
        intro w hw
        simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hw ⊢
        refine ⟨σ w, fun hs => hw ?_, (hσ w).2.symm⟩
        rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).2 hs
      refine Filter.eventually_cofinite.2 (Set.Finite.subset (hbad.biUnion fun u _ => ?_) this)
      exact ((IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E)).preimage
        (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Set.Finite.of_finite_image (f := fun P : E[X] => fun k : Fin (n + 1) => P.coeff k) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => A) fun _ => hAfin).subset ?_
    rintro _ ⟨P, hP, rfl⟩ k _
    exact ⟨P, hP, k, rfl⟩
  · intro P hP Q hQ h
    ext k
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.FinChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSectionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_ellipticCharpoly_compact_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinChar.finite_ell_charpoly | exact GlobalTheory.FinChar.finite_ell_charpoly | (intros; apply GlobalTheory.FinChar.finite_ell_charpoly <;> assumption)
end
end
