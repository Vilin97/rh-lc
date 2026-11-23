module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfIntegralAtInfinityStatement
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenize

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory

theorem exists_isHomogeneous_dehomogenize : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ),
    T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 →
        aeval a T = aeval (fun j => a j.succ) T₀ := by
  intro D T₀ q hq
  refine ⟨∑ d ∈ Finset.range (q + 1),
    X 0 ^ (q - d) * rename Fin.succ (homogeneousComponent d T₀), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hdq : d ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (isHomogeneous_X_pow (R := ℤ) (0 : Fin (D + 1)) (q - d)).mul
      ((homogeneousComponent_isHomogeneous d T₀).rename_isHomogeneous (f := Fin.succ))
    rwa [Nat.sub_add_cancel hdq] at h
  · intro R _ a ha
    have hsum : ∑ d ∈ Finset.range (q + 1), homogeneousComponent d T₀ = T₀ := by
      conv_rhs => rw [← sum_homogeneousComponent T₀]
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hq)) ?_
      intro x _ hx
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hx
      omega
    conv_rhs => rw [← hsum]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [map_mul, map_pow, aeval_X, ha, one_pow, one_mul, aeval_rename]
    rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenizeStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by
  first | exact @GlobalTheory.exists_isHomogeneous_dehomogenize | exact GlobalTheory.exists_isHomogeneous_dehomogenize | (intros; apply GlobalTheory.exists_isHomogeneous_dehomogenize <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolyringOfIntegralClosureRange

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory

theorem mem_polyring_of_integral_closure_range : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  intro K _ D y hy t ht ι z hz f hf hft
  choose p hp using hz
  set F := Subfield.closure (Set.range y) with hF
  have hsub : ∀ u : K, u ∈ Subring.closure (Set.range y) ↔ ∃ q : MvPolynomial (Fin D) ℤ, aeval y q = u := by
    intro u
    have e1 : u ∈ Subring.closure (Set.range y) ↔ u ∈ Algebra.adjoin ℤ (Set.range y) := by
      rw [Algebra.adjoin_int]; rfl
    rw [e1, Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hmem : ∀ q : MvPolynomial (Fin D) ℤ, aeval y q ∈ F := by
    intro q
    exact Subfield.subring_closure_le _ ((hsub _).mpr ⟨q, rfl⟩)
  let φ : MvPolynomial (Fin D) ℤ →+* F := (aeval y).toRingHom.codRestrict F hmem
  letI : Algebra (MvPolynomial (Fin D) ℤ) F := φ.toAlgebra
  have hφ : ∀ q, ((algebraMap (MvPolynomial (Fin D) ℤ) F q : F) : K) = aeval y q := fun q => rfl
  have hinj : Function.Injective (aeval y : MvPolynomial (Fin D) ℤ →ₐ[ℤ] K) :=
    algebraicIndependent_iff_injective_aeval.mp hy
  haveI : FaithfulSMul (MvPolynomial (Fin D) ℤ) F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinj
    rw [← hφ a, ← hφ b, h]
  haveI : IsFractionRing (MvPolynomial (Fin D) ℤ) F := by
    refine IsFractionRing.of_field _ _ ?_
    intro w
    obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp w.2
    obtain ⟨a, ha⟩ := (hsub u).mp hu
    obtain ⟨b, hb⟩ := (hsub v).mp hv
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    simp only [Subfield.coe_div, hφ, ha, hb, huv]
  haveI : IsIntegrallyClosed (MvPolynomial (Fin D) ℤ) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hcomp : (aeval y).toRingHom.comp (bind₁ p).toRingHom = (aeval z).toRingHom := by
    refine RingHom.ext fun q => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_bind₁]
    have : (fun i => aeval y (p i)) = z := funext hp
    rw [this]
  let t' : F := ⟨t, ht⟩
  have hint : IsIntegral (MvPolynomial (Fin D) ℤ) t' := by
    refine ⟨f.map (bind₁ p).toRingHom, hf.map _, ?_⟩
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ (f.map (bind₁ p).toRingHom) (algebraMap (MvPolynomial (Fin D) ℤ) F) F.subtype t'
    show F.subtype (Polynomial.eval₂ _ t' _) = F.subtype 0
    rw [h1, map_zero]
    have h2 : F.subtype.comp (algebraMap (MvPolynomial (Fin D) ℤ) F) = (aeval y).toRingHom := by
      exact RingHom.ext fun q => rfl
    rw [h2, Polynomial.eval₂_map, hcomp]
    exact hft
  obtain ⟨T₀, hT⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨T₀, by rw [← hφ, hT]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolyringOfIntegralClosureRangeStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.mem_polyring_of_integral_closure_range' : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  first | exact @GlobalTheory.mem_polyring_of_integral_closure_range | exact GlobalTheory.mem_polyring_of_integral_closure_range | (intros; apply GlobalTheory.mem_polyring_of_integral_closure_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMonicOverMvPolynomial

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory

theorem trace_monic_over_mvPolynomial {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K]
    {ι : Type} (z : ι → K) (hz : ∀ i, z i ∈ F) (v : K)
    (hv : IsIntegral (Subring.closure (Set.range z)) v) :
    ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧
      f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  set φ : MvPolynomial ι ℤ →+* K := (aeval z).toRingHom with hφdef
  set S : Subring K := Subring.closure (Set.range z) with hSdef
  have hφF : ∀ p, φ p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using F.intCast_mem a
    | add p q hp hq => simpa [map_add (f := _)] using F.add_mem hp hq
    | mul_X p i hp => simpa [map_mul, hφdef] using F.mul_mem hp (hz i)
  have hφS : ∀ p, φ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using S.intCast_mem a
    | add p q hp hq => simpa [map_add (f := _)] using S.add_mem hp hq
    | mul_X p i hp =>
        simpa [map_mul, hφdef] using S.mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  let ψ : MvPolynomial ι ℤ →+* F := φ.codRestrict F hφF
  let θ : MvPolynomial ι ℤ →+* S := φ.codRestrict S hφS
  letI : Algebra (MvPolynomial ι ℤ) K := φ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) F := ψ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) S := θ.toAlgebra
  haveI : IsScalarTower (MvPolynomial ι ℤ) F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial ι ℤ) S K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hθsurj : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    have hle : S ≤ φ.range := by
      rw [hSdef, Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨X i, by simp [hφdef]⟩
    obtain ⟨p, hp⟩ := hle hs
    exact ⟨p, Subtype.ext hp⟩
  haveI : Algebra.IsIntegral (MvPolynomial ι ℤ) S :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hθsurj
  have hvP : IsIntegral (MvPolynomial ι ℤ) v := isIntegral_trans v hv
  have hT : IsIntegral (MvPolynomial ι ℤ) (Algebra.trace F K v) := Algebra.isIntegral_trace hvP
  obtain ⟨f, hfm, hf⟩ := hT
  refine ⟨f, hfm, ?_⟩
  have h := congrArg F.subtype hf
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMonicOverMvPolynomialStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  first | exact @GlobalTheory.trace_monic_over_mvPolynomial | exact GlobalTheory.trace_monic_over_mvPolynomial | (intros; apply GlobalTheory.trace_monic_over_mvPolynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIntTraceSectionTuple

section

@[expose] public section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TraceHom

theorem trace_homog : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (q : ℕ) (w : K), (∀ l, IsIntegral (ratR x l) (w / x l ^ q)) →
    ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) = aeval (fun l => x l / x 0) T := by
  intro K _ _ D x hx hind hfd q w hint
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  have hyF : ∀ j, y j ∈ ratF x := fun j => Subfield.subset_closure ⟨j, rfl⟩
  have hzF : ∀ l k, x k / x l ∈ ratF x := by
    intro l k
    have e : ∀ k, x k / x 0 ∈ ratF x := by
      intro k
      refine Fin.cases ?_ (fun i => hyF i) k
      rw [div_self (hx 0)]; exact one_mem _
    have : x k / x l = (x k / x 0) / (x l / x 0) := by field_simp [hx 0, hx l]
    rw [this]; exact div_mem (e k) (e l)
  set t : K := (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) with htdef

  obtain ⟨f₀, hf₀, hft₀⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x 0) (hzF 0) _ (hint 0)
  have hz0 : ∀ k, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = x k / x 0 := by
    intro k
    refine Fin.cases ⟨1, ?_⟩ (fun i => ⟨X i, by simp [y]⟩) k
    rw [map_one, div_self (hx 0)]
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.mem_polyring_of_integral_closure_range' y hind t (Algebra.trace (ratF x) K (w / x 0 ^ q)).2 _ hz0 f₀ hf₀ hft₀

  have hdeg : T₀.totalDegree ≤ q := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [MvPolynomial.eq_C_of_isEmpty T₀, totalDegree_C]; exact Nat.zero_le _
    · set j : Fin D := ⟨0, hD⟩
      have hyj : y j ≠ 0 := div_ne_zero (hx _) (hx 0)
      obtain ⟨f₁, hf₁, hft₁⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x j.succ) (hzF j.succ) _ (hint j.succ)
      have hc : (⟨(x 0 / x j.succ) ^ q, pow_mem (hzF _ 0) q⟩ : ratF x) • (w / x 0 ^ q) = w / x j.succ ^ q := by
        rw [Subfield.smul_def]; simp only [smul_eq_mul, div_pow]; field_simp [hx 0, hx j.succ] <;> ring
      have htr : (Algebra.trace (ratF x) K (w / x j.succ ^ q) : K) = aeval y T₀ / y j ^ q := by
        rw [← hc, LinearMap.map_smul, smul_eq_mul, Subfield.coe_mul, ← htdef, hT₀]
        simp only [y, j, div_pow]; field_simp [hx 0, hx _] <;> ring
      rw [htr] at hft₁
      refine GlobalTheory.T.totalDegree_le_of_root_of_monic_eval y hind j hyj T₀ q _ ?_ f₁ hf₁ hft₁
      intro k
      refine Fin.cases ⟨1, 1, by simp, ?_⟩ (fun i => ⟨1, X i, ?_, ?_⟩) k
      · simp only [y, pow_one, map_one]; field_simp [hx 0, hx _]
      · simp [totalDegree_X]
      · simp only [y, pow_one, aeval_X]; field_simp [hx 0, hx _]
  obtain ⟨T, hT, hTa⟩ := GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one T₀ q hdeg
  refine ⟨T, hT, ?_⟩
  rw [hTa K _ (div_self (hx 0)), ← hT₀]

end GlobalTheory.HSAmp.TraceHom
end
end
