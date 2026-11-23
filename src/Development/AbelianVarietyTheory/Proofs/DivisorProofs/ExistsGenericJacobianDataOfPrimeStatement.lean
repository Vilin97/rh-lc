module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparating

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparatingStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGeneratorsStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_minimal_local_generators' : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime], ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧ ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by
  first | exact @GlobalTheory.exists_minimal_local_generators | exact GlobalTheory.exists_minimal_local_generators | (intros; apply GlobalTheory.exists_minimal_local_generators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMemStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  first | exact @GlobalTheory.mem_sq_localization_of_pderiv_mem | exact GlobalTheory.mem_sq_localization_of_pderiv_mem | (intros; apply GlobalTheory.mem_sq_localization_of_pderiv_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_generic_jacobian_data_of_prime (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ]
    (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime] (hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) :
    ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ),
      g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
      (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  classical
  obtain ⟨h, f, g, hgQ, hfQ, hgen, -, hmin⟩ := GlobalTheory.T.exists_minimal_local_generators' (MvPolynomial σ Λ) Q

  set φ : MvPolynomial σ Λ →+* FractionRing (MvPolynomial σ Λ ⧸ Q) :=
    (algebraMap (MvPolynomial σ Λ ⧸ Q) (FractionRing (MvPolynomial σ Λ ⧸ Q))).comp
      (Ideal.Quotient.mk Q) with hφ
  have hφker : ∀ x, φ x = 0 ↔ x ∈ Q := by
    intro x
    rw [hφ, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective _ _)

  have hind : ∀ a : Fin h → FractionRing (MvPolynomial σ Λ ⧸ Q),
      (∀ t, ∑ j, a j * φ (MvPolynomial.pderiv t (f j)) = 0) → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial σ Λ ⧸ Q)) a
    choose c hc using fun j => RingHom.mem_rangeS.mp (hb j)
    choose a' ha' using fun j => Ideal.Quotient.mk_surjective (c j)
    have hφa : ∀ j, φ (a' j) =
        algebraMap _ (FractionRing (MvPolynomial σ Λ ⧸ Q)) (b : MvPolynomial σ Λ ⧸ Q) * a j := by
      intro j
      rw [hφ, RingHom.comp_apply, ha', hc, Algebra.smul_def]
    have hx : ∑ j, a' j * f j ∈ Q := Q.sum_mem fun j _ => Q.mul_mem_left _ (hfQ j)
    have hpd : ∀ t, MvPolynomial.pderiv t (∑ j, a' j * f j) ∈ Q := by
      intro t

      rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
      refine Q.add_mem ?_ (Q.sum_mem fun j _ => Q.mul_mem_right _ (hfQ j))

      rw [← hφker, map_sum]
      simp only [map_mul, hφa, mul_assoc, ← Finset.mul_sum, ha t, mul_zero]
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem Λ σ Q hQ _ hx hpd
    have haQ := hmin a' u hu hux
    funext j
    have h1 : φ (a' j) = 0 := (hφker _).mpr (haQ j)
    rw [hφa j] at h1
    exact (mul_eq_zero.mp h1).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_det_ne_zero_of_separating_functionals (FractionRing (MvPolynomial σ Λ ⧸ Q)) σ h
    (fun t j => φ (MvPolynomial.pderiv t (f j))) hind
  refine ⟨h, f, s, g, hgQ, hfQ, hgen, fun hdet => hs ?_⟩
  have hmat : (Matrix.of fun i j => φ (MvPolynomial.pderiv (s i) (f j))) =
      φ.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)) := by
    ext i j
    simp
  rw [hmat, ← RingHom.map_det, hφker]
  exact hdet

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_local_generators_jacobian_det_not_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_of_prime | exact GlobalTheory.exists_generic_jacobian_data_of_prime | (intros; apply GlobalTheory.exists_generic_jacobian_data_of_prime <;> assumption)
end
end
