module

public import Mathlib.RingTheory.Etale.Basic
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
public import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfDirectedUnion

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_model_of_directed_union :
    ∀ (R : Type) [CommRing R] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (Ri : ι → Subring R), Monotone Ri → (∀ x, ∃ i, x ∈ Ri i) →
      ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A],
        ∃ (i : ι) (Ai : Type) (_ : CommRing Ai) (_ : Algebra (Ri i) Ai),
          Algebra.Etale (Ri i) Ai ∧ Nonempty (TensorProduct (Ri i) R Ai ≃ₐ[R] A) := by
  intro R _ ι _ _ _ Ri hmono hcov A _ _ _
  obtain ⟨κ, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := A)).mp
      inferInstance |>.out

  have hfin := P.finite_coeffs
  have hex : ∃ i, P.coeffs ⊆ (Ri i : Set R) := by
    classical
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (hfin.toFinset.image j)
    refine ⟨i, fun x hx ↦ hmono (hi _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx))) (hj x)⟩
  obtain ⟨i, hi⟩ := hex
  letI : Algebra (Ri i) A := ((algebraMap R A).comp (algebraMap (Ri i) R)).toAlgebra
  haveI : IsScalarTower (Ri i) R A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (Ri i) := ⟨fun x hx ↦ ⟨⟨x, hi hx⟩, rfl⟩⟩
  let Q := P.ofHasCoeffs (Ri i)
  refine ⟨i, P.ModelOfHasCoeffs (Ri i), inferInstance, inferInstance, ?_,
    ⟨P.tensorModelOfHasCoeffsEquiv (Ri i)⟩⟩
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Ri i) (P.ModelOfHasCoeffs (Ri i)) :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  infer_instance

end GlobalTheory.EtaleDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnionStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E],
    ∃ (i : ι) (E₀ : Type) (_ : CommRing E₀) (_ : Algebra (Polynomial (𝒜 i)) E₀),
      Algebra.Etale (Polynomial (𝒜 i)) E₀ ∧
      (letI : Algebra (Polynomial (𝒜 i)) (Polynomial T) :=
        (Polynomial.mapRingHom (𝒜 i).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) := by
  intro T _ ι _ _ _ 𝒜 hmono hcov E _ _ _
  let S : ι → Subring (Polynomial T) := fun i ↦ (Polynomial.mapRingHom (𝒜 i).subtype).range
  have hSmono : Monotone S := by
    intro i j hij p hp
    obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
    refine RingHom.mem_range.mpr ⟨q.map (Subring.inclusion (hmono hij)), ?_⟩
    simp only [coe_mapRingHom, Polynomial.map_map]
    rfl
  have hScov : ∀ p, ∃ i, p ∈ S i := by
    classical
    intro p
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (p.support.image (fun n ↦ j (p.coeff n)))
    refine ⟨i, ?_⟩
    have hp : p ∈ Polynomial.lifts (𝒜 i).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ∈ p.support
      · exact ⟨⟨p.coeff n, hmono (hi _ (Finset.mem_image_of_mem _ hn)) (hj _)⟩, rfl⟩
      · rw [Polynomial.notMem_support_iff.mp hn]
        exact ⟨0, map_zero _⟩
    exact RingHom.mem_range.mpr hp
  obtain ⟨i, E₀, _, _, hE₀, ⟨φ⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_directed_union (Polynomial T) ι S hSmono hScov E
  let f : Polynomial (𝒜 i) →+* Polynomial T := Polynomial.mapRingHom (𝒜 i).subtype
  have hf : Function.Injective f := Polynomial.map_injective _ Subtype.val_injective
  let e : Polynomial (𝒜 i) ≃+* S i := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h ↦ hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let alg₀ : Algebra (Polynomial (𝒜 i)) E₀ := ((algebraMap (S i) E₀).comp e.toRingHom).toAlgebra
  let _ : Algebra (Polynomial (𝒜 i)) (Polynomial T) := f.toAlgebra
  have hEt : Algebra.Etale (Polynomial (𝒜 i)) E₀ := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.respectsIso.2 (algebraMap (S i) E₀) e
      (RingHom.etale_algebraMap.mpr hE₀)
  have hmapT (p : Polynomial (𝒜 i)) :
      algebraMap (S i) (Polynomial T) (e p) = algebraMap (Polynomial (𝒜 i)) (Polynomial T) p := rfl
  have hmapE (p : Polynomial (𝒜 i)) :
      algebraMap (S i) E₀ (e p) = algebraMap (Polynomial (𝒜 i)) E₀ p := rfl
  have : SMulCommClass (S i) (Polynomial (𝒜 i)) (Polynomial T) :=
    ⟨fun a b x ↦ by simp only [Algebra.smul_def]; ring⟩
  have : TensorProduct.CompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T) E₀ :=
    ⟨fun p m n ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, ← hmapT, ← hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  have : TensorProduct.CompatibleSMul (Polynomial (𝒜 i)) (S i) (Polynomial T) E₀ :=
    ⟨fun s m n ↦ by
      obtain ⟨p, rfl⟩ := e.surjective s
      rw [Algebra.smul_def, Algebra.smul_def, hmapT, hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  refine ⟨i, E₀, inferInstance, alg₀, hEt, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.equivOfCompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T)
    (Polynomial T) E₀).trans φ
end
end
