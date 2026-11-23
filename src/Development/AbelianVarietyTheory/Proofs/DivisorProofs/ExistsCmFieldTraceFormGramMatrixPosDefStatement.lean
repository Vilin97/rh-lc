module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.AffineMonoid.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited

section

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatticeBoundTests
open NumberField

section Trace
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def trBil : 𝓞 E →ₗ[ℤ] 𝓞 E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_assoc, mul_add])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_add, mul_left_comm])

omit [IsCMField E] in
theorem trBil_apply (x y : 𝓞 E) :
    trBil E x y = ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re := rfl

omit [IsCMField E] in
theorem trBil_symm (x y : 𝓞 E) : trBil E x y = trBil E y x := by
  rw [trBil_apply, trBil_apply]
  exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]

omit [IsCMField E] in
theorem trBil_posDef :
    (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i) (RingOfIntegers.basis E j)).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, trBil_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]
  · set u : (E →+* ℂ) → ℂ := fun σ => ∑ i, (t i : ℂ) * σ (RingOfIntegers.basis E i : E) with hu
    have key : star t ⬝ᵥ (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i)
        (RingOfIntegers.basis E j)).mulVec t = ∑ σ, Complex.normSq (u σ) := by
      have : ∀ σ, Complex.normSq (u σ) = ∑ i, ∑ j, t i * ((σ (RingOfIntegers.basis E i : E) *
          starRingEnd ℂ (σ (RingOfIntegers.basis E j : E))).re * t j) := by
        intro σ
        rw [← Complex.ofReal_re (Complex.normSq (u σ)), ← Complex.mul_conj, hu]

        simp only [map_sum, Finset.sum_mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp; ring
      simp only [this, dotProduct, Matrix.mulVec, Matrix.of_apply, trBil_apply, star_trivial,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (γ := E →+* ℂ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm (γ := E →+* ℂ)]
    rw [key]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => ht ?_
    have hz : ∀ σ, u σ = 0 := fun σ => Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm σ
        (Finset.mem_univ _))
    have li := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun i => (t i : ℂ)) (by
        funext σ
        have := hz σ
        simpa [hu, canonicalEmbedding.latticeBasis_apply, integralBasis_apply] using this)
    funext i
    exact_mod_cast li i

end Trace

end GlobalTheory.LatticeBoundTests
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDef

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TraceLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem cast_trace_mul_bar (x y : 𝓞 E) :
    ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℝ) = GlobalTheory.LatticeBoundTests.trBil E x y := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := ((x * H.bar y : 𝓞 E) : E))
  rw [← Algebra.coe_trace_int, ← (RingHom.equivRatAlgHom E ℂ).sum_comp] at h1
  rw [GlobalTheory.LatticeBoundTests.trBil_apply, ← Complex.re_sum]
  have h2 : ∑ σ : E →+* ℂ, σ (x : E) * starRingEnd ℂ (σ (y : E))
      = ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℂ) := by
    rw [← map_intCast (algebraMap ℚ ℂ), h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, ← map_mul]
    rfl
  rw [h2]; simp

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_traceForm_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  intro E _ _ _ H
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let q : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let e : Module.Basis (Fin (Fintype.card J)) ℤ (𝓞 E) := (RingOfIntegers.basis E).reindex q
  refine ⟨Fintype.card J, Matrix.of fun i j => Algebra.trace ℤ (𝓞 E) (e i * H.bar (e j)),
    (Algebra.leftMulMatrix e).toRingHom, ?_, ?_, ?_, ?_⟩
  · rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact Module.finrank_pos
  · ext i j
    apply Int.cast_injective (α := ℝ)
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [cast_trace_mul_bar, cast_trace_mul_bar, GlobalTheory.LatticeBoundTests.trBil_symm]
  · have h := (GlobalTheory.LatticeBoundTests.trBil_posDef E).submatrix q.symm.injective
    convert h using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply, cast_trace_mul_bar, e,
      Module.Basis.reindex_apply]
  · intro a
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.leftMulMatrix_eq_repr_mul]
    have h1 : ∑ k, e.repr (a * e i) k * Algebra.trace ℤ (𝓞 E) (e k * H.bar (e j))
        = Algebra.trace ℤ (𝓞 E) (a * e i * H.bar (e j)) := by
      conv_rhs => rw [← e.sum_repr (a * e i)]

      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc, map_zsmul, smul_eq_mul]
    have h2 : ∑ k, Algebra.trace ℤ (𝓞 E) (e i * H.bar (e k)) * e.repr (H.bar a * e j) k
        = Algebra.trace ℤ (𝓞 E) (e i * H.bar (H.bar a * e j)) := by
      conv_rhs => rw [← e.sum_repr (H.bar a * e j)]

      rw [map_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, mul_smul_comm, map_zsmul, smul_eq_mul, mul_comm]
    rw [h1, h2, map_mul H.bar, bar_bar]
    congr 1; ring

end GlobalTheory.TraceLattice
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDefStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  first | exact @GlobalTheory.TraceLattice.exists_traceForm_matrix | exact GlobalTheory.TraceLattice.exists_traceForm_matrix | (intros; apply GlobalTheory.TraceLattice.exists_traceForm_matrix <;> assumption)
end
end
