module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinorDeterminants

section

@[expose] public section

theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card := by
  intro N J
  rfl

noncomputable def UpperTheory.Reformulated.B.MinorDeterminants.minorIJ :
    {R : Type} → [CommRing R] → {N : ℕ} → Matrix (Fin N) (Fin N) R → Finset (Fin N) → Finset (Fin N) → R :=
    fun {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) ↦
      if e : I.card = J.card then
        (h.submatrix (⇑(I.orderEmbOfFin e) : Fin J.card → Fin N)
            (⇑(J.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 J)) : Fin J.card → Fin N)).det
      else (0 : R)

theorem UpperTheory.Reformulated.B.MinorDeterminants.main :
    ∀ {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (f : Fin S.card → Fin N),
      Function.Injective f →
        UpperTheory.Reformulated.B.MinorDeterminants.minorIJ C (Finset.image f Finset.univ) S = (0 : ℂ) →
          (C.submatrix f (⇑(S.orderEmbOfFin rfl) : Fin S.card → Fin N)).det = (0 : ℂ) := by
  intro N C S f hf h0
  have e : (Finset.image f Finset.univ).card = S.card := by
    rw [Finset.card_image_of_injective _ hf]; simp
  unfold UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0
  rw [dite_eq_left e] at h0
  set I := Finset.image f Finset.univ with hI
  have mem : ∀ i, f i ∈ I := fun i => by simp [hI]
  let σf : Fin S.card → Fin S.card := fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩
  have hσ : Function.Injective σf := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab
    simpa [σf] using this
  let σ : Equiv.Perm (Fin S.card) := Equiv.ofBijective σf hσ.bijective_of_finite
  have hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ := by
    funext i
    simp only [Function.comp, σ, Equiv.ofBijective_apply, σf]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp
  have key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) =
      (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id := by
    rw [hfg, Matrix.submatrix_submatrix]
    rfl
  rw [key, Matrix.det_permute, h0, mul_zero]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalMinorsBlockTriangular

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PlVanish

theorem cols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minor_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.minorIJ_one_ne <;> assumption

theorem minor_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (f : Fin S.card → Fin N) (hf : Function.Injective f)
    (h0 : minorIJ C (Finset.univ.image f) S = 0) :
    (C.submatrix f (S.orderEmbOfFin rfl)).det = 0 :=
  _root_.UpperTheory.Reformulated.B.MinorDeterminants.main C S f hf h0

theorem minor_quot {N j : ℕ} (hj : j ≤ N) (i : Fin N) {h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} {α β : ℂ}
    (hb₁ : IsBlockDiag j h₁) (hb₂ : IsBlockDiag j h₂) (hd : h₁.det ≠ 0)
    (hp : ∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i))
    (I : Finset (Fin N)) :
    β * minorIJ (h₁⁻¹ * h₂) I (stepCols N j i) =
      α * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj
  have hne := cols_ne_empty hj i
  have hall : ∀ J, α * minorIJ h₁ J (stepCols N j i) = β * minorIJ h₂ J (stepCols N j i) := fun J => by
    by_cases hJ : IsStepRows N j i J
    · exact hp J hJ
    · rw [(off h₁ J hb₁ hJ).resolve_right hne, (off h₂ J hb₂ hJ).resolve_right hne, mul_zero, mul_zero]
  have e1 : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) =
      minorIJ (h₁⁻¹ * h₁) I (stepCols N j i) := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]
  rw [e1, cb, cb, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  linear_combination (-minorIJ h₁⁻¹ I J) * hall J

theorem quot_vanish : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N →
    IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 →
    (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) →
    ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  intro N j i h₁ h₂ α β hj hb₁ hb₂ hd hα hβ hp r c hc hr
  have hq := minor_quot hj i hb₁ hb₂ hd hp
  set S := stepCols N j i with hS
  set C := h₁⁻¹ * h₂ with hC
  let e := S.orderEmbOfFin rfl
  obtain ⟨t, ht⟩ : ∃ t, e t = c := by
    have h2 : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    exact h2
  let D : Matrix (Fin S.card) (Fin S.card) ℂ := C.submatrix e e
  have hD : D.det ≠ 0 := by
    have h1 := hq S
    rw [minor_one_same, mul_one] at h1
    have h2 : minorIJ C S S = D.det := dif_pos rfl
    rw [← h2]
    intro h0
    rw [h0, mul_zero] at h1
    exact hα h1.symm
  let v : Fin S.card → ℂ := fun s => C r (e s)
  have hrow : ∀ u, (D.updateRow u v).det = 0 := fun u => by
    let f : Fin S.card → Fin N := Function.update e u r
    have hmem : ∀ s, e s ∈ S := fun s => Finset.orderEmbOfFin_mem _ _ _
    have hf : Function.Injective f := fun a b hab => by
      by_cases ha : a = u
      · by_cases hb : b = u
        · rw [ha, hb]
        · subst ha
          simp only [f, Function.update_self, Function.update_of_ne hb] at hab
          exact absurd (hab ▸ hmem b) hr
      · by_cases hb : b = u
        · subst hb
          simp only [f, Function.update_self, Function.update_of_ne ha] at hab
          exact absurd (hab ▸ hmem a) hr
        · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
          exact e.injective hab
    have hI : Finset.univ.image f ≠ S := fun h => hr (by
      rw [← h]
      exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, Function.update_self _ _ _⟩)
    have h0 : minorIJ C (Finset.univ.image f) S = 0 := by
      have h1 := hq (Finset.univ.image f)
      rw [minor_one_ne hI, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hβ
    have h2 := det_submatrix_eq_zero C S f hf h0
    have e2 : D.updateRow u v = C.submatrix f e := by
      ext a b
      by_cases ha : a = u
      · subst ha
        simp [f, D, v, Matrix.updateRow_self]
      · simp [f, D, Matrix.updateRow_ne ha, Function.update_of_ne ha]
    rw [e2]
    exact h2
  have hcr : Dᵀ.cramer v = 0 := by
    funext u
    rw [Matrix.cramer_transpose_apply]
    exact hrow u
  have h3 := Matrix.mulVec_cramer Dᵀ v
  rw [hcr, Matrix.mulVec_zero, Matrix.det_transpose] at h3
  have h4 : D.det * v t = 0 := by
    have := congrFun h3 t
    simpa using this.symm
  have h5 : v t = 0 := (mul_eq_zero.1 h4).resolve_left hD
  rw [← ht]
  exact h5

end GlobalTheory.CompanionTheory.Ar.PB.PlVanish
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalMinorsBlockTriangularStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.proportional_minors_block_triangular : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N → IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 → (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish | exact GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish <;> assumption)
end
end
