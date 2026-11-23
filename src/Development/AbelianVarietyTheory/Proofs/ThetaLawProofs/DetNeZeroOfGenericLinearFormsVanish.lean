module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
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
import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.GoingUp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Mathlib.Algebra.BigOperators.Field

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.InjectiveOfInjectiveCompAevalOfTrdegLe

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory

open MvPolynomial

theorem injective_of_injective_comp_aeval_of_trdeg_le {k A κ ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing κ] [Finite ι] (b : ι → A)
    (hA : Algebra.trdeg k A ≤ Cardinal.mk ι) (χ : A →+* κ)
    (hχ : Function.Injective (fun q : MvPolynomial ι k => χ (aeval b q))) :
    Function.Injective χ := by
  have hb : AlgebraicIndependent k b := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact Function.Injective.of_comp (f := χ) hχ
  have hT := hb.isTranscendenceBasis_of_trdeg_le_of_finite hA
  have := hT.isAlgebraic
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hmem : a ∈ RingHom.ker χ := ha
  refine Ideal.comap_ne_bot_of_algebraic_mem hne hmem
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin k (Set.range b)) a) (eq_bot_iff.2 fun y hy => ?_)
  rw [Ideal.mem_comap, RingHom.mem_ker] at hy
  rw [Ideal.mem_bot]
  obtain ⟨y, hy'⟩ := y
  have hr := hy'
  rw [Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨q, rfl⟩ := hr
  have h0 : χ (aeval b q) = 0 := hy
  have hq : q = 0 := hχ (show χ (aeval b q) = χ (aeval b 0) by rw [map_zero, map_zero]; exact h0)
  subst hq
  apply Subtype.ext
  simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetNeZeroOfGenericLinearFormsVanish

section

@[expose] public section

namespace GlobalTheory

open MvPolynomial

theorem det_ne_zero_of_generic_linear_forms_vanish :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) (g N : ℕ)
    (T : Fin g × Fin N → K) (e : Fin N → K) (D : Fin g → Fin N → K),
    AlgebraicIndependent k T → Algebra.trdeg k F ≤ g → (∀ j, e j ∈ F) → (∀ a j, D a j ∈ F) →
    (∃ j, e j ≠ 0) →
    (∃ c : Fin g → Fin N → K, (∀ i, ∑ j, c i j * e j = 0) ∧
      (Matrix.of fun i a => ∑ j, c i j * D a j).det ≠ 0) →
    (∀ i, ∑ j, T (i, j) * e j = 0) → (Matrix.of fun i a => ∑ j, T (i, j) * D a j).det ≠ 0 := by
  intro k K _ _ _ F g N T e D hT hF he hD ⟨j0, hj0⟩ ⟨c, hc, hcd⟩ hTe
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := j0.pos; omega⟩
  let η : Fin (M + 1) → F := fun j => ⟨e j / e j0, F.div_mem (he j) (he j0)⟩
  let D' : Fin g → Fin (M + 1) → F := fun a j => ⟨D a j, hD a j⟩
  let b : Fin g × Fin (M + 1) → MvPolynomial (Fin g × Fin M) F := fun p =>
    Fin.insertNth (α := fun _ => MvPolynomial (Fin g × Fin M) F) j0
      (-∑ l : Fin M, X (p.1, l) * C (η (j0.succAbove l))) (fun l => X (p.1, l)) p.2
  let χ : (Fin g × Fin (M + 1) → K) → (MvPolynomial (Fin g × Fin M) F →ₐ[F] K) := fun v =>
    aeval fun q => v (q.1, j0.succAbove q.2)
  have hb : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      ∀ p, χ v (b p) = v p := by
    rintro v hv ⟨i, j⟩
    refine Fin.succAboveCases j0 ?_ (fun l => ?_) j
    · have h1 := hv i
      rw [Fin.sum_univ_succAbove _ j0] at h1
      have h2 : v (i, j0) =
          -∑ l : Fin M, v (i, j0.succAbove l) * (e (j0.succAbove l) / e j0) := by
        simp only [← mul_div_assoc, ← Finset.sum_div]
        field_simp
        linear_combination h1
      rw [h2]
      simp [b, χ, η]
    · simp [b, χ]
  let Δ : MvPolynomial (Fin g × Fin M) F :=
    (Matrix.of fun i a => ∑ j, b (i, j) * C (D' a j)).det
  have hΔ : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      χ v Δ = (Matrix.of fun i a => ∑ j, v (i, j) * D a j).det := by
    intro v hv
    rw [AlgHom.map_det]
    congr 1
    ext i a

    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    hb v hv]
    simp [χ, D']
  have hΔ0 : Δ ≠ 0 := by
    intro h
    apply hcd
    rw [← hΔ (fun p => c p.1 p.2) hc, h, map_zero]
  have htr : Algebra.trdeg k (MvPolynomial (Fin g × Fin M) F) ≤
      Cardinal.mk (Fin g × Fin (M + 1)) := by
    have : FaithfulSMul F (MvPolynomial (Fin g × Fin M) F) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)
    rw [← trdeg_add_eq k F, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype, Cardinal.mk_fintype]
    refine (add_le_add_left hF _).trans ?_
    norm_cast
    simp only [Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  have hχ : Function.Injective (χ T).toRingHom := by
    refine injective_of_injective_comp_aeval_of_trdeg_le (k := k) b htr _ ?_
    have : (fun q : MvPolynomial (Fin g × Fin (M + 1)) k => (χ T).toRingHom (aeval b q)) =
        aeval T := by
      have h3 : ((χ T).restrictScalars k).comp (aeval b) = aeval T := by
        apply MvPolynomial.algHom_ext
        intro p
        simp [hb T hTe]
      funext q
      exact DFunLike.congr_fun h3 q
    rw [this]
    exact hT
  rw [← hΔ T hTe]
  intro h
  exact hΔ0 (hχ (by simpa using h))

end GlobalTheory
end
end
