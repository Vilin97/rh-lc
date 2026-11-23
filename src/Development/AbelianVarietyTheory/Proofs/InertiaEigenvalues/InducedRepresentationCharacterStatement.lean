module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.InducedCharRealised

section

@[expose] public section

set_option autoImplicit false

namespace BrauerSchur

open scoped BigOperators

section IndFun

variable {G : Type*} [Group G] [Fintype G]


open scoped Classical in
noncomputable def indFun {R : Type*} [Field R] (H : Subgroup G) (f : H → R) (g : G) : R :=
  (Nat.card H : R)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0

end IndFun

end BrauerSchur
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.Induced

section

@[expose] public section

set_option autoImplicit false

namespace BrauerSchur

open scoped BigOperators

section Induced

variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)


open scoped Classical in
noncomputable def dot (x : G) : K := by
  classical
  exact if hx : x ∈ H then ((ψ ⟨x, hx⟩ : Kˣ) : K) else 0

theorem dot_mul_of_mem {a b : G} (hb : b ∈ H) : dot H ψ a * dot H ψ b = dot H ψ (a * b) := by
  classical
  unfold dot
  by_cases ha : a ∈ H
  · rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (H.mul_mem ha hb), ← Units.val_mul, ← map_mul]
    rfl
  · have hab : a * b ∉ H := fun h => ha (by
      have := H.mul_mem h (H.inv_mem hb)
      rwa [mul_inv_cancel_right] at this)
    rw [dite_eq_right ha, dite_eq_right hab, zero_mul]

theorem dot_conj {h : G} (hh : h ∈ H) (y : G) : dot H ψ (h⁻¹ * y * h) = dot H ψ y := by
  classical
  unfold dot
  by_cases hy : y ∈ H
  · have hm : h⁻¹ * y * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh
    rw [dite_eq_left hy, dite_eq_left hm]
    have e : (⟨h⁻¹ * y * h, hm⟩ : H) = (⟨h, hh⟩ : H)⁻¹ * ⟨y, hy⟩ * ⟨h, hh⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  · have hm : h⁻¹ * y * h ∉ H := fun hm => hy (by
      have e : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh hm) (H.inv_mem hh))
    rw [dite_eq_right hy, dite_eq_right hm]

variable {m : ℕ} (t : Fin m → G)

noncomputable def indMat (g : G) : Matrix (Fin m) (Fin m) K :=
  fun i j => dot H ψ ((t i)⁻¹ * g * t j)

theorem indMat_one (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) : indMat H ψ t 1 = 1 := by
  classical
  ext i j
  simp only [indMat, mul_one]
  rw [Matrix.one_apply]
  unfold dot
  split_ifs with h1 h2 h2
  · subst h2
    have e : (⟨(t i)⁻¹ * t i, h1⟩ : H) = 1 := Subtype.ext (inv_mul_cancel _)
    rw [e, map_one, Units.val_one]
  · exact absurd ((ht i j).mp h1) h2
  · exact absurd ((ht i j).mpr h2) h1
  · rfl

theorem indMat_mul (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g g' : G) : indMat H ψ t (g * g') = indMat H ψ t g * indMat H ψ t g' := by
  ext i k
  rw [Matrix.mul_apply]
  obtain ⟨j0, hj0⟩ := hc (g' * t k)
  have hb : (t j0)⁻¹ * g' * t k ∈ H := by rwa [mul_assoc]
  rw [Finset.sum_eq_single j0]
  · simp only [indMat]
    rw [dot_mul_of_mem H ψ hb]
    congr 1
    group
  · intro j _ hj
    simp only [indMat]
    have hz : dot H ψ ((t j)⁻¹ * g' * t k) = 0 := by
      classical
      unfold dot
      rw [dite_eq_right]
      intro hm
      apply hj
      rw [← ht j j0]
      have e : (t j)⁻¹ * t j0 = ((t j)⁻¹ * g' * t k) * ((t j0)⁻¹ * g' * t k)⁻¹ := by group
      rw [e]
      exact H.mul_mem hm (H.inv_mem hb)
    rw [hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable def indRep (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) :
    Representation K G (Fin m → K) where
  toFun g := Matrix.toLin' (indMat H ψ t g)
  map_one' := by rw [indMat_one H ψ t ht, Matrix.toLin'_one]; rfl
  map_mul' g g' := by rw [indMat_mul H ψ t ht hc, Matrix.toLin'_mul]; rfl

theorem indRep_trace (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g : G) : LinearMap.trace K (Fin m → K) (indRep H ψ t ht hc g) = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  show LinearMap.trace K (Fin m → K) (Matrix.toLin' (indMat H ψ t g)) = _
  rw [Matrix.trace_toLin'_eq]
  rfl

theorem indFun_eq_sum [Fintype G] [CharZero K] (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j)
    (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) (g : G) :
    indFun H (fun h => ((ψ h : Kˣ) : K)) g = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  classical
  show (Nat.card H : K)⁻¹ * ∑ x : G, dot H ψ (x⁻¹ * g * x) = _
  let f : Fin m × H → G := fun p => t p.1 * p.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, h⟩ ⟨j, h'⟩ hij
      simp only [f] at hij
      have hij' : i = j := by
        rw [← ht i j]
        have e : (t i)⁻¹ * t j = (h : G) * (h' : G)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hij, inv_mul_cancel_left]
        rw [e]
        exact H.mul_mem h.2 (H.inv_mem h'.2)
      subst hij'
      have : (h : G) = h' := mul_left_cancel hij
      rw [Subtype.ext this]
    · intro x
      obtain ⟨i, hi⟩ := hc x
      exact ⟨⟨i, ⟨_, hi⟩⟩, by simp [f]⟩
  rw [← Fintype.sum_bijective f hf (fun p => dot H ψ ((f p)⁻¹ * g * f p)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  have hin : ∀ i, ∑ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) =
      (Fintype.card H : K) * dot H ψ ((t i)⁻¹ * g * t i) := by
    intro i
    have : ∀ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) = dot H ψ ((t i)⁻¹ * g * t i) := by
      intro h
      have e : (f (i, h))⁻¹ * g * f (i, h) = (h : G)⁻¹ * ((t i)⁻¹ * g * t i) * h := by
        simp only [f]
        group
      rw [e, dot_conj H ψ h.2]
    rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hin i, ← Finset.mul_sum, ← mul_assoc, Nat.card_eq_fintype_card,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

end Induced

end BrauerSchur
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacter

section

@[expose] public section

open GlobalTheory.Published

noncomputable section

namespace GlobalTheory.InertiaEigenvalues

open BrauerSchur

theorem exists_transversal_index {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Fin H.index → G, (∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) ∧ ∀ x, ∃ i, (t i)⁻¹ * x ∈ H := by
  classical
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  refine ⟨fun i => (e.symm i).out, fun i j => ?_, fun x => ⟨e (x : G ⧸ H), ?_⟩⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.symm.injective.eq_iff]
  · rw [← QuotientGroup.eq]
    simp only [Equiv.symm_apply_apply, QuotientGroup.out_eq']

theorem inducedRep_cyclic_trace (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ) :
    ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ),
      (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧
      ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = GlobalTheory.Published.indFun H (fun x => (χ x : ℂ)) g := by
  classical
  obtain ⟨t, ht, hc⟩ := exists_transversal_index H
  obtain ⟨i0, hi0⟩ := hc 1
  rw [mul_one] at hi0
  have hti0 : t i0 ∈ H := by simpa using H.inv_mem hi0
  have memiff : ∀ (k i : Fin H.index) (a : G), (t i)⁻¹ * a ∈ H → ((t k)⁻¹ * a * t i0 ∈ H ↔ k = i) := by
    intro k i a ha
    rw [← ht k i]
    constructor
    · intro hm
      have e : (t k)⁻¹ * t i = ((t k)⁻¹ * a * t i0) * (t i0)⁻¹ * ((t i)⁻¹ * a)⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm (H.inv_mem hti0)) (H.inv_mem ha)
    · intro hm
      have e : (t k)⁻¹ * a * t i0 = ((t k)⁻¹ * t i) * ((t i)⁻¹ * a) * t i0 := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm ha) hti0
  refine ⟨indRep H χ t ht hc, Pi.single i0 1, ?_, ?_, ?_⟩
  · intro σ
    ext k
    show Matrix.toLin' (indMat H χ t (σ : G)) (Pi.single i0 1) k = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
    have hσ : (t i0)⁻¹ * (σ : G) ∈ H := H.mul_mem hi0 σ.2
    by_cases hk : k = i0
    · subst hk
      rw [Pi.single_eq_same, mul_one, dot_conj H χ hti0 (σ : G)]
      unfold dot
      rw [dite_eq_left σ.2]
    · rw [Pi.single_eq_of_ne hk, mul_zero]
      unfold dot
      rw [dite_eq_right]
      rw [memiff k i0 _ hσ]
      exact hk
  · rw [eq_top_iff]
    have hsingle : ∀ i, Pi.single i (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun g => indRep H χ t ht hc g (Pi.single i0 1)) := by
      intro i
      have hti : (t i)⁻¹ * t i ∈ H := by simpa using H.one_mem
      have hval : indRep H χ t ht hc (t i) (Pi.single i0 1) = dot H χ (t i0) • Pi.single i (1 : ℂ) := by
        ext k
        show Matrix.toLin' (indMat H χ t (t i)) (Pi.single i0 1) k = _
        rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
        simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same, mul_one, inv_mul_cancel, one_mul]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
          unfold dot
          rw [dite_eq_right]
          rw [memiff k i _ hti]
          exact hk
      have hne : dot H χ (t i0) ≠ 0 := by
        unfold dot
        rw [dite_eq_left hti0]
        exact Units.ne_zero _
      have : Pi.single i (1 : ℂ) = (dot H χ (t i0))⁻¹ • indRep H χ t ht hc (t i) (Pi.single i0 1) := by
        rw [hval, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t i, rfl⟩)
    intro x _
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [e]; exact hsingle i
  · intro g
    rw [indRep_trace, ← indFun_eq_sum H χ t ht hc g]
    rfl

end GlobalTheory.InertiaEigenvalues

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement

section

@[expose] public section

open GlobalTheory.Published

theorem _root_.GlobalTheory.T.induced_representation_character : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)
end
end
