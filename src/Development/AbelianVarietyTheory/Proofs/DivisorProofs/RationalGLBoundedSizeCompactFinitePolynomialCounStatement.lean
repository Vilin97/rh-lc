module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLeStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le : ∀ (E : Type) [Field E] [NumberField E], ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧ ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.IntCount.card_bounded_integers_le | exact GlobalTheory.IntCount.card_bounded_integers_le | (intros; apply GlobalTheory.IntCount.card_bounded_integers_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdelesStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.exists_common_denominator_compact_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf → ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  first | exact @GlobalTheory.AdeleDenom.exists_common_denom | exact GlobalTheory.AdeleDenom.exists_common_denom | (intros; apply GlobalTheory.AdeleDenom.exists_common_denom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCount

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCountStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ∃ m : ℕ, ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧ ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.rat_bounded_compact_polynomial | exact GlobalTheory.rat_bounded_compact_polynomial | (intros; apply GlobalTheory.rat_bounded_compact_polynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCoun

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCounStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.ratGL_bounded_count | exact GlobalTheory.ratGL_bounded_count | (intros; apply GlobalTheory.ratGL_bounded_count <;> assumption)
end
end
