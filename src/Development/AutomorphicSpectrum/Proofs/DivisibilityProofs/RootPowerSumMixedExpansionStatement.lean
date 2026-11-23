module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsMixedDifferenceExpansion

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem exists_monomial_mixExpansion {σ : Type} [Fintype σ] (d : ℕ) :
    ∀ s : σ →₀ ℕ, s.degree = d → ∃ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ,
      mixDiff (monomial s (1 : ℝ)) = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i ∧
      ∀ i, (Gs i).IsHomogeneous (d - 1) ∧ (d = 0 → Gs i = 0) := by
  classical
  induction d with
  | zero =>
    intro s hs
    have hs0 : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst hs0
    refine ⟨fun _ => 0, ?_, fun i => ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩⟩
    simp [mixDiff]
  | succ d ih =>
    intro s hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra h
      push_neg at h
      have h0 : s = 0 := Finsupp.ext h
      simp [h0] at hs
    have hle : Finsupp.single i 1 ≤ s := by
      rw [Finsupp.single_le_iff]
      omega
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single i 1 :=
      ⟨s - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩
    have hdeg : s'.degree = d := by
      have e : (s' + Finsupp.single i 1).degree = s'.degree + 1 := by
        rw [Finsupp.degree_eq_weight_one, map_add (f := _)]
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      omega
    obtain ⟨G', hG', hG'h⟩ := ih s' hdeg
    refine ⟨fun j => (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0) + X (Sum.inr i) * G' j,
      ?_, fun j => ⟨?_, fun h => absurd h (Nat.succ_ne_zero d)⟩⟩
    · have key : mixDiff (monomial (s' + Finsupp.single i 1) (1 : ℝ)) =
          (X (Sum.inl i) - X (Sum.inr i)) * rename Sum.inl (monomial s' (1 : ℝ)) +
            X (Sum.inr i) * mixDiff (monomial s' (1 : ℝ)) := by
        simp only [mixDiff]
        rw [monomial_add_single, pow_one, map_mul, map_mul, rename_X, rename_X]
        ring
      rw [key, hG', Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    · have h2 : (X (Sum.inr i) * G' j : MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · rw [(hG'h j).2 h0, mul_zero]
          exact isHomogeneous_zero _ _ _
        · have h3 := (isHomogeneous_X ℝ (Sum.inr i : σ ⊕ σ)).mul (hG'h j).1
          rwa [show 1 + (d - 1) = d by omega] at h3
      have h1 : (if j = i then rename Sum.inl (monomial s' (1 : ℝ)) else 0 :
          MvPolynomial (σ ⊕ σ) ℝ).IsHomogeneous d := by
        split_ifs
        · exact (isHomogeneous_monomial _ hdeg).rename_isHomogeneous
        · exact isHomogeneous_zero _ _ _
      rw [Nat.add_sub_cancel]
      exact h1.add h2

theorem exists_mixExpansion_mixDiff (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ)
    (hF : F.IsHomogeneous n) : ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  classical
  have H := fun s : σ →₀ ℕ => fun h : s.degree = n => exists_monomial_mixExpansion n s h
  choose! G hGeq hGhom using H
  have hdeg : ∀ s ∈ F.support, s.degree = n := fun s hs => by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (mem_support_iff.mp hs)
  have hlin : mixDiff F = ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ)) := by
    conv_lhs => rw [F.as_sum]

    simp only [mixDiff, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show monomial s (F.coeff s) = C (F.coeff s) * monomial s (1 : ℝ) by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, rename_C, rename_C]
    ring
  refine ⟨fun i => ∑ s ∈ F.support, C (F.coeff s) * G s i, ?_⟩
  unfold IsMixExpansion
  refine ⟨?_, fun i => ?_⟩
  · rw [hlin]
    calc ∑ s ∈ F.support, C (F.coeff s) * mixDiff (monomial s (1 : ℝ))
        = ∑ s ∈ F.support, C (F.coeff s) * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * G s i :=
          Finset.sum_congr rfl fun s hs => by rw [hGeq s (hdeg s hs)]
      _ = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * ∑ s ∈ F.support, C (F.coeff s) * G s i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  · exact IsHomogeneous.sum _ _ _ fun s hs => ((hGhom s (hdeg s hs) i).1).C_mul _
end

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsMixedDifferenceExpansionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.exists_mixed_difference_expansion : ∀ (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ), F.IsHomogeneous n → ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | exact GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumMixedExpansion

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) =
      ∑ j ∈ Finset.range k,
        (X (Sum.inl (e a)) : MvPolynomial (σ ⊕ σ) ℝ) ^ j * X (Sum.inr (e a)) ^ (k - 1 - j) := by

  simp [psumExpansion, map_sum, map_mul, map_pow, rename_X]

theorem isHomogeneous_rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    (rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))).IsHomogeneous
      (k - 1) := by
  rw [rename_map_psumExpansion]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j + (k - 1 - j) = k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have h := ((isHomogeneous_X ℝ (Sum.inl (e a) : σ ⊕ σ)).pow j).mul
    ((isHomogeneous_X ℝ (Sum.inr (e a) : σ ⊕ σ)).pow (k - 1 - j))
  simpa [hj'] using h

theorem mixDiff_sum_pow {σ : Type} [Fintype σ] (r k : ℕ) (e : Fin r → σ) :
    mixDiff (∑ a, X (e a) ^ k : MvPolynomial σ ℝ) =
      ∑ a, (X (Sum.inl (e a)) - X (Sum.inr (e a))) *
        rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) := by
  unfold mixDiff

  simp only [map_sum, map_pow, rename_X, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rename_map_psumExpansion, mul_comm, (Commute.all _ _).geom_sum₂_mul]

theorem isMixExpansion_psum_mul : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  intro σ _ _ r k m e G hG
  refine ⟨?_, fun i => ?_⟩
  · rw [mixDiff_sum_pow, ← Finset.sum_fiberwise Finset.univ e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  · exact (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_rename_map_psumExpansion r k e a).mul hG

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumMixedExpansionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.power_sum_mixed_expansion : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | exact GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansion

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mixDiff_mul_leibniz {σ : Type} (A B : MvPolynomial σ ℝ) :
    mixDiff (A * B) = mixDiff A * rename Sum.inl B + rename Sum.inr A * mixDiff B := by
  simp only [mixDiff, map_mul]
  ring

theorem mixDiff_eq_zero_of_isHomogeneous_zero {σ : Type} {Q : MvPolynomial σ ℝ}
    (hQ : Q.IsHomogeneous 0) : mixDiff Q = 0 := by
  have h : Q.totalDegree = 0 := Nat.eq_zero_of_le_zero hQ.totalDegree_le
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
  rw [h]
  simp only [mixDiff, rename_C, sub_self]

theorem rootPs_mul_mixExpansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  intro Ψ _ _ N d k hk1 hk2 τ Q hQ
  obtain ⟨Hs, hMix⟩ := GlobalTheory.T.exists_mixed_difference_expansion (Ψ × Fin N) (d + 1 - k) Q hQ
  unfold IsMixExpansion at hMix
  obtain ⟨hHs, hHdeg⟩ := hMix
  have hQl : (rename Sum.inl Q : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous (d + 1 - k) :=
    hQ.rename_isHomogeneous
  have hE := GlobalTheory.T.power_sum_mixed_expansion (Ψ × Fin N) N k (d + 1 - k) (fun a => (τ, a)) (rename Sum.inl Q) hQl
  unfold IsMixExpansion at hE
  obtain ⟨hE1, hE2⟩ := hE
  obtain ⟨Hs', hz, hmixQ, hdeg'⟩ : ∃ Hs' : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ,
      (k = d + 1 → ∀ i, Hs' i = 0) ∧ mixDiff Q = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Hs' i ∧
        ∀ i, (Hs' i).IsHomogeneous (d - k) := by
    by_cases hkd : k = d + 1
    · refine ⟨fun _ => 0, fun _ _ => rfl, ?_, fun _ => MvPolynomial.isHomogeneous_zero _ _ _⟩
      have h0 : Q.IsHomogeneous 0 := by
        have e : d + 1 - k = 0 := by omega
        rw [e] at hQ
        exact hQ
      simp only [mul_zero, Finset.sum_const_zero]
      exact mixDiff_eq_zero_of_isHomogeneous_zero h0
    · refine ⟨Hs, fun h => absurd h hkd, hHs, fun i => ?_⟩
      have h3 := hHdeg i
      have e : d + 1 - k - 1 = d - k := by omega
      rw [e] at h3
      exact h3
  unfold IsMixExpansion
  refine ⟨Hs', hdeg', hz, ?_, ?_⟩
  · rw [mixDiff_mul_leibniz, hmixQ]
    have h1 : mixDiff (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) * rename Sum.inl Q =
        ∑ i, (X (Sum.inl i) - X (Sum.inr i)) *
          ((∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
            rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
              (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) := hE1
    have h2 : (rename Sum.inr (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) :
        MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ) = ∑ a : Fin N, X (Sum.inr (τ, a)) ^ k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rootPs, map_sum, map_pow, rename_X]
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · intro i
    apply MvPolynomial.IsHomogeneous.add
    · have h4 := hE2 i
      have e : k - 1 + (d + 1 - k) = d := by omega
      rw [e] at h4
      exact h4
    · have hS : (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k :
          MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous k :=
        MvPolynomial.IsHomogeneous.sum _ _ _ (fun a _ => MvPolynomial.isHomogeneous_X_pow _ _)
      by_cases hkd : k = d + 1
      · rw [hz hkd i, mul_zero]
        exact MvPolynomial.isHomogeneous_zero _ _ _
      · have h5 := hS.mul (hdeg' i)
        have e : k + (d - k) = d := by omega
        rw [e] at h5
        exact h5

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.root_power_sum_mixed_expansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | exact GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion <;> assumption)
end
end
