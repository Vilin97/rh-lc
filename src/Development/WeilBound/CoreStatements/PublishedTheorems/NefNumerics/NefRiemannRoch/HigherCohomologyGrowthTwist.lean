module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsPolynomialGrowthStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.global_sections_polynomial_growth : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  first | exact @GlobalTheory.exists_hdim_twist_lbPow_zero_le | exact GlobalTheory.exists_hdim_twist_lbPow_zero_le | (intros; apply GlobalTheory.exists_hdim_twist_lbPow_zero_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSection

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem higherCohomology_bound_twist_neg_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL ih F _ hF B hB s hs hb i hi
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F hB s) ≤ (d : ℕ) := suppDim_cut_le F hB s hF
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 : ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (cut F hB s) (lbPow L m)) j ≤ C * ((d + 1) * (m + 1) ^ d) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨C, hC⟩ := GlobalTheory.T.global_sections_polynomial_growth k X hX d L hL (cut F hB s) hcut
      exact ⟨C, fun m => (hC m).trans
        (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d)))⟩
    · obtain ⟨C, hC⟩ := ih (cut F hB s) hcut j hj
      exact ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ d)
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))))⟩
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := hb (j + 1) hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  have hB' := Twist.isLB_lbZPow hB (-1)
  obtain ⟨M', hM', e'⟩ := cls_surj (cls _ hB' + cls _ hM)
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hB' hM hM' e'
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B (lbPow L m) M' hB hM hM' s hs (by
    rw [e', cls_lbZPow hB (-1) hB']
    simp [add_comm, add_left_comm, add_assoc])).2.1 j
  have e2 : hdim k (twist (twistZ F B (-1)) (lbPow L m)) (j + 1) = hdim k (twist F M') (j + 1) :=
    hdim_congr k _ e
  rw [e2, add_mul]
  exact key.trans (Nat.add_le_add (hC₁ m) (hC₂ m))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSectionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | exact GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | (intros; apply GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyGrowthTwist

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.NefRR.hdim_twist_twist_bound : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ M : LB X, M.IsLB → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twist F M) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL hE F _ hF M hM hFb i hi
  have := isNoetherian_of_isProjOver hp
  obtain ⟨_, _, hAmp⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, B, hA, hB, s, t, hs, ht, hc⟩ := hAmp.exists_sub_of_mono_cutHom F (cls M hM)
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' k X hp d L hL hE F hF B hB t ht hFb i hi
  have : Mono (cutHom F hA s) := hs
  have hcut : suppDim (cut F hA s) ≤ d := suppDim_cut_le F hA s hF
  have := isFiniteQC_cut F hA s
  have := isFiniteQC_twist (F := cut F hA s) hM
  obtain ⟨C₂, h₂⟩ := hE (twist (cut F hA s) M) (by rwa [suppDim_twist hM]) i hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hLm := isLB_lbPow hL m
  have hN := isLB_tens hM hLm
  have hBi := isLB_lbZPow hB (-1)
  have hN' := isLB_tens hBi hLm
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (tens M (lbPow L m)) (tens (lbZPow B (-1)) (lbPow L m)) hA hN hN' s hs
    (by
      change cls M hM + cls _ hLm = (cls _ hBi + cls _ hLm) + cls A hA
      rw [hc, cls_lbZPow hB]; abel)).1 i
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hM hLm hN rfl
  obtain ⟨e₂⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hLm hN' rfl
  obtain ⟨e₃⟩ := nonempty_twist_twist_iso_of_cls_eq (cut F hA s) hM hLm hN rfl
  rw [hdim_congr k i e₁]
  rw [← hdim_congr k i e₂, ← hdim_congr k i e₃] at key
  have h₁m := h₁ m
  have h₂m := h₂ m
  have hpow : d * (m + 1) ^ (d - 1) ≤ (d + 1) * (m + 1) ^ d :=
    Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  calc _ ≤ _ := key
    _ ≤ C₁ * ((d + 1) * (m + 1) ^ d) + C₂ * ((d + 1) * (m + 1) ^ d) :=
        Nat.add_le_add h₁m (h₂m.trans (Nat.mul_le_mul_left _ hpow))
    _ = _ := (Nat.add_mul _ _ _).symm
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthTwist

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.higher_cohomology_growth_twist : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ M : LB X, M.IsLB → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twist F M) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @_root_.GlobalTheory.NefRR.hdim_twist_twist_bound | exact _root_.GlobalTheory.NefRR.hdim_twist_twist_bound | (intros; apply _root_.GlobalTheory.NefRR.hdim_twist_twist_bound <;> assumption)
end
end
