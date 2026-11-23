module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRestrictionIrreducible
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
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefHigherCohomologyGrowth

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefTwist_hdim_bound_succ : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d + 1 : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d))) := by
  intro k _ _ d hd Y _ hY N hN E _ hsupp j hj
  haveI hnoeth : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  obtain ⟨hprop, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hY
  haveI := hprop
  have hfin : ∀ (F : Y.Modules) [IsFiniteQC F] (m : ℕ), FiniteCoh k (twist F (lbPow N m)) :=
    fun F _ m => IsAmpleLB.finiteCohTwists (algebraMap_eq_strHom k Y) F hA _ (isLB_lbPow hN.isLB m)
  let P : Y.Modules → Prop := fun F => suppDim F ≤ ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ j, 0 < j → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow N m)) j ≤ C * ((d + 1) * (m + 1) ^ d)
  have key : ∀ F : Y.Modules, IsFiniteQC F → P F := by
    refine QCoh.devissage Y P ?_ ?_ ?_
    · intro F hF _ j _
      refine ⟨0, fun m => ?_⟩
      have hz : IsZero (twist F (lbPow N m)) := (isZero_twist_iff (isLB_lbPow hN.isLB m)).2 hF
      haveI : Subsingleton (coh (twist F (lbPow N m)) j) := by
        have := cohOn.subsingleton_of_isZero hz ⊤ j
        exact this
      rw [hdim_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · intro S hS h1 h3 hP1 hP3 hs2 j hj
      haveI := h1
      haveI := h3
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨C1, hC1⟩ := hP1 ((suppDim_le_of_mono S.f).trans hs2) j hj
      obtain ⟨C3, hC3⟩ := hP3 ((suppDim_le_of_epi S.g).trans hs2) j hj
      refine ⟨C1 + C3, fun m => ?_⟩
      have hL := isLB_lbPow hN.isLB m
      haveI := Twist.preservesFiniteLimits_twistFunctor hL
      haveI := Twist.preservesColimits_twistFunctor hL
      have hS' := hS.map_of_exact (twistFunctor (lbPow N m))
      have h := hdim₂_le k hS' j ((hfin S.X₁ m).finite j) ((hfin S.X₃ m).finite j)
      have e1 := hC1 m
      have e3 := hC3 m
      simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃, twistFunctor_obj] at h
      calc hdim k (twist S.X₂ (lbPow N m)) j ≤ hdim k (twist S.X₁ (lbPow N m)) j + hdim k (twist S.X₃ (lbPow N m)) j := h
        _ ≤ C1 * ((d + 1) * (m + 1) ^ d) + C3 * ((d + 1) * (m + 1) ^ d) := Nat.add_le_add e1 e3
        _ = (C1 + C3) * ((d + 1) * (m + 1) ^ d) := by ring
    · intro Z hirr IH G hG hs j hj
      haveI := hG
      have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set Y) := by
        refine (support_pushforward_subset_image_of_isClosedImmersion _ G).trans ?_
        rintro _ ⟨x, -, rfl⟩
        rw [← range_redι Z]
        exact ⟨x, rfl⟩
      haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ProperFinite.isFiniteQC_pushforward (redι Z) (IsAmpleLB.pull_of_isClosedImmersion hA (redι Z)) G
      by_cases hstrict : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊂ (Z : Set Y)
      · exact IH _ inferInstance hstrict hs j hj
      · have heq : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set Y) := by
          by_contra hne
          exact hstrict (HasSubset.Subset.ssubset_of_ne hsub hne)
        have hgen := hirr.isGenericPoint_genericPoint_closure
        rw [Z.isClosed.closure_eq] at hgen
        obtain ⟨w, hcl⟩ : ∃ w : Y, closure ({w} : Set Y) = (Z : Set Y) := ⟨_, hgen⟩
        have hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
          rw [heq, ← hcl]
          exact subset_closure (Set.mem_singleton _)
        have hdimZ : topologicalKrullDim (Z : Set Y) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
          have := SheafCycle.dim_closure_le_suppDim hw
          rw [hcl] at this
          exact this.trans hs
        exact RRPush.hdim_pushforward_le k d hd Y hY N hN Z hirr hdimZ G j hj
  exact key E inferInstance hsupp j hj

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRiemannRoch

theorem hdim_twist_nef_pow_le_of_pos (k : Type) [Field k] [Infinite k] (d : ℕ) :
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → ∀ N : LB Y, IsNef k N →
      ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j →
        ∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)) := by
  induction d with
  | zero =>
    intro Y _ hY N hN E _ hE j hj
    refine ⟨0, fun m => ?_⟩
    haveI := isNoetherian_of_isProjOver hY
    have hE0 : suppDim E ≤ 0 := by exact_mod_cast hE
    haveI := subsingleton_coh_of_suppDim_le_zero hE0 hj
    rw [hdim_twist_of_suppDim_le_zero k hE0 (isLB_lbPow hN.isLB m), hdim_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  | succ d ih => exact nefTwist_hdim_bound_succ k d ih

theorem abs_factorial_mul_sections_sub_top_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ), topologicalKrullDim X ≤ (d : ℕ) → ∀ L : LB X, IsNef k L → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hX d hd L hL
  haveI := isNoetherian_of_isProjOver hX
  obtain ⟨_, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX
  have hLB := hL.isLB
  have hO : suppDim (structureModule X) ≤ ((d : ℕ) : WithBot ℕ∞) := by
    rw [QCoh.suppDim_structureModule]
    exact hd
  obtain ⟨K, hK⟩ := abs_factorial_mul_chi_twist_lbPow_sub_le k X hX d
    (structureModule X) hO L hLB
  have hb : ∀ n : ℕ, 0 < n → ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (structureModule X) (lbPow L m)) n ≤ C * (d * (m + 1) ^ (d - 1)) :=
    fun n hn => hdim_twist_nef_pow_le_of_pos k d X hX L hL (structureModule X) hO n hn
  choose! Cf hCf using hb
  set D : ℕ := d.factorial with hD
  refine ⟨K + D * ∑ i ∈ Finset.range d, Cf (i + 1), fun m => ?_⟩
  have hLm := isLB_lbPow hLB m
  haveI : IsFiniteQC (twist (structureModule X) (lbPow L m)) := isFiniteQC_twist hLm
  have hvan : ∀ n : ℕ, d + 1 ≤ n → Subsingleton (coh (twist (structureModule X) (lbPow L m)) n) := by
    intro n hn
    refine IsAmpleLB.subsingleton_coh_of_suppDim_lt hA _ ?_
    rw [suppDim_twist hLm]
    refine lt_of_le_of_lt hO ?_
    exact_mod_cast (Nat.lt_of_succ_le hn)
  have hchi1 := chi_eq_sum_range k (d + 1) hvan
  set h : ℕ → ℚ := fun n => (hdim k (twist (structureModule X) (lbPow L m)) n : ℚ) with hh
  have hH : ∀ i ∈ Finset.range d, h (i + 1) ≤ (Cf (i + 1) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    intro i _
    have := hCf (i + 1) (Nat.succ_pos i) m
    simp only [hh]
    exact_mod_cast this
  have hkey : ((D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d) =
      ((D : ℚ) * (chi k (twist (structureModule X) (lbPow L m)) : ℚ) -
        (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d) -
      (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
    have e1 : (chi k (twist (structureModule X) (lbPow L m)) : ℚ) =
        h 0 + ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1) := by
      rw [hchi1]
      push_cast
      rw [Finset.sum_range_succ']
      simp [hh]
      ring
    rw [e1]
    ring
  have hfin : |(D : ℚ) * h 0 - (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| ≤
      ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [hkey]
    set B : ℚ := (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) with hBdef
    have hD0 : (0 : ℚ) ≤ D := by positivity
    have s1 : |(D : ℚ) * (chi k (twist (structureModule X) (lbPow L m)) : ℚ) -
        (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| ≤ (K : ℚ) * B := by
      have e := hK m
      rw [← topSelf_def] at e
      have e' : ((|(d.factorial : ℤ) * chi k (twist (structureModule X) (lbPow L m)) -
          topSelfIntersection k L d * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
          ((K : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) := by
        exact_mod_cast e
      push_cast at e'
      simpa [hD, hBdef] using e'
    have s2 : |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| ≤ (∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by simp only [hh]; positivity)]
      exact hH i hi
    have hB0 : 0 ≤ B := by positivity
    calc |(D : ℚ) * (chi k (twist (structureModule X) (lbPow L m)) : ℚ) -
            (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d -
            (D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)|
        ≤ |(D : ℚ) * (chi k (twist (structureModule X) (lbPow L m)) : ℚ) -
            (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| +
          |(D : ℚ) * ∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := abs_sub _ _
      _ = |(D : ℚ) * (chi k (twist (structureModule X) (lbPow L m)) : ℚ) -
            (topSelfIntersection k L d : ℚ) * (m : ℚ) ^ d| +
          (D : ℚ) * |∑ i ∈ Finset.range d, (-1) ^ (i + 1) * h (i + 1)| := by
          rw [abs_mul, abs_of_nonneg hD0]
      _ ≤ (K : ℚ) * B + (D : ℚ) * ((∑ i ∈ Finset.range d, (Cf (i + 1) : ℚ)) * B) := by
          gcongr
      _ = ((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℚ) * B := by
          push_cast
          ring
  have hfin' : ((|(d.factorial : ℤ) * (lbH0 k (lbPow L m) : ℤ) - topSelfIntersection k L d * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      (((K + D * ∑ i ∈ Finset.range d, Cf (i + 1) : ℕ) : ℤ) * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) := by
    push_cast
    simpa [hh, lbH0, hD] using hfin
  exact_mod_cast hfin'

end GlobalTheory.NefRiemannRoch
end
end
