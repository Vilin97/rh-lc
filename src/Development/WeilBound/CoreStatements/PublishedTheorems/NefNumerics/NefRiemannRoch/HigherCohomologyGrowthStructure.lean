module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBoundOfStepDiff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDimsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigher

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem abs_chi_sub_hdim_zero_add_hdim_one_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  intro k _ _ X _ hp n L hL F _ hF e he
  choose C hC using fun i : ℕ => he (i + 2) (by omega)
  refine ⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM
  have hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i) := fun i hi =>
    subsingleton_coh_of_isProjOver hp _
      (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))
  rw [chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a := by
    intro a b c; ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  exact_mod_cast hC i m

end GlobalTheory.NefRR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigherStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.euler_char_h0_h1_bound_higher : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  first | exact @GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | exact GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | (intros; apply GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNef

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.noSection_H1_bound_riemann_roch : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL F _ hF h0 hI hi
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi
  refine ⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩
  have he1 : 1 ≤ (d+1)*(m+1)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc hdim k (twist F (lbPow L 0)) 1 ≤ hdim k (twist F (lbPow L 0)) 1 * ((d+1)*(0+1)^d) :=
          Nat.le_mul_of_pos_right _ he1
      _ ≤ (C1 + C2 + hdim k (twist F (lbPow L 0)) 1) * ((d+1)*(0+1)^d) :=
          Nat.mul_le_mul_right _ (by omega)
  · have a1 := hC1 m
    have a2 := hC2 m
    rw [h0 m hm] at a1
    simp only [Nat.add_sub_cancel] at a2
    have hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) := mul_nonneg hI (by positivity)
    have hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d := by push_cast; ring
    rw [← hE] at a2
    have hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ) := by exact_mod_cast he1
    suffices h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤
        ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by
      exact_mod_cast h
    generalize (((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢
    generalize chi k (twist F (lbPow L m)) = c at a1 a2
    generalize interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp
    generalize (((d+1).factorial : ℕ) : ℤ) = f at a2 hfac
    generalize (hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢
    push_cast
    have hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ) := by positivity
    generalize (hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢
    have hC1' : (0:ℤ) ≤ C1 := by positivity
    have hC2' : (0:ℤ) ≤ C2 := by positivity
    rw [abs_le] at a1 a2
    simp only [CharP.cast_eq_zero, sub_zero] at a1
    have hc : -c ≤ (C2 : ℤ) * E := by
      rcases le_or_gt 0 c with hc | hc
      · nlinarith
      · nlinarith
    nlinarith
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNefStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.h1_dim_bound_of_no_sections_nonneg_interNum : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.noSection_H1_bound_riemann_roch | exact GlobalTheory.noSection_H1_bound_riemann_roch | (intros; apply GlobalTheory.noSection_H1_bound_riemann_roch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSection

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_pow_le_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL hE F _ hF p hp s hs i hi
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F (isLB_lbPow hL p) s) ≤ d := suppDim_cut_le F (isLB_lbPow hL p) s hF
  obtain ⟨C, hC⟩ := hE (cut F (isLB_lbPow hL p) s) hcut i hi
  refine sum_bound_of_step_diff (fun m => hdim k (twist F (lbPow L m)) i) d p C hp fun m => ?_
  have hcls : cls (lbPow L (m + p)) (isLB_lbPow hL (m + p)) =
      cls (lbPow L m) (isLB_lbPow hL m) + cls (lbPow L p) (isLB_lbPow hL p) := by
    rw [cls_lbPow hL (m + p), cls_lbPow hL m, cls_lbPow hL p, add_smul]
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F (lbPow L p) (lbPow L (m + p)) (lbPow L m) (isLB_lbPow hL p)
    (isLB_lbPow hL (m + p)) (isLB_lbPow hL m) s hs hcls).1 i
  have hb := hC (m + p)
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSectionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_pow_le_of_regular_section | exact GlobalTheory.hdim_twist_pow_le_of_regular_section | (intros; apply GlobalTheory.hdim_twist_pow_le_of_regular_section <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCuts

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_lbPow_le_of_two_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL ih F _ hF i hi
  obtain ⟨H, hH⟩ : ∃ H : LB X, IsAmpleLB H := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  obtain ⟨A, B, hA, hB, s, t, hs, ht, e⟩ := hH.exists_sub_of_mono_cutHom F (cls L hL)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨C₁, h₁⟩ := ih (cut F hA s) (suppDim_cut_le F hA s hF) (j + 1) (by omega)
  obtain ⟨C₂, h₂⟩ := ih (cut F hB t) (suppDim_cut_le F hB t hF) j (by omega)
  refine sum_bound_of_step_diff (fun m => hdim k (twist F (lbPow L m)) (j + 1)) d 1 (C₁ + C₂)
    le_rfl fun m => ?_
  obtain ⟨M, hM, eM⟩ := cls_surj (m • cls L hL - cls B hB)
  have a₁ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (lbPow L (m + 1)) M hA (isLB_lbPow hL _) hM s hs (by
    rw [cls_lbPow hL, eM, succ_nsmul]
    nth_rewrite 2 [e]
    abel)).1 (j + 1)
  have a₂ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F B (lbPow L m) M hB (isLB_lbPow hL _) hM t ht (by
    rw [cls_lbPow hL, eM, sub_add_cancel])).2.1 j
  have a₃ := h₁ (m + 1)
  have a₄ : hdim k (twist (cut F hB t) (lbPow L m)) j ≤ C₂ * (d * (m + 1 + 1) ^ (d - 1)) :=
    (h₂ m).trans (by gcongr; omega)
  rw [add_mul]
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCutsStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_two_cuts : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_lbPow_le_of_two_le | exact GlobalTheory.hdim_twist_lbPow_le_of_two_le | (intros; apply GlobalTheory.hdim_twist_lbPow_le_of_two_le <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthStructure

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem hdim_twist_structureModule_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hproj d L hL hkd hind i hi
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, f, hf, -⟩ := hproj
    haveI := hf
    exact LocallyOfFiniteType.isLocallyNoetherian (f ≫ PSpace.str k N)
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (suppDim_structureModule (X := X)).trans_le hkd
  by_cases hsec : ∃ p, 1 ≤ p ∧ HasNonzeroSec (lbPow L p)
  · obtain ⟨p, hp, s, hs⟩ := hsec
    have hmono : Mono (cutHom (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB p) s) :=
      (mono_cutHom_structureModule_iff _ s).mpr ((sec_ne_zero_iff s).mp hs)
    exact T.higherCohomology_twist_bound_of_regular_section k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp p hp s hmono i hi
  · push_neg at hsec
    have h0 : ∀ m, 1 ≤ m → hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 = 0 := by
      intro m hm
      by_contra hne
      exact hsec m hm (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) (Nat.pos_of_ne_zero hne))
    have hint := T.nef_intersection_nonneg_all_dims k X hproj (d + 1) (GlobalTheory.structureModule X) hsupp (fun _ => L) (fun _ => hL)
    have hi2 := T.higherCohomology_twist_bound_of_two_cuts k X hproj d L hL.isLB hind (GlobalTheory.structureModule X) hsupp
    rcases Nat.lt_or_ge i 2 with h | h
    · obtain rfl : i = 1 := by omega
      exact T.h1_dim_bound_of_no_sections_nonneg_interNum k X hproj d L hL.isLB (GlobalTheory.structureModule X) hsupp h0 hint hi2
    · exact hi2 i h

end GlobalTheory.NefRR
end
end
