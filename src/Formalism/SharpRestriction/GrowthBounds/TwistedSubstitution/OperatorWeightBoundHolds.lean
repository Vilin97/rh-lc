module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
public import Formalism.PeriodIntegrals.RowWtSpan
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.MemHdIff
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OpWords
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter
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
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePos
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.RWS

open PI.RW

def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0

theorem RE_eq_of_hom {K : Type} [CommRing K] {k : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin k) K) (d : ℕ)
    (h : IsWeightedHomogeneous (rowW a) f d) : RE K k a a f = (d : K) • f := by
  have h' := h.sum_weight_X_mul_pderiv
  unfold RE
  rw [Nat.cast_smul_eq_nsmul K d f, ← h']
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp [rowW]

theorem minor_hom {K : Type} [CommRing K] {k s : ℕ} (a : Fin k) (I : Fin s → Fin k) (hs : s ≤ k) :
    IsWeightedHomogeneous (rowW a) (initMinor K I hs)
      (Finset.univ.filter fun p => I p = a).card := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin k × Fin k) K))
    (fun i => rowW a (I (σ i), Fin.castLE hs i)) (w := rowW a)
    (fun i _ => isWeightedHomogeneous_X K (rowW a) _)
  have hdeg : ∑ i, rowW a (I (σ i), Fin.castLE hs i) =
      (Finset.univ.filter fun p => I p = a).card := by
    simp only [rowW]
    rw [Finset.card_filter]
    exact Equiv.sum_comp σ (fun p => if I p = a then 1 else 0)
  rw [hdeg] at hp
  rw [Units.smul_def, ← mem_weightedHomogeneousSubmodule] at *
  exact zsmul_mem hp _

theorem bidet_hom {K : Type} [CommRing K] {k N : ℕ} (a : Fin k) (sz : Fin N → ℕ)
    (hsz : ∀ j, sz j ≤ k) (I : ∀ j, Fin (sz j) → Fin k) :
    IsWeightedHomogeneous (rowW a) (bideterminant K sz hsz I)
      (∑ j, (Finset.univ.filter fun p => I j p = a).card) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => minor_hom a (I j) (hsz j)

theorem wt_le {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by
  unfold shapeDeg
  rw [ht0, Finset.card_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : 0 < sz j
  · rw [if_pos hj]
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (hI j).injective (hp.trans hq.symm)
  · rw [if_neg hj]
    have hem : (Finset.univ : Finset (Fin (sz j))) = ∅ :=
      Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩
    rw [hem]
    simp

theorem rowWtSpan_of_bideterminant (h1 : BideterminantMem) (h2 : BideterminantSpan) : PI.RowWtSpan := by
  intro K _ m ν _
  refine ⟨{d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
      (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)},
    fun d => bideterminant K d.1.2.1 d.2.1 d.1.2.2,
    fun d a => ∑ j, (Finset.univ.filter fun p => d.1.2.2 j p = a).card, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
      subst hsh
      exact h1 K (m + 1) (m + 1) N sz hsz I
    · refine le_trans (h2 K (m + 1) (m + 1) ν) (Submodule.span_mono ?_)
      rintro f ⟨N, sz, hsz, I, hsh, hmono, rfl⟩
      exact ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    exact RE_eq_of_hom a _ _ (bidet_hom a sz hsz I)
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    have hw := wt_le sz I hmono a 0 rfl
    rw [hsh] at hw
    exact hw

end PI.RWS
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowWtSpan

section

@[expose] public section

theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.GradedWeylDivisibility

private theorem initMinor_comp_perm_eq_sign_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) :
    PI.RW.initMinor R (I ∘ σ) hs =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) * PI.RW.initMinor R I hs := by
  unfold PI.RW.initMinor
  rw [← Matrix.det_permute σ]
  rfl

private theorem initMinor_eq_zero_of_not_injective {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : ¬ Function.Injective I) : PI.RW.initMinor R I hs = 0 := by
  unfold PI.RW.initMinor
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq (Ne.symm (Ne.symm hne)) (by
    funext q
    simp [hij])

private theorem initMinor_eq_sign_sort_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : Function.Injective I) :
    PI.RW.initMinor R I hs =
      ((((Equiv.Perm.sign (Tuple.sort I) : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) *
        PI.RW.initMinor R (I ∘ Tuple.sort I) hs := by
  rw [initMinor_comp_perm_eq_sign_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem bideterminant_span_holds : PI.RW.BideterminantSpan := by
  intro R _ _ k n ν
  rw [show PI.RW.dualWeyl R k n ν = Formalism.GradedWeylDivisibility.dualWeyl R k n ν from rfl,
    Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R k n ν]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hν, rfl⟩
  by_cases hinj : ∀ i, Function.Injective (I i)
  · have hb : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I =
        (∏ i, ((((Equiv.Perm.sign (Tuple.sort (I i)) : ℤˣ) : ℤ) : MvPolynomial (Fin k × Fin n) R))) *
          PI.RW.bideterminant R sz hsz (fun i => I i ∘ Tuple.sort (I i)) := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = _
      unfold PI.RW.bideterminant
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => initMinor_eq_sign_sort_mul (I i) (hsz i) (hinj i))
    rw [hb, ← Int.cast_prod, ← zsmul_eq_mul]
    have hJ : ∀ i, StrictMono (I i ∘ Tuple.sort (I i)) := fun i =>
      (Tuple.monotone_sort (I i)).strictMono_of_injective ((hinj i).comp (Equiv.injective _))
    refine zsmul_mem (Submodule.subset_span ?_) _
    exact ⟨K, sz, hsz, fun i => I i ∘ Tuple.sort (I i), hν, hJ, rfl⟩
  · push_neg at hinj
    obtain ⟨i, hi⟩ := hinj
    have h0 : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I = 0 := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (initMinor_eq_zero_of_not_injective (I i) (hsz i) hi)
    rw [h0]
    exact Submodule.zero_mem _

theorem dual_weyl_weights_bounded : Formalism.MainNotions.TestSideCounting.RestWt := rowWtSpan_of bidetMem bideterminant_span_holds

theorem letter_operators_holds : Formalism.MainNotions.TestSideCounting.RestTheta := row_letter_rule

theorem onePos_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.OnePos :=
  Formalism.MainNotions.TestSideCounting.onePos_of_opBound hOB letter_operators_holds dual_weyl_weights_bounded

theorem tensor_operators_of_one_position (h : Formalism.MainNotions.TestSideCounting.OnePos) : Formalism.MainNotions.TestSideCounting.TenOp :=
  adjointTensorOfSingle_valid Formalism.L2.G.Model.TS.Top.fockRBlock h

theorem tenOp_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.TenOp := tensor_operators_of_one_position (onePos_of_OB hOB)

theorem operator_weight_bound_holds : Formalism.MainNotions.TestSideCounting.OpBound := operator_words_bound

theorem tensor_operators_holds : Formalism.MainNotions.TestSideCounting.TenOp := tenOp_of_OB operator_weight_bound_holds

end Formalism.MainNotions.TestSideWords
end
end
end
