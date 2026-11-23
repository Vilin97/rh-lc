module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PConjRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDPairPol
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGoodConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGroupTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHeckeTraceSemi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvRoots
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMarkRoots
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolyFnConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSpecConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTraceSemi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxLin

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDSumCongr

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.dSumCongr_of :
    DSumCongr := by
  classical
  intro p _ G wt wt' s hw K f r K' φ
  unfold GlobalTheory.LKDef.dSumIrr
  rw [mul_comm _ s, ← smul_eq_mul s, smul_finsum]
  refine finsum_congr (fun q => ?_)
  split_ifs
  · rw [smul_eq_mul, hw]
    ring
  · simp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvPolProps

section

section

set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PListsEx

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.listsEx_of :
    ListsEx := by
  intro F _ _ n χ hχ
  classical
  refine ⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩
  intro τ
  have hc : ((Polynomial.map τ χ).roots.toList).length = n := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]
  have hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0)
      = (Polynomial.map τ χ).roots.toList := by
    apply List.ext_getElem
    · simp [hc]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  show (Polynomial.map τ χ).roots = _
  rw [Fin.univ_val_map, hl, Multiset.coe_toList]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PRootW

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOf

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOne

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds

section

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension

theorem InvRoots_holds : InvRoots := invRoots_of
theorem InvPolProps_holds : InvPolProps := invPolProps_of InvRoots_holds
theorem RootW_holds : RootW :=
  rootW_of UpperTheory.Gal.W2.RootSumW_holds UpperTheory.Gal.W2.RootSumWOff_holds listsEx_of schWEq_of
theorem EigOf_holds : EigOf := eigOf_of UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds
theorem CxLin_holds : CxLin := cxLin_of cxFlat_of
theorem GroupTop_of (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) : GroupTop :=
  groupTop_of h₁ h₂ RootW_holds InvRoots_holds InvPolProps_holds markRoots_of dPairPol_of dSumCongr_of testOf_of testOne_of
theorem HeckeTraceSemi_holds : HeckeTraceSemi := heckeTraceSemi_of traceSemi_of
theorem SpecConj_holds : SpecConj :=
  specConj_of traceSemi_of conjRep_of HeckeTraceSemi_holds goodConj_of (schWConj_of schWEq_of) polyFnConj_of

end UpperTheory.Gal.LocalSmoothExtension
end
end
