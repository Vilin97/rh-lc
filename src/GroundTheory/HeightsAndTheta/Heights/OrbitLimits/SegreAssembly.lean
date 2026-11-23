module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreDivisor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartDimBound
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
public import Mathlib.RingTheory.Ideal.Height
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrel
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartFiniteIrrel
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDimBound

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartDimBound.proof : ChartDimBound.Statement.{u, v, w} := by
  intro K _ ι _ F _ V i hV hi
  classical
  obtain ⟨hVp, hVh, -⟩ := hV
  let f : K → MRingOver F ι := fun k => X ⟨k, i k⟩ - 1
  let t : Set (MRingOver F ι ⧸ V) := Set.range (Ideal.Quotient.mk V ∘ f)
  have hspan : Ideal.span t = (Ideal.span (Set.range f)).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, ← Set.range_comp]
  let e : (MRingOver F ι ⧸ V) ⧸ Ideal.span t ≃+* MRingOver F ι ⧸ chartIdeal V i :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup V _)
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V) (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have hne : Ideal.span t ≠ ⊤ := by
    have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) :=
      Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hVh hi)
    have : Nontrivial ((MRingOver F ι ⧸ V) ⧸ Ideal.span t) := e.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp this
  obtain ⟨M, hM, htM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have : M.IsPrime := hM.isPrime
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) t
    (fun x hx => htM (Ideal.subset_span hx))
  rw [ringKrullDim_eq_of_ringEquiv e] at h1
  have h2 : t.encard ≤ Fintype.card K := by
    calc t.encard = ((Ideal.Quotient.mk V ∘ f) '' Set.univ).encard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set K).encard := Set.encard_image_le _ _
      _ = Fintype.card K := by simp [Set.encard_univ]
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun N hN => ?_
  rw [hs N hN, ← hs M hM]
  refine h1.trans ?_
  gcongr
  exact_mod_cast h2

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreComponent

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem SegreComponent.proof (h₁ : ChartDimBound.Statement.{u, v, w})
    (h₂ : ChartFiniteIrrel.Statement.{u, v, w}) : SegreComponent.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n f hV hf
  by_contra hne
  have hirr : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ IsRelevant W :=
    fun W hW hrel => hne ⟨W, hW, hrel⟩
  obtain ⟨i, hi⟩ : ∃ i, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  have := h₂ K ι F V f i hV.1.2.1 hf hirr
  have : IsArtinianRing (MRingOver F ι ⧸ chartIdeal V i) :=
    IsArtinianRing.of_finite F (MRingOver F ι ⧸ chartIdeal V i)
  have hA : ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp inferInstance
  have hdim := h₁ K ι F V i hV.1 hi
  rw [hV.2] at hdim
  have h := hdim.trans (add_le_add hA le_rfl)
  rw [Nat.cast_zero, zero_add] at h
  have h' : n + 1 + Fintype.card K ≤ Fintype.card K := by exact_mod_cast h
  omega

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreDivisor

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem multAt_pos_of_mem_divSupp_field {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∈ divSupp V f) : 0 < multAt (V ⊔ Ideal.span {f}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

theorem SegreDivisor.proof (h₁ : SegreComponent.Statement.{u, v, w}) :
    SegreDivisor.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n hV
  obtain ⟨i, hi⟩ : ∃ i : ∀ k, ι k, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  refine ⟨_, isMultiHomog_coordProd (F := F) i (fun _ => 1), coordProd_not_mem hV.1.1 i hi _, ?_⟩
  obtain ⟨W, hW⟩ := h₁ K ι F V n _ hV (isMultiHomog_coordProd (F := F) i (fun _ => 1))
  intro h0
  have hpos := multAt_pos_of_mem_divSupp_field hW
  rw [← DivisorCycleSwap.divCycle_apply_of_mem hW, h0, Finsupp.zero_apply] at hpos
  exact lt_irrefl _ hpos

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Positivity

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]

theorem exists_isChart_of_isProjVarF {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n) :
    ∃ i, IsChart V i :=
  ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩

theorem ratDiv_one_eq_mapRange (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    ratDiv V f 1 = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle V f) := by
  simp [ratDiv, divCycle_one]

theorem cycEval_ratDiv_one_nonneg (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (h : ∀ W ∈ divSupp V f, 0 ≤ J W) : 0 ≤ cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  exact Finset.sum_nonneg fun W hW => mul_nonneg (Nat.cast_nonneg _)
    (h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW)))

theorem cycEval_ratDiv_one_pos (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (hne : divCycle V f ≠ 0) (h : ∀ W ∈ divSupp V f, 0 < J W) :
    0 < cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  refine Finset.sum_pos (fun W hW => mul_pos ?_ ?_) (Finsupp.support_nonempty_iff.mpr hne)
  · exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)
  · exact h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW))

theorem ptDeg_pos {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) : 0 < ptDeg V i := by
  have := chart_finite hV hi
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨(chart_isField hV hi).exists_pair_ne⟩
  exact Module.finrank_pos

theorem nonneg_of_isFieldIntersection {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n →
      ∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L := by
  intro n
  induction n with
  | zero =>
    intro V hV L _
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V L i hV hi]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro V hV L hL
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    have hf := isMultiHomog_coordProd (F := F) i (fun k => (L (Fin.last n) k).toNat)
    have hfV := coordProd_not_mem hV.1.1 i hi (fun k => (L (Fin.last n) k).toNat)
    have hsec : IsRatSection V (L (Fin.last n))
        (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (L (Fin.last n) k).toNat) 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h),
        fun k => by simp [Int.toNat_of_nonneg (hL _ k)]⟩
    rw [← Fin.snoc_init_self (α := fun _ => K → ℤ) L, hI.2 V n (Fin.init L) _ _ 1 hV hsec]
    exact cycEval_ratDiv_one_nonneg _ _ _ fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW) _ fun j k => hL _ k


omit [Fintype K] in
theorem const_one_eq_snoc (n : ℕ) :
    (fun _ _ => (1 : ℤ) : Fin (n + 1) → K → ℤ) =
      Fin.snoc (α := fun _ => K → ℤ) (fun _ _ => 1) (fun _ => 1) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem segre_pos_of_isFieldIntersection (hS : SegreDivisor.Statement.{u, v, w})
    {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n → 0 < I V n (fun _ _ => 1) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V _ i hV hi]
    exact_mod_cast ptDeg_pos hV hi
  | succ n ih =>
    intro V hV
    obtain ⟨f, hf, hfV, hne⟩ := hS K ι F V n hV
    have hsec : IsRatSection V (fun _ => 1) f 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h), fun k => by simp⟩
    rw [const_one_eq_snoc, hI.2 V n _ _ f 1 hV hsec]
    exact cycEval_ratDiv_one_pos _ _ _ hne fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW)

end

theorem Positivity.of_found (hS : SegreDivisor.Statement.{u, v, w}) {K : Type u} [Fintype K]
    (F : Type w) [Field F] (ι : K → Type v) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  fun _ hI V n hV =>
    ⟨fun L hL => nonneg_of_isFieldIntersection hI n V hV L hL,
      segre_pos_of_isFieldIntersection hS hI n V hV⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreAssembly

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

universe u v w

theorem SegreComponent.full : SegreComponent.Statement.{u, v, w} :=
  SegreComponent.proof ChartDimBound.proof ChartFiniteIrrel.proof

theorem SegreDivisor.full : SegreDivisor.Statement.{u, v, w} :=
  SegreDivisor.proof SegreComponent.full

theorem Positivity.full {K : Type u} [Fintype K] (F : Type w) [Field F] (ι : K → Type v)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  Positivity.of_found SegreDivisor.full F ι

end GroundTheory.Heights₂.Heights.Targets
end
end
