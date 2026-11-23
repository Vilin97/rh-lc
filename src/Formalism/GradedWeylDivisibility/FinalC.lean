module

public import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
import Formalism.GradedWeylDivisibility.StatementC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCcompLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.EvalDeg
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetdomLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadInterlaced
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.MinorExpLt
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDecomp
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDegBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelHomog
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelLead
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTExists
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTPeel
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TwoColumn
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColumnLexBideterminant

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by
  intro R _ _ r n K sz hsz I hI
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1 :=
    fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2
  have hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k))) := by
    intro k hk
    rw [hm k hk]
    exact isRegular_one
  refine ⟨?_, ?_⟩
  · unfold bideterminant bidetExp
    rw [MonomialOrder.degree_prod_of_regular hreg]
    exact Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1
  · unfold bideterminant
    rw [MonomialOrder.leadingCoeff_prod_of_regular hreg]
    exact Finset.prod_eq_one hm

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.CompDeg

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem componentDegree : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadComp

section

section

open MvPolynomial

open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem leadingComponent : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.SMSAssembly

section

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem semistandard_module_assembly : SMSAssembly := by
  intro hCL hCS hSS hLI B _ _ r n ν
  apply le_antisymm
  · have key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl B r n ν,
        (colLex r n).toSyn ((colLex r n).degree f) = d →
        f ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
          (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        have hm := (colLex r n).degree_mem_support hf0
        obtain ⟨K, sz, hsz, I, hsh, hmono, hexp⟩ :=
          hSS r n ν _ (hCS B r n ν f hf _ hm) (hLI B r n ν f hf hf0)
        obtain ⟨hdeg, hlc⟩ := hCL B r n K sz hsz I hmono
        have hg : bideterminant B sz hsz I ∈ dualWeyl B r n ν := by
          rw [← hsh]; exact bidetMem B r n K sz hsz I
        have hgS : bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ)
            (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
            shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} :=
          Submodule.subset_span ⟨K, sz, hsz, I, hsh, rfl⟩
        have hf' : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ dualWeyl B r n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hg)
        have h1 : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ Submodule.span B
            {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
              shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
          by_cases hne : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I = 0
          · rw [hne]; exact Submodule.zero_mem _
          have hlt := lcassem_sub_lt (colLex r n) (hdeg.trans hexp) hlc hne
          exact ih _ (by rw [← hd]; exact hlt) _ hf' rfl
        have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ ((colLex r n).leadingCoeff f) hgS)
        rwa [sub_add_cancel] at h2
    exact fun f hf => key _ f hf rfl
  · rw [Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← hsh]
    exact bidetMem B r n K sz hsz I

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.StandardMonomialSpanOf

section

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.FinalC

section

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem minorExpLt : MinorExpLt := minorExponentLt
theorem colLexInitMinor : ColLexInitMinor := colLexInitMinor_of minorExpLt
theorem column_lex_bideterminant : ColumnLexBideterminant := columnLexBideterminant_of_initialMinor colLexInitMinor
theorem colSums : ColSums := columnSums_holds
theorem sSYTPeel : SSYTPeel := semistandardPeel
theorem sSYTExists : SSYTExists := sSYTExists_of sSYTPeel
theorem compDeg : CompDeg := componentDegree
theorem leadComp : LeadComp := leadingComponent
theorem peelDecomp : PeelDecomp := peelDecomposition
theorem peelHomog : PeelHomog := sliceHomogeneous
theorem peelLead : PeelLead := sliceLeading
theorem evalDeg : EvalDeg := evalDegree
theorem peelDegBound : PeelDegBound := peelDegBound_of evalDeg
theorem twoColumn : TwoColumn := twoColumn_of peelDecomp peelHomog peelLead peelDegBound
theorem leadInterlaced : LeadInterlaced := leadInterlaced_of compDeg leadComp twoColumn
theorem standardMonomialSpanDomain : StandardMonomialSpanDomain :=
  semistandard_module_assembly column_lex_bideterminant colSums sSYTExists leadInterlaced

theorem standardMonomialSpan : StandardMonomialSpan :=
  standardMonomialSpanOf standardMonomialSpanDomain

private theorem bidet_rowPart_lemma {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (k : ℕ) :
    ∀ (s : Finset (Fin K)) (m : Fin r × Fin n →₀ ℕ),
      m ∈ (∏ j ∈ s, initMinor ℤ (I j) (hsz j)).support → rowPart k m ≤ ∑ j ∈ s, min k (sz j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    simp only [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra h
      apply (MvPolynomial.mem_support_iff.mp hm)
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)]
    subst hm0
    simp [rowPart_zero]
  | @insert j s hj ih =>
    intro m hm
    rw [Finset.prod_insert hj] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [rowPart_add, Finset.sum_insert hj]
    exact Nat.add_le_add ((initMinor_support (I j) (hsz j) m1 hm1).1 k) (ih m2 hm2)

private theorem sum_rowNu_lemma_2 {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ j, sz j ≤ n) (hnr : n ≤ r)
    (k : ℕ) :
    ∑ j : Fin K, min k (sz j) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) (shapeDeg (n := n) sz) a := by
  classical
  have h1 : ∀ a : Fin r, rowNu (r := r) (shapeDeg (n := n) sz) a =
      ∑ j : Fin K, if a.val < sz j then 1 else 0 := by
    intro a
    unfold rowNu
    split_ifs with h
    · unfold shapeDeg
      rw [Finset.card_filter]
    · symm
      apply Finset.sum_eq_zero
      intro j _
      have := hsz j
      exact if_neg (by omega)
  have h2 : ∀ j : Fin K, min k (sz j) = ∑ a : Fin r with a.val < k, if a.val < sz j then 1 else 0 := by
    intro j
    have hj : sz j ≤ r := (hsz j).trans hnr
    rw [← Finset.card_filter, Finset.filter_filter]
    have hset : (Finset.univ.filter fun a : Fin r => a.val < k ∧ a.val < sz j).map Fin.valEmbedding =
        Finset.range (min k (sz j)) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        omega
      · intro hx
        exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hset, Finset.card_range]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  exact le_of_eq (Finset.sum_congr rfl (fun j _ => h2 j))

theorem dualWeylDominanceZ :
    ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → Antitone ν → ∀ f ∈ dualWeyl ℤ r n ν, ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a) ∧
      ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, rowNu (r := r) ν a := by
  intro r n ν hnr hν f hf m hm
  have hcol := colSums ℤ r n ν f hf m hm
  refine ⟨fun k => ?_, ?_⟩
  · rw [standardMonomialSpan r n ν hν] at hf
    clear hcol
    show rowPart k m ≤ _
    induction hf using Submodule.span_induction generalizing m with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hν', rfl⟩ := hx
      subst hν'
      exact (bidet_rowPart_lemma sz hsz I k Finset.univ m hm).trans (sum_rowNu_lemma_2 sz hsz hnr k)
    | zero => simp at hm
    | add x y _ _ ihx ihy =>
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · exact ihx m h
      · exact ihy m h
    | smul a x _ ihx =>
      exact ihx m (MvPolynomial.support_smul hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnr
    have hL : ∑ a : Fin (n + d), rowDeg m a = ∑ s : Fin n, ν s := by
      unfold rowDeg
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun s _ => hcol s)
    rw [hL, Fin.sum_univ_add]
    simp [rowNu]

end Formalism.GradedWeylDivisibility
end
end
