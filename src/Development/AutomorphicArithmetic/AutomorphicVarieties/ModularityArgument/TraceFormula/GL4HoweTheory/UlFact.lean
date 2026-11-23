module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

-- Source module: Lemmata.FirstBlockLemmaG.Imports

section

@[expose] public section

namespace Bl.FirstBlockLemmaG

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsLocalRing.{0} O] {a m : O},
  IsUnit.{0} a → Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} O) m → IsUnit.{0} (HSub.hSub.{0, 0, 0} a m) := by
  intro O _ _ a m ha hm
  by_contra h
  have h1 : a - m ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal (a - m)).mpr (mem_nonunits_iff.mpr h)
  have h2 : a ∈ IsLocalRing.maximalIdeal O := by
    have h3 := Ideal.add_mem _ h1 hm
    rwa [sub_add_cancel] at h3
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal a).mp h2)) ha

end Bl.FirstBlockLemmaG
end
end

-- Source module: Lemmata.MiscLemmasA.Imports

section

@[expose] public section

namespace Bl.SecondBlockLemmaB

theorem goal1 (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  intro n
  induction n with
  | zero =>
    intro g _ _ _
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ n ih =>
    intro g hd hU hL'
    obtain ⟨u, hu⟩ : ∃ u : O, g (Fin.last n) (Fin.last n) * u = 1 := (hd _).exists_right_inv
    have hnl : ∀ i : Fin n, ¬ (Fin.last n < i.castSucc) :=
      fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    have hcorr : ∀ i : Fin n,
        g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc ∈ U * L := fun i =>
      Ideal.mul_mem_mul (U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i)))
        (hL' _ _ (Fin.castSucc_lt_last i))
    have hAd : ∀ i : Fin n, IsUnit (g i.castSucc i.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc) := by
      intro i
      have h2 := hd i.castSucc
      rw [show g i.castSucc i.castSucc = (g i.castSucc i.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc)
        + g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc by ring] at h2
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h2 with h | h
      · exact h
      · exact absurd h (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
          (hL (Ideal.mul_le_right (hcorr i)))))
    have hAU : ∀ i j : Fin n, i < j → g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc ∈ U := by
      intro i j hij
      exact U.sub_mem (hU _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (U.mul_mem_right _ (U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i))))
    have hAL : ∀ i j : Fin n, j < i → g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc ∈ L := by
      intro i j hij
      exact L.sub_mem (hL' _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (L.mul_mem_left _ (hL' _ _ (Fin.castSucc_lt_last j)))
    obtain ⟨x', y', δ', hg, hx1, hx0, hxU, hδu, hδ, hy1, hy0, hyL⟩ :=
      ih (Matrix.of fun i j => g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc)
        (fun i => by simp only [Matrix.of_apply]; exact hAd i)
        (fun i j h => by simp only [Matrix.of_apply]; exact hAU i j h)
        (fun i j h => by simp only [Matrix.of_apply]; exact hAL i j h)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
        (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => O) (g i'.castSucc (Fin.last n) * u)
          (fun j' => x' i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
        (Fin.lastCases (motive := fun _ => O) 1 (fun j' => u * g (Fin.last n) j'.castSucc) j)
        (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => y' i' j') j) i,
      Fin.lastCases (motive := fun _ => O) (g (Fin.last n) (Fin.last n)) δ',
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp
          linear_combination (-(g (Fin.last n) j.castSucc)) * hu
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp
          linear_combination (-(g i.castSucc (Fin.last n))) * hu
        | cast j =>
          have := hg i j
          simp only [Matrix.of_apply] at this
          simp
          linear_combination this - (g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc) * hu
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [hx1 i]
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd h (hnl i)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hx0 i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          exact U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i))
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hxU i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact hd _
      | cast i => simp only [Fin.lastCases_castSucc]; exact hδu i
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i =>
        have h1 := hδ i
        simp only [Matrix.of_apply] at h1
        simp only [Fin.lastCases_castSucc]
        have e : δ' i - g i.castSucc i.castSucc = (δ' i - (g i.castSucc i.castSucc
            - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc))
            - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc := by ring
        rw [e]
        exact (U * L).sub_mem h1 (hcorr i)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [hy1 i]
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => exact absurd h (hnl j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hy0 i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          exact L.mul_mem_left _ (hL' _ _ (Fin.castSucc_lt_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd h (hnl i)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hyL i j (Fin.castSucc_lt_castSucc_iff.mp h)

end Bl.SecondBlockLemmaB
end
end

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.BaseChangeIwahoriFactorization

section

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.Z

theorem isUnit_sub_of_mem_maximalIdeal {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  first | exact Bl.FirstBlockLemmaG.goal1 .. | (apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha hm | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O

theorem iwahori_factorization_exists (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  first | exact Bl.SecondBlockLemmaB.goal1 .. | (apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O

end Formalism.IrreducibleCountingLemmas.Z
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.UlFact

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.ulFact :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a → ∀ x ∈ howeSet n ϖ a c,
      ∃ u ∈ unipB E (Fin n), ∃ b ∈ howeSet n ϖ a c, x = u * b ∧ ∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0 := by
  intro E _ _ _ _ n ϖ hϖ a c ha x hx
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (c * ((i : ℕ) : ℤ))
  let w : Fin n → Fin n → E := fun i j => ((t i * (t j)⁻¹ : Eˣ) : E)
  have hw0 : ∀ i j, w i j ≠ 0 := fun i j => Units.ne_zero _
  have hwi : ∀ i, w i i = 1 := fun i => by simp [w]
  have hww : ∀ i k j, w i k * w k j = w i j := fun i k j => by
    simp only [w]
    rw [← Units.val_mul]
    congr 1
    group
  have hpow : ∀ i j : Fin n, ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) = ((ϖ ^ a : Eˣ) : E) * w i j := fun i j => by
    simp only [w, t]
    rw [← Units.val_mul, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 2
    ring
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j * w i j = (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    by_cases h : i = j
    · subst h; rw [hwi, mul_one]
    · rw [Matrix.one_apply_ne h, zero_mul]
  have key : ∀ (i j : Fin n) (z : E), valuation E (z * w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) ↔
      valuation E (z - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun i j z => by
    rw [hpow, ← hone i j, ← sub_mul, hone, map_mul, map_mul]
    exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (hw0 i j))
  have hg : ∀ i j, valuation E ((x : Matrix (Fin n) (Fin n) E) i j / w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ a : Eˣ) : E) := fun i j => (key i j _).1 (by rw [div_mul_cancel₀ _ (hw0 i j)]; exact hx i j)
  have h1 : ∀ i j, valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hint : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j / w i j ∈ 𝒪[E] := fun i j => by
    change valuation E _ ≤ 1
    rw [← sub_add_cancel (_ / w i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hg i j).trans hlt.le) (h1 i j)
  let I : Ideal 𝒪[E] :=
    { carrier := {z | valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)}
      add_mem' := fun {y z} h h' => by
        rw [Set.mem_setOf_eq] at h h' ⊢
        rw [Subring.coe_add]
        exact Valuation.map_add_le _ h h'
      zero_mem' := by simp
      smul_mem' := fun r z h => by
        rw [Set.mem_setOf_eq] at h ⊢
        rw [smul_eq_mul, Subring.coe_mul, map_mul]
        simpa using mul_le_mul' (show valuation E (r : E) ≤ 1 from r.2) h }
  have hI : ∀ z : 𝒪[E], z ∈ I ↔ valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun _ => Iff.rfl
  have hIm : I ≤ IsLocalRing.maximalIdeal 𝒪[E] := IsLocalRing.le_maximalIdeal fun h => by
    have : (1 : 𝒪[E]) ∈ I := h ▸ Submodule.mem_top
    rw [hI] at this
    exact absurd (lt_of_le_of_lt this hlt) (by simp)
  let g : Matrix (Fin n) (Fin n) 𝒪[E] := fun i j => ⟨_, hint i j⟩
  have hgd : ∀ i, g i i - 1 ∈ I := fun i => by
    have := hg i i
    rwa [Matrix.one_apply_eq] at this
  have hgo : ∀ i j, i ≠ j → g i j ∈ I := fun i j h => by
    have := hg i j
    rwa [Matrix.one_apply_ne h, sub_zero] at this
  obtain ⟨X, Y, δ, e, x1, x0, -, -, hδ, y1, y0, yL⟩ := Formalism.IrreducibleCountingLemmas.Z.iwahori_factorization_exists 𝒪[E] I I hIm n g
    (fun i => by
      have := Formalism.IrreducibleCountingLemmas.Z.isUnit_sub_of_mem_maximalIdeal isUnit_one (hIm (I.neg_mem (hgd i)))
      simpa using this)
    (fun i j h => hgo i j h.ne) fun i j h => hgo i j h.ne'
  let U : Matrix (Fin n) (Fin n) E := fun i j => (X i j : E) * w i j
  let B : Matrix (Fin n) (Fin n) E := fun i j => ((δ i * Y i j : 𝒪[E]) : E) * w i j
  have hU0 : ∀ i j, j < i → U i j = 0 := fun i j h => by simp [U, x0 i j h]
  have hU1 : ∀ i, U i i = 1 := fun i => by simp [U, x1, hwi]
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hU0 i j h)]
    simp [hU1]
  let u : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet
  have hUB : U * B = (x : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h2 : (x : Matrix (Fin n) (Fin n) E) i j / w i j = ∑ k, (X i k : E) * δ k * Y k j := by
      have := congrArg (fun z : 𝒪[E] => (z : E)) (e i j)
      simpa [g] using this
    rw [← div_mul_cancel₀ ((x : Matrix (Fin n) (Fin n) E) i j) (hw0 i j), h2, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [U, B]
    rw [← hww i k j]
    push_cast
    ring
  have hb : ((u⁻¹ * x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = B := by
    rw [Units.val_mul, ← hUB]
    change (u⁻¹).val * (u.val * B) = B
    rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨u, (mem_unipB E).2 ⟨hU0, hU1⟩, u⁻¹ * x, fun i j => ?_, (mul_inv_cancel_left _ _).symm, fun i j h => ?_⟩
  · rw [hb]
    refine (key i j _).2 ?_
    rcases lt_trichotomy i j with h | h | h
    · rw [y0 i j h, Matrix.one_apply_ne h.ne]
      simp
    · subst h
      rw [y1, mul_one, Matrix.one_apply_eq]
      have : δ i - 1 ∈ I := by
        simpa using I.add_mem (Ideal.mul_le_left (hδ i)) (hgd i)
      exact this
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      exact (hI _).1 (I.mul_mem_left _ (yL i j h))
  · rw [hb]
    simp [B, y0 i j h]
end
end
