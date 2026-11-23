module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Formalism.RealPlaceAnalysis.StatementA
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeLeKFiniteVectorsFiniteDimensionalStatement
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeigStatement
import Formalism.RealPlaceAnalysis.StatementKT

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZero

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.SignInnerAdjoint

theorem sgn_sq_one {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε a b : ℂ) = 1 := by
  unfold Formalism.REAL.sgn; split_ifs <;> norm_num

theorem sgn_symm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
  unfold Formalism.REAL.sgn; split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem inner_E_right {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (a b : Fin n) (w y : V) :
    ⟪w, E a b y⟫_ℂ = (Formalism.REAL.sgn ε a b : ℂ) * ⟪E b a w, y⟫_ℂ := by
  rw [hU b a w y, sgn_symm, ← mul_assoc, sgn_sq_one, one_mul]

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (l : List (Fin n × Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ∀ w x : V,
      ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ =
        c * ⟪((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w, x⟫_ℂ := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun w x => by simp⟩
  | cons p t ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨(Formalism.REAL.sgn ε p.1 p.2 : ℂ) * c, mul_ne_zero ?_ hc, fun w x => ?_⟩
    · intro h0; have := sgn_sq_one ε p.1 p.2; rw [h0] at this; simp at this
    · simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.map_nil, List.prod_append, List.prod_nil, mul_one, Module.End.mul_apply,
        Prod.fst_swap, Prod.snd_swap] at h ⊢
      rw [inner_E_right hU, h, mul_assoc]

end GlobalTheory.SignInnerAdjoint

theorem GlobalTheory.SignInnerAdjoint.main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  intro n ε V _ _ E hU l w x hne
  obtain ⟨c, hc, h⟩ := GlobalTheory.SignInnerAdjoint.word_adj hU l
  rw [h] at hne
  have h2 := right_ne_zero_of_mul hne
  intro h3; exact h2 (inner_eq_zero_symm.mp h3)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZeroStatement

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  first | exact @GlobalTheory.SignInnerAdjoint.main | exact GlobalTheory.SignInnerAdjoint.main | (intros; apply GlobalTheory.SignInnerAdjoint.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMapRootEqSumCount

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_map_root_eq_sum_count {n : ℕ} (l : List (Fin n × Fin n)) :
    (l.map fun p : Fin n × Fin n => root p.1 p.2).sum
      = ∑ a, ∑ b, (l.count (a, b) : ℝ) • root a b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.count_cons, Nat.cast_add, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨x, y⟩ := p
    simp only [beq_iff_eq, Prod.mk.injEq]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp

theorem root_word_count_letters : ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = false ∧ ε p.2 = true) → μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = Λ + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε μ Λ l hl hsum
  refine ⟨fun a b => l.count (b, a), ?_, ?_⟩
  · intro a b h
    have hm : (b, a) ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨(hl _ hm).2, (hl _ hm).1⟩
  · rw [sum_map_root_eq_sum_count] at hsum
    have key : ∑ a, ∑ b, ((l.count (b, a) : ℕ) : ℝ) • root a b
        = - ∑ a, ∑ b, ((l.count (a, b) : ℕ) : ℝ) • root a b := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have : root b a = - root a b := by
        unfold root; abel
      rw [this, smul_neg]
    rw [key, ← hsum]; abel

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKType

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kType_weight_in_cone_over_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε H _ _ σ D E lam hP hC hDS hK μ S hS
  have hcomp : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hI : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨w, hw0, -, hwH⟩ := hK.hw μ S hS
  have key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype,
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 := by
    by_contra hne
    let Q : Submodule ℂ D :=
      { carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) →
          ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0}
        add_mem' := by
          intro a b ha hb l hl
          rw [map_add (f := _), inner_add_right, ha l hl, hb l hl, add_zero]
        zero_mem' := by
          intro l hl
          rw [map_zero, inner_zero_right]
        smul_mem' := by
          intro c a ha l hl
          rw [map_smul, inner_smul_right, ha l hl, mul_zero] }
    have hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype := by
      intro T hT y hy
      have hTD := (GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT).1
      refine ⟨⟨y, hTD hy⟩, ?_, rfl⟩
      intro l hl
      by_contra h
      exact hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩
    have hlow : lowKSub ε lam σ ≤ Q.map D.subtype := sSup_le hT
    have hspan := GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hP hC hDS hK
    have hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤
        (ℂ ∙ w)ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨l, hl, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨x', hx', hxx⟩ := hlow hx
      have : x' = x := Subtype.ext hxx
      subst this
      exact hx' l hl
    rw [hspan] at hle
    have hw : w ∈ (ℂ ∙ w)ᗮ := hle Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hw
    exact hw0 hw
  obtain ⟨T, hT, x, hx, l, hl, hne⟩ := key
  have hadj := GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero n ε D E hK.unit l w x hne
  obtain ⟨-, hfd, hstab, hhw⟩ := GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT
  have hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [List.mem_reverse] at hq
    exact ⟨(hl q hq).2, (hl q hq).1⟩
  have hKU : KUnit ε E := fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z
  obtain ⟨l', -, hl'ty, hsum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw
    μ w hwH false true _ hl' x hx hadj
  exact GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKTypeStatement

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (root)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsKTypeOf IsDS)
open CompanionTheory.D.LK (IsKMod)

theorem _root_.GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  exact @GlobalTheory.kType_weight_in_cone_over_lowK
end
end
