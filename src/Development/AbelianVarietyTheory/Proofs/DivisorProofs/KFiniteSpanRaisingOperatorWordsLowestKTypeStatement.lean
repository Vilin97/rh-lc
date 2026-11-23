module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilledStatement
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRepStatement

section

@[expose] public section

open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open CompanionTheory.D.LK (IsKMod)

theorem GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D),
      CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E →
      ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ :=
  @GlobalTheory.KFinIrr.kMod_irred
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingWordSpanStableOfLoweringKill

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.raisingSpan_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  intro n ε V _ _ E hG L hK hL
  set S := Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have gen : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x ∈ S :=
    fun l hl x hx => Submodule.subset_span ⟨l, hl, x, hx, rfl⟩
  have pre : ∀ c d, ε c = true → ε d = false → ∀ y ∈ S, E c d y ∈ S := by
    intro c d hc hd y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hz
      have h1 := gen ((c, d) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hc, hd⟩
        · exact hl p hp) x hx
      simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
    | zero => rw [map_zero]; exact S.zero_mem
    | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
  have main : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      ∀ a b, E a b ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x) ∈ S := by
    intro l
    induction l with
    | nil =>
      intro _ x hx a b
      simp only [List.map_nil, List.prod_nil, Module.End.one_apply]
      cases ha : ε a <;> cases hb : ε b
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
      · rw [hL b a hb ha x hx]; exact S.zero_mem
      · have h1 := gen [(a, b)] (by simp [ha, hb]) x hx
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h1
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
    | cons q l ih =>
      obtain ⟨c, d⟩ := q
      intro hl x hx a b
      have hl' : ∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false := fun p hp => hl p (List.mem_cons_of_mem _ hp)
      have hcd : ε c = true ∧ ε d = false := hl (c, d) (by simp)
      have ih' := ih hl' x hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      set z := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x
      have key : E a b (E c d z) = E c d (E a b z) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) z := by
        rw [← hG a b c d, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [key, LinearMap.sub_apply]
      refine S.add_mem (pre c d hcd.1 hcd.2 _ (ih' a b)) (S.sub_mem ?_ ?_)
      · split_ifs
        · exact ih' a d
        · rw [LinearMap.zero_apply]; exact S.zero_mem
      · split_ifs
        · exact ih' c b
        · rw [LinearMap.zero_apply]; exact S.zero_mem
  intro a b y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, x, hx, rfl⟩ := hz
    exact main l hl x hx a b
  | zero => rw [map_zero]; exact S.zero_mem
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
  | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingWordSpanStableOfLoweringKillStatement

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.raisingWordSpan_stable_of_lowering_kill : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  first | exact @GlobalTheory.HolDS.raisingSpan_stable | exact GlobalTheory.HolDS.raisingSpan_stable | (intros; apply GlobalTheory.HolDS.raisingSpan_stable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKType

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

theorem kfin_span_raising_words_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} = ⊤ := by
  intro n ε H _ _ σ D E lam hHC hCh hDS hK
  obtain ⟨_, hKS, hne, hkill⟩ := GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed n ε H σ D E lam hHC hCh hDS hK
  haveI : CompleteSpace H := hDS.1
  set L := (lowKSub ε lam σ).comap D.subtype with hL
  set S := Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := fun a b x hx =>
    GlobalTheory.T.raisingWordSpan_stable_of_lowering_kill n ε D E hK.gl L hKS hkill a b x hx
  have hLS : L ≤ S := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨[], by simp, x, hx, by simp⟩
  rcases GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep n ε H σ D E hDS.1 hDS.2.2.1 hDS.2.2.2.1 hK S hstab with h | h
  · exfalso
    apply hne
    exact le_bot_iff.mp (h ▸ hLS)
  · exact h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKTypeStatement

section

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} = ⊤ :=
  @GlobalTheory.kfin_span_raising_words_lowK
end
end
