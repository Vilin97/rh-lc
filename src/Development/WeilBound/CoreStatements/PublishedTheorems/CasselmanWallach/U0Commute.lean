module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ParabolicUnipotentGL
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
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
public import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryGroupStatement

section

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

theorem UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ}
      {x y : Module.End ℂ V},
      x ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j → y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k → x * y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
  intro n V _ _ E j k x y hx hy
  have h : UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j * UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k ≤ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
    unfold UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ⟨l1, hl1, rfl⟩, b, ⟨l2, hl2, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [List.map_append, List.prod_append]
  exact h (Submodule.mul_mem_mul hx hy)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.U0Commute

section

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CWB

open PositivityTheory.CW

namespace WordFiltrationCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

theorem one_mem : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem mul_mem {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) :=
  by apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption

theorem bracket_mem (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption

end WordFiltrationCommute

theorem word_filtration_of_length : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ

end PositivityTheory.CWB

end
end
end
