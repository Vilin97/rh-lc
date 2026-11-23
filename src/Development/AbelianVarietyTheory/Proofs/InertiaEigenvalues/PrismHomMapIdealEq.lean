module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Mathlib.RingTheory.PicardGroup
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMemStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem ideal_dual_symm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (x y : ↥I) : f x * (y : A) = f y * (x : A) := by
  have h : (x : A) • y = (y : A) • x := Subtype.ext (by simp [mul_comm])
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm (f x), ← this, mul_comm]

theorem invertible_ideal_eq_of_not_le_maximal_mul (A : Type) [CommRing A] (I N : Ideal A) :
    Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  intro hI hNI hm

  set c : Ideal A := N.colon I with hc
  have key : ∀ (f : Module.Dual A ↥I) (n : ↥I), (n : A) ∈ N → f n ∈ c := by
    intro f n hn
    rw [hc, Submodule.mem_colon]
    intro p hp
    rw [smul_eq_mul, ideal_dual_symm I f n ⟨p, hp⟩]
    exact N.mul_mem_left _ hn
  have hcTop : c = ⊤ := by
    by_contra hne
    obtain ⟨m, hmax, hcm⟩ := Ideal.exists_le_maximal c hne
    apply hm m hmax
    intro n hn
    obtain ⟨t, ht⟩ := hI.bijective.2 1
    have hall : ∀ t : Module.Dual A ↥I ⊗[A] ↥I, contractLeft A ↥I t * n ∈ m * I := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [contractLeft_apply, ideal_dual_symm I f x ⟨n, hNI hn⟩]
        exact Ideal.mul_mem_mul (hcm (key f ⟨n, hNI hn⟩ hn)) x.2
      | add s u hs hu => rw [map_add (f := _), add_mul]; exact Ideal.add_mem _ hs hu
    simpa [ht] using hall t
  apply le_antisymm hNI
  intro y hy
  have h1 : (1 : A) ∈ c := hcTop ▸ Submodule.mem_top
  rw [hc, Submodule.mem_colon] at h1
  simpa using h1 y hy

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul : ∀ (A : Type) [CommRing A] (I N : Ideal A), Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  first | exact @GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | exact GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | (intros; apply GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
end
end
end
