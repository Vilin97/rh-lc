module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqOfOpposite

section

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.Opp

open GlobalTheory.GLq.Opp



variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

theorem blk_eq (x : Gn g k) (y : Gn g l) : blk k l (k + l) x y = par finSumFinEquiv x 0 y := by
  have h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j
      else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [entN]
    · have := i.2
      simp [entN]
    · have := j.2
      simp [entN]
    · simp [entN]
  unfold blk
  rw [h, toG, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

theorem eq_par (z : Gn g (k + l)) (h0 : InPar k (z : Mt g (k + l))) (h1 : tl k (z : Mt g (k + l)) = 1)
    (h2 : br k l (z : Mt g (k + l)) = 1) : ∃ B, z = par finSumFinEquiv 1 B 1 := by
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [tl, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
    rfl
  refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
  · simp
  · rw [h0 _ _ (by simp) (by simp)]; simp
  · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

end GlobalTheory.SerSys.Opp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVector

section

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.ParVec

open GlobalTheory.GLq.Opp GlobalTheory.SerSys.Opp MonoidAlgebra

private theorem inPar_tl_br_par_one {g : ℕ} [Fact g.Prime] {a b : ℕ} (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    InPar a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) ∧
    tl a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 ∧
    br a b ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i' with i' | i'
    · have := i'.isLt
      simp at hi
      omega
    · rcases j' with j' | j'
      · simp
      · simp at hj
  · ext i j
    show entN _ i j = _
    rw [(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]
    simp [entN]
  · ext i j
    show entN _ (a + i) (a + j) = _
    rw [(entN_par (1 : Gn g a) B 1 i j).2.2.1]
    simp [entN]

theorem has_mul_of_isParVec : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  intro g _ S n V _ _ π a b χ h f v hn hχ hv hne
  subst hn
  obtain ⟨hvK, hrad, hy⟩ := hv
  let v' : fixK1 π := ⟨v, hvK⟩
  have hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x := fun x => blk_eq x 1
  have hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y := fun y => blk_eq 1 y
  let ρA : Representation ℂ (Gn g a) (fixK1 π) := (repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let ρB : Representation ℂ (Gn g b) (fixK1 π) := (repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let u : fixK1 π := ρA.asAlgebraHom (S.e a f) v'
  have hu : (u : V) = actTop π a b (S.e a f) v := by
    show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _
    rw [alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA]
    rfl
  have hv1 : ρB.asAlgebraHom (S.e b h) v' = v' := by
    rw [alg_apply]
    have hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v' := by
      intro y
      apply Subtype.ext
      show π (lift g (a + b) (inB finSumFinEquiv y)) v = _
      rw [← hB]
      exact hy y
    simp_rw [hyv, smul_smul, ← Finset.sum_smul]
    have hev := (Loc.charIn_iff S χ b h).1 hχ
    simp only [Loc.ev] at hev
    rw [hev, one_smul]
  have key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u := by
    apply S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u
    · intro u0 h0 h1 h2
      obtain ⟨B, rfl⟩ := eq_par (k := a) (l := b) u0 h0 h1 h2
      show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'

      rw [alg_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      congr 1
      have hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x =
          inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1 := by
        show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 =
          par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1
        rw [par_mul, par_mul]
        simp [← Matrix.mul_assoc]
      show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
      congr 1
      obtain ⟨r0, r1, r2⟩ := inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)
      exact Subtype.ext (hrad _ r0 r1 r2)
    · simp_rw [hA]
      have e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u := by
        rw [alg_apply]
        rfl
      rw [e2]
      show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [← Module.End.mul_apply, ← map_mul, S.idem]
    · simp_rw [hB]
      have e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u := by
        rw [alg_apply]
        rfl
      rw [e3]
      show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      have hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') =
          ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v') := by
        simp only [ρA, ρB, comp_alg]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]
      rw [hc, hv1]
  refine ⟨(u : V), u.2, ?_⟩
  rw [← repK_alg, key, hu]
  exact hne

end GlobalTheory.SerSys.ParVec
end
end
end
