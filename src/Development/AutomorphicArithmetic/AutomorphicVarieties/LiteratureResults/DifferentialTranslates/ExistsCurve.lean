module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvDeriv
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSym

section

@[expose] public section

noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem altSym : AltSym := by
  intro V F _ _ _ _ q w p L γ u D hw hL hγ hu hD
  have hA : HasFDerivAt w (fderiv ℝ w p) p := hw.hasFDerivAt
  have hDi : ∀ i, D i = fderiv ℝ w p (L i p) (fun j => L (i.succAbove j) p) +
      ∑ j : Fin q, w p (Function.update (fun j' => L (i.succAbove j') p) j
        (L (i.succAbove j) (L i p))) := by
    intro i
    have hg : ∀ j : Fin q, HasFDerivAt (fun t => u i (i.succAbove j) t)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L (i.succAbove j) (L i p))) 0 :=
      fun j => ((hu i (i.succAbove j)).2).hasFDerivAt
    have hA' : HasFDerivAt w (fderiv ℝ w p) (γ i 0) := by
      rw [(hγ i).1]
      exact hA
    have hf : HasFDerivAt (fun t => w (γ i t))
        ((fderiv ℝ w p).comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L i p))) 0 :=
      hA'.comp 0 (hγ i).2.hasFDerivAt
    have H := (hf.continuousAlternatingMap_apply hg).hasDerivAt
    rw [(hD i).unique H]
    have hu0 : ∀ j, u i j 0 = L j p := fun j => (hu i j).1
    simp [hu0, (hγ i).1]
  have hrm : ∀ i : Fin (q + 1), Fin.removeNth i (fun k => L k p) = fun j => L (i.succAbove j) p :=
    fun i => rfl
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [hDi, smul_add, Finset.sum_add_distrib, hrm]
  suffices hS : ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q,
      w p (Function.update (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = 0 by
    rw [hS, add_zero]
  set M : Fin (q + 1) → Fin (q + 1) → V := fun i k => L k (L i p) with hM
  have hMs : ∀ i k, M i k = M k i := fun i k => hL k i
  set Y : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → V :=
    fun i k m => if m = i ∨ m = k then M i k else L m p with hYdef
  set c : Fin (q + 1) → Fin (q + 1) → F :=
    fun i k => if i = k then 0 else (-1 : ℤ) ^ (i : ℕ) • w p (Fin.removeNth i (Y i k)) with hcdef
  have hc : ∀ i k, c i k + c k i = 0 := by
    intro i k
    by_cases hik : i = k
    · subst hik
      simp [c]
    · have hY : Y k i = Y i k := by
        funext m
        simp only [Y, hMs k i, or_comm]
      simp only [c, hik, Ne.symm hik, if_false, hY]
      exact (w p).neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (v := Y i k) (by simp [Y]) hik
  have hsum : ∑ i, ∑ k, c i k = 0 := by
    have h1 : ∑ i, ∑ k, c i k = -∑ i, ∑ k, c i k := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact eq_neg_iff_add_eq_zero.mpr (hc k i)
    have h2 : (2 : ℝ) • ∑ i, ∑ k, c i k = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h1]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hne : ∀ (i : Fin (q + 1)) (j : Fin q), i ≠ i.succAbove j := fun i j => (Fin.succAbove_ne i j).symm
  have hrow : ∀ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q, w p (Function.update
      (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = ∑ k, c i k := by
    intro i
    rw [Fin.sum_univ_succAbove _ i, Finset.smul_sum]
    simp only [c, if_pos rfl, zero_add, hne, if_false]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    funext j'
    by_cases hj : j' = j
    · subst hj
      simp [Fin.removeNth_apply, Y, M]
    · simp [Fin.removeNth_apply, Y, M, Function.update_of_ne hj, Fin.succAbove_ne i j', hj]
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => hrow i

end UpperTheory.V.Lit.Dr
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X : Herm E a) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1), by
        have hX : star X.1 = X.1 := X.2
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) = X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1
        rw [star_add, star_mul, star_mul, hX, hv, add_comm]⟩
      map_add' := fun p p' => Subtype.ext (by
        change X.1 * (Matrix.of p.1 + Matrix.of p'.1) + (Matrix.of p.1 + Matrix.of p'.1) * X.1 =
          (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1) + (X.1 * Matrix.of p'.1 + Matrix.of p'.1 * X.1)
        rw [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change X.1 * (c • Matrix.of p.1) + (c • Matrix.of p.1) * X.1 = c • (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1)
        rw [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem jor_one (X : Herm E a) : jor X (hOne E a) = (2 : ℝ) • hv X := Subtype.ext (by
  change X.1 * 1 + 1 * X.1 = (2 : ℝ) • X.1
  rw [mul_one, one_mul, two_smul])

private theorem jor_comm (X Y : Herm E a) : jor X (hv Y) = jor Y (hv X) := Subtype.ext (by
  change X.1 * Y.1 + Y.1 * X.1 = Y.1 * X.1 + X.1 * Y.1
  rw [add_comm])

private theorem exists_curve (X : Herm E a) : ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧
    HasDerivAt (fun t => toL (c t).val) (toL X.1) 0 ∧
    ∀ v : HV E a, HasDerivAt (fun t => sand (c t) v) (jor X v) 0 := by
  classical
  have hX : star X.1 = X.1 := X.2
  have hu : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1) := by
    have hc : Continuous fun t : ℝ => (1 + t • X.1).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    have h : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1).det :=
      hc.continuousAt.eventually (Units.isOpen.mem_nhds (by simp))
    exact h.mono fun t ht => (Matrix.isUnit_iff_isUnit_det _).2 ht
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => if h : IsUnit (1 + t • X.1) then h.unit else 1
  have hc : ∀ᶠ t : ℝ in nhds 0, (c t).val = 1 + t • X.1 :=
    hu.mono fun t ht => by simp only [c, dif_pos ht, IsUnit.unit_spec]
  refine ⟨c, Units.ext (by simpa using hc.self_of_nhds), ?_, fun v => ?_⟩
  · have h := (((hasDerivAt_id (0 : ℝ)).smul_const (toL X.1)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))))
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (hc.mono fun t ht => by
      beta_reduce
      rw [ht]; rfl)
  · let B : HV E a := ⟨toL (X.1 * Matrix.of v.1 * star X.1), IsSelfAdjoint.conjugate v.2 X.1⟩
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const (jor X v)).const_add v).add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const B)
    simp only [id, mul_zero, zero_mul, add_zero, zero_smul, one_smul] at h
    refine h.congr_of_eventuallyEq (hc.mono fun t ht => Subtype.ext ?_)
    change (c t).val * Matrix.of v.1 * star (c t).val =
      Matrix.of v.1 + t • (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) + (t * t) • (X.1 * Matrix.of v.1 * star X.1)
    rw [ht, star_add, star_one, star_smul, star_trivial t, hX]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

theorem corrD : CorrD := by
  intro E _ _ _ a ho U Ξ q α w h g x X
  choose c hc0 hc1 hc2 using fun i => exists_curve (X i)
  have hp : sand g (hOne E a) ∈ (geo ho U Ξ).Y := ⟨g, rfl⟩
  have hinv : ∀ v : HV E a, sand g⁻¹ (sand g v) = v := fun v => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  let L : Fin (q + 1) → HV E a →L[ℝ] HV E a := fun i => (sand g).comp ((jor (X i)).comp (sand g⁻¹))
  have hL : ∀ i v, L i (sand g v) = sand g (jor (X i) v) := fun i v => by
    simp only [L, ContinuousLinearMap.comp_apply, hinv]
  have hL1 : ∀ i, L i (sand g (hOne E a)) = (2 : ℝ) • sand g (hv (X i)) := fun i => by
    rw [hL, jor_one, map_smul]
  have hL2 : ∀ i j, L j (L i (sand g (hOne E a))) = (2 : ℝ) • sand g (jor (X i) (hv (X j))) := fun i j => by
    rw [hL1, map_smul, hL, jor_comm]
  have hd : ∀ i v, HasDerivAt (fun t => sand (g * c i t) v) (sand g (jor (X i) v)) 0 := fun i v => by
    have h1 := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc2 i v)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [map_mul]; rfl
  have key := altSym (HV E a) (Fin Ξ.d → ℂ) q (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) L
    (fun i t => sand (g * c i t) (hOne E a)) (fun i j t => (2 : ℝ) • sand (g * c i t) (hv (X j)))
    (fun i => Ξ.mat g *ᵥ ev (smLie Ξ (toL (X i).1) (α (i.removeNth X))) (infGL E a g * finGL E a x))
    (Geo.differentiableAt_Om w _ hp)
    (fun i j => by rw [hL2, hL2, jor_comm])
    (fun i => ⟨by rw [hc0, mul_one], by rw [hL]; exact hd i _⟩)
    (fun i j => ⟨by rw [hc0, mul_one, hL1], by rw [hL2]; exact (hd i _).const_smul (2 : ℝ)⟩)
    (fun i => by
      refine (evDeriv E a Ξ (α (i.removeNth X)) g x (c i) _ (hc0 i) (hc1 i)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ?_)
      exact h (g * c i t) x (i.removeNth X))
  rw [Geo.dOm_apply _ w _ hp]
  simp only [hL1] at key

  rw [key, dCo_apply, map_sum, Finset.sum_apply, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, Matrix.mulVec_smul]

end UpperTheory.V.Lit.Dr
end
end
end
