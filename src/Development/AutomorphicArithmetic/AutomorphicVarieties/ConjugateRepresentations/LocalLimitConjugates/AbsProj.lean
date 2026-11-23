module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsLim

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsDense

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.absDense :
    UpperTheory.V.Cj.H.AbsDense := by
  intro G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw
  set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu
  have hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y
  have hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y := by
    intro g y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let W : Submodule ℂ H :=
    { carrier := {x | ∀ v : D, inner ℂ x (u v) = 0}
      add_mem' := by
        intro a b ha hb v
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha v, hb v, add_zero]
      zero_mem' := by
        intro v
        simp only [Set.mem_setOf_eq, inner_zero_left]
      smul_mem' := by
        intro c a ha v
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha v, mul_zero] }
  have hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W := by
    refine ⟨?_, ?_⟩
    · have hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0} := by
        ext x
        simp [W]
      rw [hset]
      exact isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro g x hx v
      show inner ℂ (R g x) (u v) = 0
      have key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩ := by
        simp only [hu, map_add (f := _), map_smul]
        rw [hA g⁻¹ v]
      rw [← hinv g (u v), hinner, key]
      exact hx _
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := Submodule.mem_inf.mp hx
    have h0 : inner ℂ x (u ⟨x, hxD⟩) = 0 := hxW ⟨x, hxD⟩
    have hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0 := by
      have hs' := hsym ⟨x, hxD⟩ ⟨x, hxD⟩
      rw [← inner_conj_symm] at hs'
      exact Complex.conj_eq_iff_im.mp hs'
    simp only [hu] at h0
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have him := congrArg Complex.im h0
    simp [hre, hs] at him
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)
  have hwW : w ∈ W := hw
  rw [hirr W hW hWD] at hwW
  exact (Submodule.mem_bot ℂ).mp hwW
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsProj

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem absProj_ext {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : D → H) (hd : ∀ w : H, (∀ v : D, inner ℂ w (e v) = 0) → w = 0) (L : H →L[ℂ] H)
    (hL : ∀ v, L (e v) = 0) (w : H) : L w = 0 := by
  have hperp : (Submodule.span ℂ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply hd u
    intro v
    rw [inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).1 hu (e v) (Submodule.subset_span ⟨v, rfl⟩)
  have hcl : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have hle : Submodule.span ℂ (Set.range e) ≤ LinearMap.ker (L : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hL v
  have hle' : (Submodule.span ℂ (Set.range e)).topologicalClosure ≤ LinearMap.ker (L : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hle L.isClosed_ker
  have hw : w ∈ LinearMap.ker (L : H →ₗ[ℂ] H) := hle' (hcl ▸ Submodule.mem_top)
  exact hw

theorem UpperTheory.V.Cj.H.absProj :
    UpperTheory.V.Cj.H.AbsProj := by
  intro G H _ _ _ _ R D A hD hiso hAR hsym hirr
  set s : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hsdef
  have hs : ∀ k : ℕ, s k ≠ 0 := fun k ↦ by
    simp only [hsdef]
    positivity
  have hs0 : Filter.Tendsto s Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense : ∀ (t : ℝ), t ≠ 0 → ∀ (w : H),
      (∀ (v : ↥D), inner ℂ w (↑(A v) + (Complex.I * ↑t) • ↑v) = 0) → w = 0 :=
    absDense G H R D A hD hiso hAR hsym hirr
  have hdense' : ∀ (k : ℕ) (w : H),
      (∀ v : ↥D, inner ℂ w (↑(A v) - (Complex.I * ↑(s k)) • ↑v) = 0) → w = 0 := by
    intro k w hw
    refine hdense (-(s k)) (neg_ne_zero.2 (hs k)) w fun v ↦ ?_
    have h : (↑(A v) : H) + (Complex.I * ((-(s k) : ℝ) : ℂ)) • (↑v : H)
        = ↑(A v) - (Complex.I * ↑(s k)) • ↑v := by
      push_cast
      rw [mul_neg, neg_smul, ← sub_eq_add_neg]
    rw [h]
    exact hw v
  have hT : ∀ k : ℕ, ∃ T : H →L[ℂ] H,
      (∀ v : ↥D, T (↑(A v) + (Complex.I * ↑(s k)) • ↑v) = ↑v) ∧ ∀ w : H, |s k| * ‖T w‖ ≤ ‖w‖ :=
    fun k ↦ absInv H D A hsym (s k) (hs k) (hdense (s k) (hs k))
  choose T hTinv hTbd using hT
  have hTR : ∀ (k : ℕ) (g : G) (w : H), T k (R g w) = R g (T k w) := by
    intro k g w
    have key := absProj_ext (fun v : ↥D ↦ (↑(A v) + (Complex.I * ↑(s k)) • ↑v : H))
      (hdense (s k) (hs k)) ((T k).comp (R g) - (R g).comp (T k)) ?_ w
    · simpa [sub_eq_zero] using key
    · intro v
      have hv : (R g) ↑v ∈ D := hD g v v.2
      have h1 : (R g) (↑(A v) + (Complex.I * ↑(s k)) • ↑v)
          = ↑(A ⟨(R g) ↑v, hv⟩) + (Complex.I * ↑(s k)) • ↑(⟨(R g) ↑v, hv⟩ : ↥D) := by
        rw [map_add (f := _), map_smul, hAR g v]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      rw [h1, hTinv k ⟨(R g) ↑v, hv⟩, hTinv k v]
      simp
  set K : Submodule ℂ H := (D.subtype ∘ₗ A).range.topologicalClosure with hKdef
  set P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K.starProjection with hPdef
  have hPperp : ∀ (w : H) (v : ↥D), inner ℂ (P w) ↑(A v) = 0 := by
    intro w v
    have hAv : (↑(A v) : H) ∈ K :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (D.subtype ∘ₗ A) v)
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact Submodule.inner_left_of_mem_orthogonal hAv (K.sub_starProjection_mem_orthogonal w)
  have hclose : ∀ w : H, w - P w ∈ (D.subtype ∘ₗ A).range.topologicalClosure := by
    intro w
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
    exact K.starProjection_apply_mem w
  have hlim := absLim H D A hsym s hs0 (fun k ↦ hdense (s k) (hs k)) hdense' T hTinv hTbd P
    hPperp hclose
  refine ⟨P, fun k ↦ (Complex.I * ↑(s k)) • T k, T, ?_, ?_, ?_, ?_, hPperp, ?_⟩
  · intro g w
    have h2 : Filter.Tendsto (fun k ↦ (Complex.I * ↑(s k)) • T k (R g w)) Filter.atTop
        (𝓝 (R g (P w))) := by
      refine (((R g).continuous.tendsto _).comp (hlim w)).congr fun k ↦ ?_
      simp [Function.comp_apply, map_smul, hTR k g w]
    exact tendsto_nhds_unique (hlim (R g w)) h2
  · intro k g w
    simp [ContinuousLinearMap.smul_apply, map_smul, hTR k g w]
  · intro k g w
    exact hTR k g w
  · intro k v
    have h := hTinv k v
    rw [map_add (f := _), map_smul] at h
    rw [ContinuousLinearMap.smul_apply]
    exact (eq_sub_of_add_eq h).symm
  · intro w
    simpa only [ContinuousLinearMap.smul_apply] using hlim w
end
end
