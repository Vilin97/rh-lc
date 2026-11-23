module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
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
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenKill

section

@[expose] public section

noncomputable section

open Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def gpoly (Λ : ℂ) : ℝ[X] := X ^ 2 - C (2 * Λ.re) * X + C (Complex.normSq Λ)

theorem gpoly_eval_one (Λ : ℂ) : (gpoly Λ).eval 1 = Complex.normSq (1 - Λ) := by
  simp only [gpoly, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem mapOp_apply {A : Type} (φ : A → A) (m : ℕ) (F : (Fin m → A) → ℝ) (y : Fin m → A) :
    mapOp φ m F y = F fun i => φ (y i) := rfl

theorem kill_one {A : Type} (φ : A → A) (m : ℕ) (E : (Fin m → A) → ℂ) (Λ z : ℂ)
    (hE : ∀ y, E (fun i => φ (y i)) = Λ * E y) :
    aeval (mapOp φ m) (gpoly Λ) (fun y => (z * E y).re) = 0 := by
  simp only [gpoly, map_add (f := _), map_sub, map_mul, aeval_X, aeval_C, map_pow]
  funext y
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mapOp_apply,
    hE, Pi.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kill_sum {A : Type} (φ : A → A) (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → (Fin m → A) → ℂ) (Λ z : ι → ℂ) (hE : ∀ j y, E j (fun i => φ (y i)) = Λ j * E j y)
    (F : (Fin m → A) → ℝ) (hF : ∀ y, (F y : ℂ) = ∑ j, z j * E j y) :
    aeval (mapOp φ m) (∏ j, gpoly (Λ j)) F = 0 := by
  have hF' : F = ∑ j, fun y => (z j * E j y).re := by
    funext y
    rw [Finset.sum_apply, ← Complex.re_sum, ← hF y, Complex.ofReal_re]

  rw [hF', map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply,
    kill_one φ m (E j) (Λ j) (z j) (hE j), map_zero]

theorem cup_kill {A : Type} [Group A] (φ : A →* A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ι → Additive A → ℂ) (lam : ι → ℂ)
    (hβ : ∀ j x, β j (Additive.ofMul (φ x)) = lam j * β j (Additive.ofMul x))
    (hspan : ∀ α : Additive A →+ ℝ, ∃ c : ι → ℂ, ∀ x, (α x : ℂ) = ∑ j, c j * β j x) (q : ℕ)
    (α : Fin (q + 1) → (Additive A →+ ℝ)) :
    aeval (mapOp φ (q + 2)) (∏ J : Fin (q + 1) → ι, gpoly (∏ i, lam (J i))) (cupH α) = 0 := by
  choose c hc using hspan
  let d : Fin (q + 1) → (Fin (q + 2) → A) → Additive A :=
    fun i y => Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ)
  let E : (Fin (q + 1) → ι) → (Fin (q + 2) → A) → ℂ := fun J y => ∏ i, β (J i) (d i y)
  let Λ : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, lam (J i)
  let z : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, c (α i) (J i)
  have hE : ∀ J y, E J (fun i => φ (y i)) = Λ J * E J y := by
    intro J y
    simp only [E, Λ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : d i (fun k => φ (y k)) = Additive.ofMul (φ ((y i.castSucc)⁻¹ * y i.succ)) := by
      simp only [d, map_mul, map_inv]
    rw [this, hβ]
  have hF : ∀ y, (cupH α y : ℂ) = ∑ J, z J * E J y := by
    intro y
    have h1 : (cupH α y : ℂ) = ∏ i, ∑ j, c (α i) j * β j (d i y) := by
      rw [cupH, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => hc (α i) _
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [z, E]
    rw [Finset.prod_mul_distrib]
  exact kill_sum (⇑φ) (q + 2) E Λ z hE (cupH α) hF

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenSpan

section

@[expose] public section

noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

variable (L : Type) [Field L] [NumberField L]

def embLin (σ : L →+* ℂ) : 𝓞 L →ₗ[ℤ] ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAddMonoidHom.toIntLinearMap

def coeLin : (𝓞 L →ₗ[ℤ] ℂ) →ₗ[ℂ] (𝓞 L → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embLin_linIndep : LinearIndependent ℂ (embLin L) := by
  have hinj : Function.Injective
      (fun σ : L →+* ℂ => ((σ.comp (algebraMap (𝓞 L) L)).toMonoidHom : 𝓞 L →* ℂ)) := by
    intro σ τ h
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    exact DFunLike.congr_fun h x
  have h1 := (linearIndependent_monoidHom (𝓞 L) ℂ).comp _ hinj
  apply LinearIndependent.of_comp (coeLin L)
  exact h1

theorem finrank_lin : Module.finrank ℂ (𝓞 L →ₗ[ℤ] ℂ) = Fintype.card (L →+* ℂ) := by
  rw [Module.finrank_linearMap_self, NumberField.RingOfIntegers.rank, NumberField.Embeddings.card]

theorem emb_span (α : 𝓞 L →+ ℝ) :
    ∃ c : (L →+* ℂ) → ℂ, ∀ x : 𝓞 L, (α x : ℂ) = ∑ σ, c σ * σ (algebraMap (𝓞 L) L x) := by
  have hspan := (embLin_linIndep L).span_eq_top_of_card_eq_finrank' (finrank_lin L).symm
  let f : 𝓞 L →ₗ[ℤ] ℂ := ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp α).toIntLinearMap
  have hf : f ∈ Submodule.span ℂ (Set.range (embLin L)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  refine ⟨c, fun x => ?_⟩
  have hx := LinearMap.congr_fun hc x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hx
  exact hx.symm

theorem mat_span (n r : ℕ) (α : Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ) :
    ∃ c : Fin n × Fin r × (L →+* ℂ) → ℂ, ∀ x,
      (α x : ℂ) = ∑ j, c j * j.2.2 (algebraMap (𝓞 L) L
        (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1)) := by
  let e : Matrix (Fin n) (Fin r) (𝓞 L) →+ Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun m => Additive.ofMul (Multiplicative.ofAdd m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : ∀ i j, ∃ c : (L →+* ℂ) → ℂ, ∀ y : 𝓞 L,
      ((α.comp (e.comp (Matrix.singleAddMonoidHom i j))) y : ℂ) =
        ∑ σ, c σ * σ (algebraMap (𝓞 L) L y) :=
    fun i j => emb_span L _
  choose c hc using hc
  refine ⟨fun j => c j.1 j.2.1 j.2.2, fun x => ?_⟩
  have lhs : (α x : ℂ) = ∑ i, ∑ j, ((α.comp (e.comp (Matrix.singleAddMonoidHom i j)))
      (Multiplicative.toAdd (Additive.toMul x) i j) : ℂ) := by
    have hx : x = e (Multiplicative.toAdd (Additive.toMul x)) := rfl
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (Multiplicative.toAdd (Additive.toMul x))]

    simp only [map_sum, Complex.ofReal_sum]
    rfl
  rw [lhs]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact hc i j _

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.ProdEmbNeOne

section

@[expose] public section

noncomputable section

open NumberField InfinitePlace Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def mulVHom {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) where
  toFun := mulV n r v
  map_one' := by simp [mulV]
  map_mul' x y := by simp [mulV, smul_add]

theorem prod_emb_ne_one {L : Type} [Field L] [NumberField L] (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1)
    (q : ℕ) (hq : q + 1 ≤ m) (σs : Fin (q + 1) → (L →+* ℂ)) :
    ∏ i, σs i (algebraMap (𝓞 L) L (v : 𝓞 L)) ≠ 1 := by
  classical
  intro h
  have hn : ∏ i, (InfinitePlace.mk (σs i)) (algebraMap (𝓞 L) L (v : 𝓞 L)) = 1 := by
    have := congrArg norm h
    rw [norm_prod, norm_one] at this
    simpa [InfinitePlace.apply] using this
  let g : Fin (q + 1) → InfinitePlace L := fun i => InfinitePlace.mk (σs i)
  let a : InfinitePlace L → ℕ := fun w => (Finset.univ.filter fun i => g i = w).card
  have hsum : ∑ w, a w = q + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 1))))
      (t := (Finset.univ : Finset (InfinitePlace L))) (f := g) (fun _ _ => Finset.mem_univ _)
    simpa [a] using this.symm
  have hprod : ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
    rw [← hn, ← Finset.prod_fiberwise Finset.univ g]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => w (algebraMap (𝓞 L) L (v : 𝓞 L))), Finset.prod_const]
    intro i hi
    have hgi : g i = w := (Finset.mem_filter.mp hi).2
    simp only [g] at hgi
    rw [hgi]
  exact hv a (by omega) (by omega) hprod

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

open PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes in
theorem PositivityTheory.KB.SplitAffineSpectral.eigen : PositivityTheory.KB.SplitAffineSpectral.Eigen := by
  intro L _ _ _ m v hv n r q hq
  classical
  let lam : Fin n × Fin r × (L →+* ℂ) → ℂ := fun j => j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L))
  let β : Fin n × Fin r × (L →+* ℂ) → Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) → ℂ :=
    fun j x => j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1))
  refine ⟨∏ J : Fin (q + 1) → Fin n × Fin r × (L →+* ℂ), gpoly (∏ i, lam (J i)), ?_, ?_⟩
  · rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun J _ => ?_
    rw [gpoly_eval_one, Ne, Complex.normSq_eq_zero, sub_eq_zero]
    exact fun h => prod_emb_ne_one m v hv q hq (fun i => (J i).2.2) h.symm
  · intro α
    have hβ : ∀ j x, β j (Additive.ofMul (mulVHom n r (v : 𝓞 L) x)) = lam j * β j (Additive.ofMul x) := by
      intro j x
      change j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (mulV n r (v : 𝓞 L) x) j.1 j.2.1)) =
        j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L)) * j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd x j.1 j.2.1))
      simp only [mulV, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, map_mul]
    exact cup_kill (mulVHom n r (v : 𝓞 L)) β lam hβ (fun α => mat_span L n r α) q α
end
end
end
