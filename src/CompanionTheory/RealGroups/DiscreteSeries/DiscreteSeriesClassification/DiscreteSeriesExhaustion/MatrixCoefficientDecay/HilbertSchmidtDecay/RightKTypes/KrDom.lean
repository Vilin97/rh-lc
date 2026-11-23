module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.BaseAct
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CommuteOmTensRho
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.Chebyshev

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KlfStepCoefApply

section

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem klf_stepCoef_apply (X : GMod n) (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n)
    (u : (step X z).V) (g : Matrix (Fin n) (Fin n) ℂ) :
    stepCoef X z c j u g = ∑ i, g j i * c ((Subtype.val u : Fin n → X.V) i) g := rfl

theorem klf_contFam_step {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : ContFam ε c) (z : ℂ) :
    ContFam ε (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  rintro ⟨i, j⟩ v
  simp only [klf_stepCoef_apply]
  exact continuous_finsetSum _ fun a _ => ((S7.continuous_toM ε).matrix_elem j a).mul (h i _)

theorem leftExp_step {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : LeftExp ε c) (z : ℂ) :
    LeftExp ε (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  rintro ⟨i, j⟩
  obtain ⟨r, is, β, B, hB, hc⟩ := h i
  refine ⟨n * r, fun m => (is (finProdFinEquiv.symm m).2, (finProdFinEquiv.symm m).1),
    fun m k => S7.toMK k j (finProdFinEquiv.symm m).1 * β (finProdFinEquiv.symm m).2 k, |B|, ?_, ?_⟩
  · intro m k
    rw [norm_mul]
    have h1 : ‖S7.toMK k j (finProdFinEquiv.symm m).1‖ ≤ 1 :=
      entry_norm_bound_of_unitary (U := S7.toMK k) k.2.1 _ _
    calc _ ≤ 1 * |B| := mul_le_mul h1 ((hB _ _).trans (le_abs_self B)) (norm_nonneg _) zero_le_one
      _ = |B| := one_mul _
  · intro v g k
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, klf_stepCoef_apply, hc, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem leftExp_path {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : LeftExp ε c)
    (χ : Fin n → ℂ) (ss : List (Fin n)) :
    LeftExp ε (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2) := by
  induction ss generalizing X I χ with
  | nil =>
    rintro ⟨i, js⟩
    obtain ⟨r, is, β, B, hB, hc⟩ := h i
    exact ⟨r, fun l => (is l, js), β, B, hB, hc⟩
  | cons s ss ih =>
    rintro ⟨i, js⟩
    obtain ⟨r, is, β, B, hB, hc⟩ := ih (leftExp_step h (χ s)) (χ + Pi.single s 1) ((i, js.headD s), js.tail)
    exact ⟨r, fun l => ((is l).1.1, (is l).1.2 :: (is l).2), β, B, hB, hc⟩

theorem contFam_path {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : ContFam ε c)
    (χ : Fin n → ℂ) (ss : List (Fin n)) :
    ContFam ε (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2) := by
  induction ss generalizing X I χ with
  | nil => exact fun p => h p.1
  | cons s ss ih =>
    rintro ⟨i, js⟩
    exact ih (klf_contFam_step h (χ s)) (χ + Pi.single s 1) ((i, js.headD s), js.tail)

theorem leftExp_base {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    LeftExp ε (X := ⟨D, E, hK.gl⟩) (fun ξ : D => baseCoef σ D (ξ : H)) := by
  intro ξ
  obtain ⟨S, hfin, hξ, hS⟩ := (hK.mem _).1 ξ.2
  have hSD : ∀ x ∈ S, x ∈ D := fun x hx => (hK.mem _).2 ⟨S, hfin, hx, hS⟩
  let b := stdOrthonormalBasis ℂ S
  have hmem : ∀ k : S7.KG ε, σ (S7.toMK k⁻¹) (ξ : H) ∈ S := fun k => hS _ (k⁻¹).2 _ hξ
  have hUJ : ∀ g : S7.UJ ε, S7.toM g ∈ Formalism.MainNotions.S.UJset ε := fun g => g.2
  refine ⟨Module.finrank ℂ S, fun l => ⟨(b l : H), hSD _ (b l).2⟩,
    fun l k => ⟪σ (S7.toMK k⁻¹) (ξ : H), (b l : H)⟫_ℂ, ‖(ξ : H)‖, ?_, ?_⟩
  · intro l k
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 : ‖(b l : H)‖ = 1 := b.orthonormal.1 l
    rw [h1, mul_one, hU.2.1 _ (hUJ _)]
  · intro v g k
    show ⟪(ξ : H), σ (S7.toMK k * S7.toM g) (v : H)⟫_ℂ =
      ∑ l, ⟪σ (S7.toMK k⁻¹) (ξ : H), (b l : H)⟫_ℂ * ⟪(b l : H), σ (S7.toM g) (v : H)⟫_ℂ
    have hkg : S7.toMK k * S7.toM g = S7.toM ((k : S7.UJ ε) * g) := rfl
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (S7.toMK k⁻¹)).toLinearMap, hU.2.1 _ (hUJ _)⟩
    have e1 := L.inner_map_map (ξ : H) (σ (S7.toMK k * S7.toM g) (v : H))
    have e2 : L (σ (S7.toMK k * S7.toM g) (v : H)) = σ (S7.toM g) (v : H) := by
      have h3 := hU.1.2 (S7.toMK k⁻¹) (hUJ _) (S7.toMK k * S7.toM g) (hkg ▸ hUJ _)
      have h4 : S7.toMK k⁻¹ * (S7.toMK k * S7.toM g) = S7.toM g := by
        show S7.toM (((k : S7.UJ ε))⁻¹ * ((k : S7.UJ ε) * g)) = S7.toM g
        rw [inv_mul_cancel_left]
      rw [h4] at h3
      rw [h3]
      rfl
    rw [← e1, e2]
    have e3 : σ (S7.toMK k⁻¹) (ξ : H) =
        ∑ l, ⟪(b l : H), σ (S7.toMK k⁻¹) (ξ : H)⟫_ℂ • (b l : H) := by
      have := congrArg (Subtype.val : S → H) (b.sum_repr' ⟨_, hmem k⟩)
      simpa using this.symm
    show ⟪σ (S7.toMK k⁻¹) (ξ : H), _⟫_ℂ = _
    conv_lhs => rw [e3]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, inner_conj_symm]

theorem contFam_base {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    ContFam ε (X := ⟨D, E, hK.gl⟩) (fun ξ : D => baseCoef σ D (ξ : H)) := by
  intro ξ v
  have h : Continuous fun g : S7.UJ ε => σ (S7.toM g) (v : H) :=
    (hU.2.2 (v : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
  exact continuous_const.inner h

end CompanionTheory.RgExh.Dec.L.WyKR
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.RightExp

section

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rightExp {ε : Fin n → Bool} {X : GMod n} (A : KAct ε X) (x : X.V) :
    ∃ (r : ℕ) (w : Fin r → X.V) (a : Fin r → S7.KG ε → ℂ) (B : ℝ), (∀ l k, ‖a l k‖ ≤ B) ∧
      ∀ k, A.ρ k x = ∑ l, a l k • w l := by
  obtain ⟨W, hW, hmem⟩ := A.fin x
  obtain ⟨C, hC⟩ := A.bdd
  let b := Module.finBasis ℂ W
  let embW : W →ₗ[ℂ] A.N := A.emb ∘ₗ W.subtype
  have hinj : Function.Injective embW := A.inj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range embW := LinearEquiv.ofInjective embW hinj
  have : FiniteDimensional ℂ (LinearMap.range embW) := LinearMap.finiteDimensional_range embW
  let ψ : Fin (Module.finrank ℂ W) → (LinearMap.range embW →L[ℂ] ℂ) :=
    fun l => LinearMap.toContinuousLinearMap ((b.coord l) ∘ₗ e.symm.toLinearMap)
  refine ⟨Module.finrank ℂ W, fun l => (b l : X.V), fun l k => b.repr ⟨A.ρ k x, hmem k⟩ l,
    ∑ l, ‖ψ l‖ * (|C| * ‖A.emb x‖), fun l k => ?_, fun k => ?_⟩
  · have h1 : b.repr ⟨A.ρ k x, hmem k⟩ l = ψ l (e ⟨A.ρ k x, hmem k⟩) := by
      simp [ψ]
    show ‖b.repr ⟨A.ρ k x, hmem k⟩ l‖ ≤ _
    rw [h1]
    have h2 : ‖e ⟨A.ρ k x, hmem k⟩‖ = ‖A.emb (A.ρ k x)‖ := rfl
    calc ‖ψ l (e ⟨A.ρ k x, hmem k⟩)‖ ≤ ‖ψ l‖ * ‖e ⟨A.ρ k x, hmem k⟩‖ := (ψ l).le_opNorm _
      _ ≤ ‖ψ l‖ * (|C| * ‖A.emb x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [h2]
          exact (hC k x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      _ ≤ _ := Finset.single_le_sum (f := fun l => ‖ψ l‖ * (|C| * ‖A.emb x‖))
          (fun l _ => by positivity) (Finset.mem_univ l)
  · have h3 := congrArg Subtype.val (b.sum_repr ⟨A.ρ k x, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    exact h3.symm

end CompanionTheory.RgExh.Dec.L.WyKR
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.StepCoefApply

section

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section

variable {ε : Fin n → Bool} {X : GMod n}

theorem stepRho_bdd (A : KAct ε X) (z : ℂ) :
    ∃ C : ℝ, ∀ k x, ‖stepEmb A z (stepRho A z k x)‖ ≤ C * ‖stepEmb A z x‖ := by
  obtain ⟨C, hC⟩ := A.bdd
  refine ⟨n * |C|, fun k x => ?_⟩
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun b => ?_

  rw [stepEmb_apply, stepRho_coe, tensRho_apply, map_sum]
  calc ‖∑ i, A.emb (S7.toMK k b i • A.ρ k ((sv x) i))‖
      ≤ ∑ i, ‖A.emb (S7.toMK k b i • A.ρ k ((sv x) i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, |C| * ‖stepEmb A z x‖ := by
        refine sum_le_sum fun i _ => ?_
        rw [map_smul, norm_smul]
        have h1 := hC k ((sv x) i)
        have h2 : ‖A.emb ((sv x) i)‖ ≤ ‖stepEmb A z x‖ := norm_le_pi_norm (stepEmb A z x) i
        have h3 := kr_entry k b i
        have h4 : C * ‖A.emb ((sv x) i)‖ ≤ |C| * ‖stepEmb A z x‖ :=
          (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg C))
        calc ‖S7.toMK k b i‖ * ‖A.emb (A.ρ k ((sv x) i))‖
            ≤ 1 * ‖A.emb (A.ρ k ((sv x) i))‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ ≤ |C| * ‖stepEmb A z x‖ := by rw [one_mul]; exact h1.trans h4
    _ = n * |C| * ‖stepEmb A z x‖ := by simp [mul_assoc]

theorem stepRho_fin (A : KAct ε X) (z : ℂ) (x : (step X z).V) :
    ∃ W : Submodule ℂ (step X z).V, FiniteDimensional ℂ W ∧ ∀ k, stepRho A z k x ∈ W := by
  choose Wi hWi hmem using fun i => A.fin ((sv x) i)
  let Wt : Submodule ℂ X.V := ⨆ i, Wi i
  let W : Submodule ℂ (step X z).V :=
    Submodule.comap (stepSub X z).subtype (Submodule.pi Set.univ fun _ => Wt)
  refine ⟨W, ?_, fun k => ?_⟩
  · let f : W →ₗ[ℂ] (Fin n → Wt) :=
      { toFun := fun w i => ⟨sv (w : (step X z).V) i, w.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective f fun w w' h => ?_
    apply Subtype.ext; apply sv_inj; funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro b _
    show tensRho A k (sv x) b ∈ Wt
    rw [tensRho_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (hmem i k))

def stepAct (A : KAct ε X) (z : ℂ) : KAct ε (step X z) where
  N := Fin n → A.N
  emb := stepEmb A z
  inj := stepEmb_inj A z
  ρ := stepRho A z
  compat := stepRho_compat A z
  bdd := stepRho_bdd A z
  fin := stepRho_fin A z

theorem stepCoef_apply' (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n) (u : (step X z).V)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    stepCoef X z c j u g = ∑ i, g j i * c ((sv u) i) g := rfl

theorem rightEq_step (A : KAct ε X) {I : Type} {c : CoefFam X I} (hc : RightEq A c) (z : ℂ) :
    RightEq (stepAct A z) (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  intro p u g k
  have hc' : ∀ i v, c i v (S7.toM g * S7.toMK k) = c i (A.ρ k v) (S7.toM g) := fun i v => hc i v g k
  simp only [stepCoef_apply']
  show ∑ i, (S7.toM g * S7.toMK k) p.2 i * c p.1 ((sv u) i) (S7.toM g * S7.toMK k) =
    ∑ l, S7.toM g p.2 l * c p.1 (tensRho A k (sv u) l) (S7.toM g)

  simp only [hc', Matrix.mul_apply, tensRho_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
  smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun i _ => by ring

def pathAct : {X : GMod n} → KAct ε X → (χ : Fin n → ℂ) → (ss : List (Fin n)) → KAct ε (path X χ ss)
  | _, A, _, [] => A
  | _, A, χ, s :: ss => pathAct (stepAct A (χ s)) (χ + Pi.single s 1) ss

theorem rightEq_path : ∀ {X : GMod n} (A : KAct ε X) {I : Type} {c : CoefFam X I}, RightEq A c →
    ∀ (χ : Fin n → ℂ) (ss : List (Fin n)),
      RightEq (pathAct A χ ss) (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2)
  | _, A, _, c, hc, χ, [] => fun p v g k => hc p.1 v g k
  | X, A, I, c, hc, χ, s :: ss => by
    have h := rightEq_path (stepAct A (χ s)) (rightEq_step A hc (χ s)) (χ + Pi.single s 1) ss
    intro p v g k
    exact h ((p.1, p.2.headD s), p.2.tail) v g k

end

end CompanionTheory.RgExh.Dec.L.WyKR
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.KrDom

section

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem kr_dom {ι : Type} [Fintype ι] (γ h : ι → ℂ) (B : ℝ) (hγ : ∀ a, ‖γ a‖ ≤ B) :
    ‖∑ a, γ a * h a‖ ^ 2 ≤ (Fintype.card ι * B ^ 2) * ∑ a, ‖h a‖ ^ 2 := by
  have h1 : ‖∑ a, γ a * h a‖ ≤ |B| * ∑ a, ‖h a‖ := by
    calc _ ≤ ∑ a, ‖γ a * h a‖ := norm_sum_le _ _
      _ ≤ ∑ a, |B| * ‖h a‖ := sum_le_sum fun a _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((hγ a).trans (le_abs_self B)) (norm_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖h a‖)
  calc ‖∑ a, γ a * h a‖ ^ 2 ≤ (|B| * ∑ a, ‖h a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = B ^ 2 * (∑ a, ‖h a‖) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ B ^ 2 * (Fintype.card ι * ∑ a, ‖h a‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg B)
        simpa using h2
    _ = _ := by ring

theorem kr_img {ι κ : Type} [Fintype ι] [DecidableEq κ] (p : ι → κ) (f : κ → ℝ) (hf : ∀ q, 0 ≤ f q) :
    ∑ a, f (p a) ≤ Fintype.card ι * ∑ q ∈ Finset.univ.image p, f q := by
  calc ∑ a, f (p a) ≤ ∑ _a : ι, ∑ q ∈ Finset.univ.image p, f q :=
        sum_le_sum fun a _ => Finset.single_le_sum (fun q _ => hf q) (Finset.mem_image_of_mem p (Finset.mem_univ a))
    _ = _ := by simp

theorem kRight : KRight := by
  intro n ε H _ _ _ σ D E hK χ ss hU i u
  classical
  have hL := leftExp_path (leftExp_base hK hU) χ ss
  have hC := contFam_path (contFam_base hK hU) χ ss
  have hR := rightEq_path (baseAct hK hU) (rightEq_base hK hU) χ ss
  refine ⟨hC i u, ?_⟩
  obtain ⟨r, is, β, B, hβ, hLi⟩ := hL i
  obtain ⟨r', w, a, B', ha, hw⟩ := rightExp (pathAct (baseAct hK hU) χ ss) u
  let p : Fin r × Fin r' → (D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V := fun q => (is q.1, w q.2)
  refine ⟨Finset.univ.image p, Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2 * Fintype.card (Fin r × Fin r'),
    fun g k k' => ?_⟩
  have e1 : famP σ D E hK.gl χ ss i u (S7.toMK k * S7.toM g * S7.toMK k') =
      ∑ q : Fin r × Fin r', (β q.1 k * a q.2 k') * famP σ D E hK.gl χ ss (p q).1 (p q).2 (S7.toM g) := by
    have h1 := hR i u ((k : S7.UJ ε) * g) k'
    have h2 := hLi ((pathAct (baseAct hK hU) χ ss).ρ k' u) g k
    have e0 : S7.toM ((k : S7.UJ ε) * g) = S7.toMK k * S7.toM g := rfl
    rw [e0] at h1
    delta famP
    rw [h1, h2, hw k', Fintype.sum_prod_type]
    refine sum_congr rfl fun l _ => ?_

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, p]
    exact sum_congr rfl fun m _ => by ring
  rw [e1]
  refine (kr_dom _ _ (|B| * |B'|) fun q => ?_).trans ?_
  · rw [norm_mul]
    exact mul_le_mul ((hβ _ _).trans (le_abs_self B)) ((ha _ _).trans (le_abs_self B')) (norm_nonneg _)
      (abs_nonneg B)
  · have h3 := kr_img p (fun q => ‖famP σ D E hK.gl χ ss q.1 q.2 (S7.toM g)‖ ^ 2) (fun q => sq_nonneg _)
    calc (Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2) *
          ∑ q, ‖famP σ D E hK.gl χ ss (p q).1 (p q).2 (S7.toM g)‖ ^ 2
        ≤ (Fintype.card (Fin r × Fin r') * (|B| * |B'|) ^ 2) *
          (Fintype.card (Fin r × Fin r') * ∑ q ∈ Finset.univ.image p, ‖famP σ D E hK.gl χ ss q.1 q.2 (S7.toM g)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring

end CompanionTheory.RgExh.Dec.L.WyKR
end
end
end
