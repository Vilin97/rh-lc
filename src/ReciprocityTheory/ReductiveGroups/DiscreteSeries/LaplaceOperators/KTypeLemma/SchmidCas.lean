module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerOrth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchForm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import Mathlib.RingTheory.Finiteness.Prod
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreB

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Intertwine

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}

theorem layer_map_le (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) {V : Submodule ℂ M}
    {V' : Submodule ℂ M'} (hV : ∀ x ∈ V, f x ∈ V') :
    ∀ k, ∀ x ∈ layer ε E V k, f x ∈ layer ε E' V' k := by
  intro k
  induction k with
  | zero => exact hV
  | succ k ih =>
    have hle : layer ε E V (k + 1) ≤ (layer ε E' V' (k + 1)).comap f := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun x hx => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
      · exact (le_sup_left : layer ε E' V' k ≤ layer ε E' V' k ⊔ _) (ih x hx)
      · rintro _ ⟨x, hx, rfl⟩
        show f (E a b x) ∈ layer ε E' V' k ⊔ _
        rw [hf]
        refine (le_sup_right : _ ≤ layer ε E' V' k ⊔ _) ?_
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
          (Submodule.mem_iSup_of_mem hab ⟨f x, ih x hx, rfl⟩))
    exact fun x hx => hle hx

theorem khw_map (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E' μ (f w) :=
  ⟨fun a => by rw [← hf, hw.1 a, map_smul], fun a b hab hε => by rw [← hf, hw.2 a b hab hε, map_zero]⟩

theorem casimir_map (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (x : M) :
    f (casimir E x) = casimir E' (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [casimir, LinearMap.sum_apply, map_sum, hf]

end Intertwine

section Prod

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def prodE (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) :
    Fin n → Fin n → Module.End ℂ (WithLp 2 (M₁ × M₂)) := fun a b =>
  (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap ∘ₗ (LinearMap.prodMap (E₁ a b) (E₂ a b)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

def prFst : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₁ := LinearMap.fst ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

def prSnd : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₂ := LinearMap.snd ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

theorem prod_ext {x y : WithLp 2 (M₁ × M₂)} (h₁ : prFst x = prFst y) (h₂ : prSnd x = prSnd y) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)

variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem prFst_prodE (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prFst (prodE E₁ E₂ a b x) = E₁ a b (prFst x) := rfl
theorem prSnd_prodE (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prSnd (prodE E₁ E₂ a b x) = E₂ a b (prSnd x) := rfl

theorem isGlRep_prod (hE₁ : IsGlRep E₁) (hE₂ : IsGlRep E₂) : IsGlRep (prodE E₁ E₂) := by
  intro a b c d
  refine LinearMap.ext fun x => prod_ext ?_ ?_
  · have h := congrArg (fun X : Module.End ℂ M₁ => X (prFst x)) (hE₁ a b c d)
    simp only [LinearMap.sub_apply, mul_apply_eq_comp] at h
    change prFst _ = prFst _
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, map_sub, prFst_prodE]
    rw [h]
    split_ifs <;> (try simp) <;> rfl
  · have h := congrArg (fun X : Module.End ℂ M₂ => X (prSnd x)) (hE₂ a b c d)
    simp only [LinearMap.sub_apply, mul_apply_eq_comp] at h
    change prSnd _ = prSnd _
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, map_sub, prSnd_prodE]
    rw [h]
    split_ifs <;> (try simp) <;> rfl

end Prod

section ProdUnitary

variable {M₁ M₂ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] [NormedAddCommGroup M₂]
  [InnerProductSpace ℂ M₂] {ε : Fin n → Bool}
  {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem isInfUnitary_prod (hU₁ : IsInfUnitary ε E₁) (hU₂ : IsInfUnitary ε E₂) :
    IsInfUnitary ε (prodE E₁ E₂) := by
  intro a b x y
  have h₁ := hU₁ a b (prFst x) (prFst y)
  have h₂ := hU₂ a b (prSnd x) (prSnd y)
  simp only [WithLp.prod_inner_apply]
  change inner ℂ (prFst (prodE E₁ E₂ a b x)) (prFst y) + inner ℂ (prSnd (prodE E₁ E₂ a b x)) (prSnd y) =
    adjSign ε a b * (inner ℂ (prFst x) (prFst (prodE E₁ E₂ b a y)) +
      inner ℂ (prSnd x) (prSnd (prodE E₁ E₂ b a y)))
  rw [prFst_prodE, prSnd_prodE, prFst_prodE, prSnd_prodE, h₁, h₂, mul_add]

end ProdUnitary

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCore

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section ProdSub

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def prodSub (V₁ : Submodule ℂ M₁) (V₂ : Submodule ℂ M₂) : Submodule ℂ (WithLp 2 (M₁ × M₂)) :=
  (V₁.prod V₂).comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

theorem mem_prodSub {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} {x : WithLp 2 (M₁ × M₂)} :
    x ∈ prodSub V₁ V₂ ↔ prFst x ∈ V₁ ∧ prSnd x ∈ V₂ := Iff.rfl

theorem finiteDimensional_prodSub {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} (h₁ : FiniteDimensional ℂ V₁)
    (h₂ : FiniteDimensional ℂ V₂) : FiniteDimensional ℂ (prodSub V₁ V₂) := by
  have h₁' : V₁.FG := Module.Finite.iff_fg.mp h₁
  have h₂' : V₂.FG := Module.Finite.iff_fg.mp h₂
  refine Module.Finite.iff_fg.mpr ?_
  unfold prodSub
  first
    | (rw [Submodule.comap_equiv_eq_map_symm]; exact (h₁'.prod h₂').map _)
    | (have heq : Submodule.comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap (V₁.prod V₂) =
          Submodule.map (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap (V₁.prod V₂) := by
         ext x
         simp only [Submodule.mem_comap, Submodule.mem_map]
         constructor
         · intro hx
           exact ⟨_, hx, by simp⟩
         · rintro ⟨y, hy, rfl⟩
           simpa using hy
       rw [heq]
       exact (h₁'.prod h₂').map _)

theorem prodSub_kStable {ε : Fin n → Bool} {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    {E₂ : Fin n → Fin n → Module.End ℂ M₂} {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂}
    (h₁ : IsKStableSub ε E₁ V₁) (h₂ : IsKStableSub ε E₂ V₂) :
    IsKStableSub ε (prodE E₁ E₂) (prodSub V₁ V₂) := fun a b hab v hv =>
  mem_prodSub.2 ⟨h₁ a b hab _ (mem_prodSub.1 hv).1, h₂ a b hab _ (mem_prodSub.1 hv).2⟩

end ProdSub

theorem casimir_mem_genSub {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {V : Submodule ℂ M} {w : M} (hw : w ∈ V) : casimir E w ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf]
  rintro T ⟨hVT, hT⟩
  show (∑ a, ∑ b, E a b * E b a) w ∈ T
  first
    | (rw [LinearMap.sum_apply]
       refine Submodule.sum_mem _ fun a _ => ?_
       rw [LinearMap.sum_apply]
       exact Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))
    | (simp only [LinearMap.coeFn_sum, Finset.sum_apply]
       exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))

theorem casimir_eq_casVal_of_model {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {M₁ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    (hE₁ : IsGlRep E₁) (hU₁ : IsInfUnitary ε E₁) {V₁ : Submodule ℂ M₁}
    (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E₁ V₁ 1,
      IsKHWVec ε E₁ (lowK ε lam - root a b) w → w = 0)
    {M₂ : Type*} [NormedAddCommGroup M₂] [InnerProductSpace ℂ M₂] {E₂ : Fin n → Fin n → Module.End ℂ M₂}
    (hE₂ : IsGlRep E₂) (hU₂ : IsInfUnitary ε E₂) {V₂ : Submodule ℂ M₂}
    (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v) :
    ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v := by
  obtain ⟨hfd₁, hks₁, hirr₁, w₁, hw₁m, hw₁0, hw₁K⟩ := hV₁
  obtain ⟨hfd₂, hks₂, -, w₂, hw₂m, hw₂0, hw₂K⟩ := hV₂

  set y : WithLp 2 (M₁ × M₂) := (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm (w₁, w₂) with hydef
  have hy1 : prFst y = w₁ := by simp [hydef, prFst]
  have hy2 : prSnd y = w₂ := by simp [hydef, prSnd]
  have hE := isGlRep_prod hE₁ hE₂
  have hU := isInfUnitary_prod hU₁ hU₂
  have hyK : IsKHWVec ε (prodE E₁ E₂) (lowK ε lam) y := by
    refine ⟨fun a => prod_ext ?_ ?_, fun a b hab hε => prod_ext ?_ ?_⟩
    · rw [prFst_prodE, map_smul, hy1, hw₁K.1 a]
    · rw [prSnd_prodE, map_smul, hy2, hw₂K.1 a]
    · rw [prFst_prodE, hy1, hw₁K.2 a b hab hε, map_zero]
    · rw [prSnd_prodE, hy2, hw₂K.2 a b hab hε, map_zero]
  have hy0 : y ≠ 0 := fun h => hw₁0 (by rw [← hy1, h, map_zero])
  have hSle : kLowSpan ε (prodE E₁ E₂) y ≤ prodSub V₁ V₂ :=
    kLowSpan_le (prodSub_kStable hks₁ hks₂) (mem_prodSub.2 ⟨hy1 ▸ hw₁m, hy2 ▸ hw₂m⟩)
  haveI := finiteDimensional_prodSub hfd₁ hfd₂
  have hfin : FiniteDimensional ℂ (kLowSpan ε (prodE E₁ E₂) y) := Submodule.finiteDimensional_of_le hSle
  have hS := kLowSpan_kIrrHW hE hU hyK hy0 hfin

  have hNoS : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε (prodE E₁ E₂) (kLowSpan ε (prodE E₁ E₂) y) 1,
      IsKHWVec ε (prodE E₁ E₂) (lowK ε lam - root a b) w → w = 0 := by
    intro a b hab hne w hw hwK
    have h1 := hNo a b hab hne _
      (layer_map_le prFst (fun a b x => prFst_prodE a b x) (fun x hx => (mem_prodSub.1 (hSle hx)).1) 1 w hw)
      (khw_map prFst (fun a b x => prFst_prodE a b x) hwK)
    have h2 := no_of_casimir hE₂ hU₂ hc₂ hgap a b hab hne _
      (layer_map_le prSnd (fun a b x => prSnd_prodE a b x) (fun x hx => (mem_prodSub.1 (hSle hx)).2) 1 w hw)
      (khw_map prSnd (fun a b x => prSnd_prodE a b x) hwK)
    exact prod_ext (by rw [h1, map_zero]) (by rw [h2, map_zero])
  have hcomm : ∀ a b x, casimir (prodE E₁ E₂) (prodE E₁ E₂ a b x) =
      prodE E₁ E₂ a b (casimir (prodE E₁ E₂) x) :=
    fun a b x => congrArg (fun T : Module.End ℂ (WithLp 2 (M₁ × M₂)) => T x) (casimir_comm hE a b)
  have hcK := khw_map (casimir (prodE E₁ E₂)) hcomm hyK
  have hcS := khw_lowK_mem_of_no hE hU hS hNoS hgap
    (casimir_mem_genSub (prodE E₁ E₂) (self_mem_kLowSpan y)) hcK
  obtain ⟨c, hc⟩ := kLowSpan_line hE hU hyK hy0 hcS hcK.1

  have h2 : casimir E₂ w₂ = c • w₂ := by
    have := casimir_map (E := prodE E₁ E₂) (E' := E₂) prSnd (fun a b x => prSnd_prodE a b x) y
    rw [hc, map_smul, hy2] at this
    exact this.symm
  have hcv : (casVal lam : ℂ) = c := smul_left_injective ℂ hw₂0 ((hc₂ w₂ hw₂m).symm.trans h2)
  have h1 : casimir E₁ w₁ = (casVal lam : ℂ) • w₁ := by
    have := casimir_map (E := prodE E₁ E₂) (E' := E₁) prFst (fun a b x => prFst_prodE a b x) y
    rw [hc, map_smul, hy1, ← hcv] at this
    exact this.symm

  have kerI : ∀ v, v ∈ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) ↔
      casimir E₁ v = (casVal lam : ℂ) • v := fun v => by
    rw [LinearMap.mem_ker]
    show casimir E₁ v - (casVal lam : ℂ) • v = 0 ↔ _
    exact sub_eq_zero
  have hcomm₁ : ∀ a b x, casimir E₁ (E₁ a b x) = E₁ a b (casimir E₁ x) :=
    fun a b x => congrArg (fun T : Module.End ℂ M₁ => T x) (casimir_comm hE₁ a b)
  have hst : IsKStableSub ε E₁ (V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1)) := by
    intro a b hab v hv
    refine ⟨hks₁ a b hab v hv.1, (kerI _).2 ?_⟩
    rw [hcomm₁, (kerI v).1 hv.2, map_smul]
  rcases hirr₁ _ inf_le_left hst with h | h
  · exfalso
    have hw : w₁ ∈ V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) := ⟨hw₁m, (kerI w₁).2 h1⟩
    rw [h] at hw
    exact hw₁0 ((Submodule.mem_bot ℂ).1 hw)
  · intro v hv
    have hv' : v ∈ V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) := by rw [h]; exact hv
    exact (kerI v).1 hv'.2

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section No

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem sc_no_of_schmid (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (hn : (n : ℝ) < h)
    (hS : ∀ x ∈ Wm ε E V, phi E 1 x = 0) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hε w hw hμ
  by_contra hw0
  have : FiniteDimensional ℂ V := hV.1
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have hP : V.starProjection w = 0 := by
    by_contra hne
    have hkhw := isKHWVec_starProjection hKU hV.2.1 hμ
    have heq := khw_weight_eq_of_irr hE hV (Submodule.starProjection_apply_mem V w) hne hkhw
    have h2 := congr_fun heq a
    simp only [Pi.sub_apply, root, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne] at h2
    linarith
  have hperp : ∀ u ∈ layer ε E V 0, inner ℂ u w = 0 := by
    intro u hu
    have hwo : w ∈ Vᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := V) w
      rwa [hP, sub_zero] at this
    exact (Submodule.mem_orthogonal V w).1 hwo u hu
  obtain ⟨P, hPnc, hP0, hPμ, hPperp⟩ := lift_layer hE hU hV.1 hV.2.1 (k := 0) hw hperp hμ hw0
  obtain ⟨xm, hxm, xp, hxp, hsum⟩ := ncV_one_decomp hE hU hV hmono hh hbig hPnc
  have hxm0 : inner ℂ xm P = 0 :=
    hPperp xm (Wm_le_ncV hxm) (by rw [hS xm hxm]; exact zero_mem _)
  have hmp : inner ℂ xm xp = 0 := Wm_perp_Wp hU hxm hxp
  have hxm_eq : xm = 0 := by
    have h3 : inner ℂ xm xm = 0 := by
      rw [hsum, inner_add_right, hmp, add_zero] at hxm0
      exact hxm0
    exact inner_self_eq_zero.1 h3
  rw [hxm_eq, zero_add] at hsum
  have hPWp : P ∈ Wp ε E V := hsum ▸ hxp
  obtain ⟨r, s, -, -, hC⟩ := crossOp_khw hE hU hV hPnc hP0 hPμ
  have hroot : lowK ε lam - root a b = lowK ε lam + root b a := by
    ext x; simp only [Pi.sub_apply, Pi.add_apply, root]; ring
  have hneg := crossVal_neg hmono hh hab hε
  rw [← hroot] at hneg
  have hWp := Wp_bound hE hU hV hmono hh hbig hPWp
  set val : ℝ := casValK ε (lowK ε lam - root a b) - n - casValK ε (lowK ε lam) with hval
  have key : 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 P) P) = val * ‖P‖ ^ 2 := by
    have e := congrArg (fun x => RCLike.re (inner ℂ x P)) hC
    have hre : ((‖P‖ : ℂ) ^ 2).re = ‖P‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [inner_smul_left, inner_self_eq_norm_sq_to_K] at e
    simp at e
    rw [hre] at e
    exact e
  have hpos : 0 < ‖P‖ ^ 2 := by positivity
  have h4 : 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ (-2 * h - 2) * ‖P‖ ^ 2 := by
    rw [key] at hWp
    exact hWp.trans (mul_le_mul_of_nonneg_right hneg hpos.le)
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

end No

theorem schmid_casimir (n : ℕ) : SchmidCasimirStatement n := by
  intro ε ν h c N _ _ EN W hE hU hW hS hc hint hmono hgap hneed hp hq
  set lam : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam
  have hlow : lowK ε lam = ν := by
    ext a; simp only [lowK, hlam, Pi.add_apply, Pi.sub_apply]; ring
  have hW' : IsKIrrHW ε EN (lowK ε lam) W := by rw [hlow]; exact hW
  have hN1 : 2 + (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN2 : 2 + 3 * (n : ℝ) / 2 ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_left (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN3 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2
      ≤ hNeed ε := (le_max_left _ _).trans (le_max_right _ _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by linarith
  have hn : (n : ℝ) < h := by linarith
  have hstd : StdGap ε lam := ⟨hmono, h, hgap, hbig⟩
  have hHC : S7.IsHCParam lam := ⟨hmono, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hHC
  obtain ⟨μ, hμ⟩ := S7.exists_mu hHC
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
    have e : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by
      simp only [S7.q0, Nat.cast_min]
    have hm : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
    have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
    rw [e]
    nlinarith
  have hPsi := (S7.isPsiFor_psiM ε lam h T μ hHC hμ hgap hq0 h8).1
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hcas := casimir_eq_casVal_of_model hstd hE hU hW'
    (sc_no_of_schmid hE hU hW' hmono hgap hbig hn hS) hD.glRep (isInfUnitary_of_isDerivedOn hσ hD)
    (datumV_isKIrrHW hPsi hv₀) (datumV_casimir hPsi T.w)
  obtain ⟨w, hwW, hw0, -⟩ := hW.2.2.2
  have h1 := hc w hwW
  rw [hcas w hwW] at h1
  simpa using (smul_left_injective ℂ hw0 h1).symm

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
end
