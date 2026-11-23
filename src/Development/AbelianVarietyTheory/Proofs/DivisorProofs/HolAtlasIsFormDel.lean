module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZeroStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTarget

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem del_loc_repr_contDiffOn : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  intro M _ n A α hα i S
  have key : ∀ v ∈ (A.e i).target, (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S =
      ∑ a, ∑ T, GlobalTheory.del (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a) *
        (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.dz a * GlobalTheory.CxForm.bas n T) S := by
    intro v hv
    have h1 : A.loc (A.del α) i v = GlobalTheory.CxForm.delAt (A.loc α i) v := by
      rw [GlobalTheory.CxForm.HolAtlas.loc, dite_eq_left hv]
      simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.HolAtlas.Pt.crd, GlobalTheory.CxForm.HolAtlas.Pt.ch, GlobalTheory.CxForm.HolAtlas.Pt.pt, (A.e i).right_inv hv]
    rw [h1, GlobalTheory.CxForm.delAt]

    simp only [GlobalTheory.CxForm.coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ key
  have ho := (A.e i).open_target
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun T _ => ContDiffOn.mul ?_ contDiffOn_const
  have hf := hα.smooth i T
  have hd := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a))
      (A.e i).target := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v
      (Complex.I • coordVec a)) (A.e i).target := hd.clm_apply contDiffOn_const
  refine ((h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).congr fun v _ => ?_
  rfl

end GlobalTheory.CxForm.HolAtlas
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTargetStatement

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.del_loc_repr_contDiffOn_target : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | exact GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | (intros; apply GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderivStatement

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  first | exact @GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | exact GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv | (intros; apply GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

  rw [FormMul.repr_coefwise, e,
  del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
  ContinuousLinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibnizStatement

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ) (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) → (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) → GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v = ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  first | exact @GlobalTheory.CxForm.DelForm.delAt_sum_smul | exact GlobalTheory.CxForm.DelForm.delAt_sum_smul | (intros; apply GlobalTheory.CxForm.DelForm.delAt_sum_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphic

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]

    simp [map_sum, map_smul, smul_eq_mul]

  simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphicStatement

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {c : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}, DifferentiableAt ℝ c (φ v) → DifferentiableAt ℂ φ v → GlobalTheory.CxForm.DelForm.dOne (fun w => c (φ w)) v = GlobalTheory.CxForm.pull (fderiv ℂ φ v) (GlobalTheory.CxForm.DelForm.dOne c (φ v)) := by
  first | exact @GlobalTheory.CxForm.DelForm.dOne_comp_holo | exact GlobalTheory.CxForm.DelForm.dOne_comp_holo | (intros; apply GlobalTheory.CxForm.DelForm.dOne_comp_holo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel

section

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open GlobalTheory.CxForm

variable {n : ℕ}

theorem delAt_pull_comp {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) {β : V n → Alt n}
    (hβ : ∀ S, DifferentiableAt ℝ (fun u => (bas n).repr (β u) S) (φ v)) :
    delAt (fun w => pull (fderiv ℂ φ w) (β (φ w))) v = pull (fderiv ℂ φ v) (delAt β (φ v)) := by
  have hφ1 : DifferentiableAt ℂ φ v := hφ.differentiableAt two_ne_zero
  have e : (fun w => pull (fderiv ℂ φ w) (β (φ w))) =
      fun w => ∑ T, (bas n).repr (β (φ w)) T • pull (fderiv ℂ φ w) (bas n T) := funext fun w => by
    conv_lhs => rw [← (bas n).sum_repr (β (φ w))]

    simp only [map_sum, map_smul]
  rw [e, GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz (fun T w => (bas n).repr (β (φ w)) T) (fun T w => pull (fderiv ℂ φ w) (bas n T))
    (fun T => (hβ T).comp v (hφ1.restrictScalars ℝ)) (fun T S => GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv hφ (bas n T) S)]
  simp only [GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero hφ, smul_zero, add_zero]

  rw [delAt_eq_sum_dOne β (φ v), map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_mul, GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic (c := fun u => (bas n).repr (β u) T) (hβ T) hφ1]

variable {M : Type} [TopologicalSpace M] {A : HolAtlas M n}

theorem del_compat {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.del α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.del α x') := by
  set φ : V n → V n := x'.ch ∘ x.ch.symm with hφdef
  have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hv : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  have hφ : ContDiffAt ℂ 2 φ x.crd := by
    have hd : DifferentiableOn ℂ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := A.holo x.1.1 x'.1.1
    have hs : ContDiffOn ℂ ∞ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := (contDiffOn_piLp 2).2 fun c =>
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hW
        ((EuclideanSpace.proj c : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hd)
    exact (hs.contDiffAt (hW.mem_nhds hv)).of_le (WithTop.coe_le_coe.2 le_top)
  have hφv : φ x.crd = x'.crd := by
    change x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
    rw [x.ch.left_inv x.2]
    exact congrArg x'.ch h
  have hloc : A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun w => pull (fderiv ℂ φ w) (A.loc α x'.1.1 (φ w)) := by
    filter_upwards [hW.mem_nhds hv] with w hw
    let p : A.Pt := ⟨(x.1.1, x.ch.symm w), x.ch.map_target hw.1⟩
    let p' : A.Pt := ⟨(x'.1.1, x.ch.symm w), hw.2⟩
    have hc := hα.compat p p' rfl
    have hp : p.crd = w := x.ch.right_inv hw.1
    rw [HolAtlas.loc, dite_eq_left hw.1]
    refine hc.trans ?_
    rw [hp, ← A.loc_crd α p']
    rfl
  show delAt (A.loc α x.1.1) x.crd = pull (fderiv ℂ φ x.crd) (delAt (A.loc α x'.1.1) x'.crd)
  rw [delAt_congr hloc, delAt_pull_comp hφ (fun S => hφv ▸ FormMul.differentiableAt_coef hα x' S), hφv]

theorem isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld),
    A.IsForm α → A.IsForm (A.del α) :=
  fun A α hα => ⟨GlobalTheory.T.del_loc_repr_contDiffOn_target A α hα, fun x x' h => del_compat hα x x' h⟩

end GlobalTheory.CxForm.DelForm
end
end
end
