module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEval

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEvalStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_point_dual_quotient_form_eq_eval : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I), ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  first | exact @GlobalTheory.dual_quotient_form_eq_eval | exact GlobalTheory.dual_quotient_form_eq_eval | (intros; apply GlobalTheory.dual_quotient_form_eq_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvd

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvdStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  first | exact @GlobalTheory.tensor_projective_dvd_of_coord_dvd | exact GlobalTheory.tensor_projective_dvd_of_coord_dvd | (intros; apply GlobalTheory.tensor_projective_dvd_of_coord_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditive

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add (f := _), map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
end
end
