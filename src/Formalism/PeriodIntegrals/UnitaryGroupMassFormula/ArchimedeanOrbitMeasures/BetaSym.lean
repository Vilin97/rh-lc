module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu
public import Mathlib.RingTheory.TotallySplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuF

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x


open Classical in
def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)


open Classical in
def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end


end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BetaSym

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sigE (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : E ≃ₐ[F] E :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ t) = Algebra.trace R (R ⊗[F] E) t := by
  have h : sigR R σ t = Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (sigE σ hσ) t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigE]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [h, Algebra.trace_eq_of_algEquiv]

theorem hR_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    hR R σ J y x = sigR R σ (hR R σ J x y) := by
  have h := gramR_memP R σ hσ J hJ ![x, y] 0 1
  simp only [gramR, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, sigR_invP R σ hσ]

end Gen

theorem BR_symm {D : D7} (X : HidaSetting D) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y x := by
  simp only [BR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hR_swap (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) (x a) (y a),
    trace_sigR (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X)]

theorem betaSym_holds : BetaSym := by
  intro D X x y
  simp only [betaI]
  rw [BR_symm]

end PI.AprimeInfW
end
end
end
