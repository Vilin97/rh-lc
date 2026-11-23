module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

-- Source module: Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfC3Stable

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sig_apply (D : D7) (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hE_repr (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (W.frame.repr x) (W.frame.repr y) = W.hT x y := by
  conv_rhs => rw [← W.frame.sum_repr x, ← W.frame.sum_repr y]

  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
  map_smul, smul_eq_mul, sig_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfRationalFrames

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V) :
    Matrix (Fin W.rank) (Fin W'.rank) D.host.E :=
  fun i j => W.frame.repr (ι (W'.frame j)) i

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

end Gen

theorem gram_frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V)
    (h1 : HSpace.IsIsomEmb W' W ι) :
    W'.gram = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat D W W' ι) * W.gram * frameMat D W W' ι := by
  ext i j
  have e1 : W'.gram i j = W.hT (ι (W'.frame i)) (ι (W'.frame j)) := (h1 _ _).symm
  rw [e1, ← hE_repr D W]
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, frameMat,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
end
end
