module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpMat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LieDecomp

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpSub

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.PairAlg

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.pairAlg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a)
      (S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ'.d) (Fin Ξ'.d) ℂ)),
      (∀ τ i j, (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) ∈ S) →
        (∀ X, (Ξ.dmat X, Ξ'.dmat X) ∈ S) ∧ ∀ y, (Ξ.mat y, Ξ'.mat y) ∈ S := by
  intro E _ _ _ a Ξ Ξ' S h
  have h1 : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), (Ξ.dmat (toL X), Ξ'.dmat (toL X)) ∈ S := by
    intro X
    have e : (Ξ.dmat (toL X), Ξ'.dmat (toL X)) = ∑ τ : E →+* ℂ, ∑ i, ∑ j,
        (X.map (coord τ)) i j • (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) := by
      rw [lieDecomp E a _ Ξ.dmat X, lieDecomp E a _ Ξ'.dmat X]
      refine Prod.ext ?_ ?_
      · simp only [hol_apply, Prod.fst_sum, Prod.smul_fst]
      · simp only [hol_apply, Prod.snd_sum, Prod.smul_snd]
    rw [e]
    exact S.sum_mem fun τ _ => S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h τ i j) _
  refine ⟨fun X => h1 (Matrix.of X), fun y => ?_⟩
  let H : Submonoid (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (Ξ.mat y, Ξ'.mat y) ∈ S}
      one_mem' := by
        change (Ξ.mat 1, Ξ'.mat 1) ∈ S
        rw [map_one, map_one]
        exact S.one_mem
      mul_mem' := by
        intro x y hx hy
        change (Ξ.mat (x * y), Ξ'.mat (x * y)) ∈ S
        rw [map_mul, map_mul]
        exact S.mul_mem hx hy }
  refine expGen E a H (fun X y hy => ?_) y
  change (Ξ.mat y, Ξ'.mat y) ∈ S
  rw [expMat E a Ξ X y hy, expMat E a Ξ' X y hy]
  exact expSub _ _ S _ _ (h1 X)
end
end
