module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Tactic.Basify
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
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplCons
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetSchur
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtMem
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplFirstRow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGramMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinkowskiBox
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOrbit
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplQuadDiag
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceConj
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceMem
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceStep
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplShortPrim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTwoRow

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplBoxVolume

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplBoxVolume

theorem set_eq_preimage {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]

end PSymplBoxVolume


open PSymplBoxVolume in
theorem SymplBoxVolume.proof : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtVecMul

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplExtVecMul.proof : SymplExtVecMul.Statement := by
  intro R _ n α β γ δ p q Q w
  funext y
  rcases y with y | y <;> refine Fin.cases ?_ (fun j => ?_) y <;>
    simp [vecMul, dotProduct, symplCons, symplExt, Fintype.sum_sum_type, Fin.sum_univ_succ]

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGcd

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PSymplGcd

theorem of_gcd_ne_zero (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  refine ⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩
  have h := Int.gcd_eq_gcd_ab a b
  apply mul_left_cancel₀ hc
  linear_combination (-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h

end PSymplGcd

theorem SymplGcd.proof : SymplGcd.Statement := by
  intro a b
  by_cases hc : (Int.gcd a b : ℤ) = 0
  · have h0 : Int.gcd a b = 0 := by exact_mod_cast hc
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    exact ⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩
  · exact PSymplGcd.of_gcd_ne_zero a b hc

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOmegaMem

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOmegaMem

theorem mul_J_mul_transpose_apply {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl

end PSymplOmegaMem

theorem SymplOmegaMem.proof : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplStep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTop

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplecticReduction.proof (hStep : SymplStep.Statement) (hDet : SymplDetBound.Statement) :
    SymplecticReduction.Statement := by
  intro g _ G hG hpos
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne g)
  obtain ⟨ρsq, hleast, hρ, hle, P, hP, hent, hdet⟩ :=
    hStep n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => hDet n H hH hHpos)
  refine ⟨ρsq, hleast, ?_, P, hP, hent, ?_⟩
  · push_cast; linarith
  · calc (symplGram P G).toBlocks₁₁.det ≤ ρsq * (2 * (n : ℝ)) ^ n := hdet
      _ ≤ ρsq * (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        apply mul_le_mul_of_nonneg_left _ hρ.le
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SymplOmegaMem.full : SymplOmegaMem.Statement :=
  SymplOmegaMem.proof

theorem SymplCons.full : SymplCons.Statement :=
  SymplCons.proof

theorem SymplExtVecMul.full : SymplExtVecMul.Statement :=
  SymplExtVecMul.proof

theorem SymplTwoRow.full : SymplTwoRow.Statement :=
  SymplTwoRow.proof

theorem SymplGcd.full : SymplGcd.Statement :=
  SymplGcd.proof

theorem SymplQuadDiag.full : SymplQuadDiag.Statement :=
  SymplQuadDiag.proof

theorem SymplBoxVolume.full : SymplBoxVolume.Statement :=
  SymplBoxVolume.proof

theorem SymplShortPrim.full : SymplShortPrim.Statement :=
  SymplShortPrim.proof

theorem SymplGramMem.full : SymplGramMem.Statement :=
  SymplGramMem.proof

theorem SymplReducePosDef.full : SymplReducePosDef.Statement :=
  SymplReducePosDef.proof

theorem SymplReduceConj.full : SymplReduceConj.Statement :=
  SymplReduceConj.proof

theorem SymplDetSchur.full : SymplDetSchur.Statement :=
  SymplDetSchur.proof

theorem SymplExtMem.full : SymplExtMem.Statement :=
  SymplExtMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplMinkowskiBox.full : SymplMinkowskiBox.Statement :=
  SymplMinkowskiBox.proof SymplBoxVolume.full

theorem SymplMinExists.full : SymplMinExists.Statement :=
  SymplMinExists.proof SymplQuadDiag.full

theorem SymplReduceMem.full : SymplReduceMem.Statement :=
  SymplReduceMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplOrbit.full : SymplOrbit.Statement :=
  SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full

theorem SymplMinBound.full : SymplMinBound.Statement :=
  SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full

theorem SymplReduceStep.full : SymplReduceStep.Statement :=
  SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full

theorem SymplFirstRow.full : SymplFirstRow.Statement :=
  SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full

theorem SymplStep.full : SymplStep.Statement :=
  SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full

theorem SymplDetBound.full : SymplDetBound.Statement :=
  SymplDetBound.proof SymplStep.full

theorem SymplecticReduction.full : SymplecticReduction.Statement :=
  SymplecticReduction.proof SymplStep.full SymplDetBound.full

end GroundTheory.Heights₂.Heights
end
end
