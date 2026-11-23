module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndexStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilateStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBaseStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscrStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInvStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableEulerFac

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacterStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.product_localDensities_adeleCharacter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.LocalDensityProduct.density_product | exact GlobalTheory.LocalDensityProduct.density_product | (intros; apply GlobalTheory.LocalDensityProduct.density_product <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmLocalDensitiesProductFormula

section

@[expose] public section

namespace GlobalTheory.Proof.cm_localDensities_productFormula

theorem densityProduct : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct :=
  fun F E _ _ _ _ _ _ σ h₁ h₂ h₃ =>
    ⟨GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ h₁ h₂ h₃, GlobalTheory.T.dual_lattice_different_index F E σ h₁ h₂ h₃, GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr F E σ h₁ h₂ h₃,
      GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate F E σ h₁ h₂ h₃, GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ h₁ h₂ h₃, GlobalTheory.T.product_localDensities_adeleCharacter F E σ h₁ h₂ h₃⟩

end GlobalTheory.Proof.cm_localDensities_productFormula
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmLocalDensitiesProductFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.cm_localDensities_productFormula : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct := by
  first | exact @GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | exact GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | (intros; apply GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EulerProductOfDensities

section

@[expose] public section

namespace GlobalTheory.DensityProductClosed

theorem eulerProductOfDensities : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.EulerProductOfDensities :=
  GlobalTheory.DensityProductCompare.densityProduct_iff.1 GlobalTheory.T.cm_localDensities_productFormula

end GlobalTheory.DensityProductClosed
end
end
