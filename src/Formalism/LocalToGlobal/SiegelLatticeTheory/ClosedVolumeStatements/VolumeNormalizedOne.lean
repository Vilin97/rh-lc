module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
public import Formalism.PeriodIntegrals.LocProdFormula
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
public import Formalism.PeriodIntegrals.ProdFormulaE
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf

section

@[expose] public section

namespace PI.LocProdFormulaW

theorem locProdFormula_of (h : PI.ProdFormulaE.ProdFormulaE) : PI.LocProdFormula := by
  intro F E _ _ _ _ _ h2 sig atP M hM x hx
  rw [((h F E sig h2 atP).1 M hM x hx).2, Rat.cast_abs]

end PI.LocProdFormulaW
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula

section

@[expose] public section

theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne

section

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem NormProd_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.NormProd D := by
  intro δ M hA x hx
  exact local_product_formula D.host.F D.host.E (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.conjF D.s.atP M
    (fun p => (hA p).1) x hx

end Formalism.L2.SG.Closed
end
end
