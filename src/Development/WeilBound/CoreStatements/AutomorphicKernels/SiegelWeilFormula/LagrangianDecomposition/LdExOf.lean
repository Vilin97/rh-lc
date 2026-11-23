module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinOneOneMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FrameOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.EpsNegUnit
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.EmbQMapApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.EDApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SchrTransl
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvAlt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HgtPull

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem hgtPull : HgtPull := PositivityTheory.SiegelWeilFormula.Ldexb.hgtPull

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.JEx

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem jEx : JEx := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (jHom d h b).codRestrict _ (jHom_mem d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (jHom d h b g).1 * incM F d.b.1 = _
    rw [jHom_val]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (jHom d h b g).1 := by
    simp only [jHom_val, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (jHom d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((jHom d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (jHom d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelW

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx_wired (hD : SDarb) (hP : PartCharInv) (hC : ChartFacts) (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_of hD PositivityTheory.SiegelWeilFormula.Ldexa.sEv bigT sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem model_existence_of_siegel_small (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_wired PositivityTheory.SiegelWeilFormula.Ldexa.sDarb partCharInv chartFacts hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSTop

section

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem smallS_of' : ChartFacts → SliceFacts → SmallS := fun hC hF => smallS_of hC hF (subSplit_of hF) haarLc

end PositivityTheory.SiegelWeilFormula.Ald
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegel

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem model_existence_of_siegel (hG : SiegelSmall) : ModelEx := model_existence_of_siegel_small hG (smallS_of' chartFacts sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelP

section

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem siegelSmall_of_slice (hF : SliceFacts) : SiegelSmall := siegelSmall_of hF Ldx.adaptedChar

end PositivityTheory.SiegelWeilFormula.Ald
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelEx

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx : ModelEx := model_existence_of_siegel (siegelSmall_of_slice sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOf

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem ldEx_of : TAll → AuxiliaryPrimeFunction → LDEx := ldEx_of_leaves yFrame jEx kStd hgtPull modelEx

end PositivityTheory.SiegelWeilFormula.Ald

end
end
end
