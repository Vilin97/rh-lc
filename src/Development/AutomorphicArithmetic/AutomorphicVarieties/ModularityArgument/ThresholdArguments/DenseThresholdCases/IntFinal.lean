module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeAllOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.WeightBounds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeGood
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightEx

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.WeightExist

theorem weightEx : PositivityTheory.Rg.BcB.F.WeightEx :=
  fun E _ _ _ n π hπ τ => (GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.CompanionTheory.WeightExist
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeCsd

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.slopeCsd :
    GlobalTheory.Cong.DescOffT → UpperTheory.V.Z.Int.SlopeOn .csd := by
  intro hD l _ ι E _ _ _ l' n hl' hn π χ hs w hw B hB
  obtain ⟨h1, h2, h3, rfl⟩ := hs
  obtain ⟨T, -, -, U, hU⟩ := hD E l' n hl' hn π ⟨h1, h2, h3, rfl⟩ ∅
  choose lam hlam using GlobalTheory.CompanionTheory.WeightExist.weightEx E n U hU.aut
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have hS := UpperTheory.V.Z.Int.coreU l ι E n hn U hU.aut lam hlam w hw σ B (hU.split w hw σ hσ)
    ((GlobalTheory.BcSpehCompare.hasSat_iff hσ B).1 hB)
  have e : (CG.mk π).infChar = fun φ => infOfWeight (lam φ) := funext fun φ => hU.inf φ _ (hlam φ)
  rw [e]
  exact hS
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeAll

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

theorem slopeAll (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : SlopeAll := slopeAllOf hL (slopeGood (slopeCsd hD))

theorem intP (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1 hπ.2.1 w B hB

theorem intK (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : IntK :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1
    ⟨quadChar K ^ n, fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hπ.2.1⟩ w B hB

end UpperTheory.V.Z.Int
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPOfDesc

section

@[expose] public section

namespace UpperTheory.V.Z.Int

theorem intP_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP := intP UpperTheory.ConvolutionTheory.Sph.quadLift hD

theorem intK_of_desc (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Af.IntK := intK UpperTheory.ConvolutionTheory.Sph.quadLift hD

end UpperTheory.V.Z.Int
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPHolds

section

@[expose] public section

namespace UpperTheory.V.Z.Int

theorem intP_holds : UpperTheory.V.Br.IntP := intP_of_desc UpperTheory.Gal.Desc.descOffT

theorem intK_holds : UpperTheory.V.Af.IntK := intK_of_desc UpperTheory.Gal.Desc.descOffT

theorem intP' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := fun _ => intP_holds

theorem intK' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := fun _ => intK_holds

end UpperTheory.V.Z.Int
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IntFinal

section

@[expose] public section




section
namespace UpperTheory.V.Z.Int
theorem intP'_alt : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.IntP := fun _ => intP_holds
theorem intK_of_prints : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.IntK := fun _ => intK_holds
end UpperTheory.V.Z.Int
end
end
end
