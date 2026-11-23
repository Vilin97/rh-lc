module

public import Formalism.HermitianCurvature.StatementPB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
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
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDerivativeHolds

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremS

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.TheoremS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pbApplied : ∀ C₄ Cthr : ℝ, 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → J.SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → J.Inst D e G CA de de' T T' l → PB.LocalModel D →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
        PB.RealInputs D C₄ jn Vt → PB.DensInput G.k G.r G.f sd →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), PB.RowsInput D sd Vt c B → PB.MassDataHyp B →
          PB.EnergyLink B jn sd C Th D.r D.f →
          ∀ (τ Rw I HS H₁ : Type) [Fintype I] [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
            [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
            (X : PB.Terms τ Rw I HS H₁) (c5 Cn : ℝ),
            PB.Link X B G de T du du' → PB.SplitInputs X B.tt →
            PB.SizeNumbers G.k G.r G.f bb G.g1 G.g2 c5 Cn →
            X.RowBig (Real.exp (-(c5 * G.k * G.f * Real.log G.k))) (du * du' / (G.size de T du).Dstar) →
            X.RowNotScalar (Real.exp (-(c5 * G.k * G.f * Real.log G.k)))
              (du * du' / (G.size de T du).Dstar) →
            X.RowNG (((2 : ℝ) ^ (G.k - 2 * G.r - 5))⁻¹ *
              Real.exp (Cn * ((2 * G.r + 2 : ℕ) : ℝ) ^ 5 * G.f * Real.log bb))
              (du * du' / (G.size de T du).Dstar) →
            ‖X.K0‖ ^ 2 ≤ (1 + (bb ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar) := by
  open Formalism.FourierDecayAlt.P.GrowthPolynomialOperator in
  exact t_PairBoundFromLocal t_MainRow t_PairBound Formalism.FourierDecayAlt.P.HilbertSchmidtNorm.localCores
    Formalism.FourierDecayAlt.P.HilbertSchmidtNorm.globalCores t_LatticeLink t_AxiomsOfLocalModel Formalism.FourierDecayAlt.P.lattice_average_induction
    t_PairBoundAbstract t_PriceOfIota t_EqualIota t_PairSplit t_SubFamily t_NumPrice t_NumExp
    t_NumDens t_NumLoops t_NumNG t_NGExponent t_EtaZero

end Formalism.L2.SG.TheoremS
end
end
end
