module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel
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
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunctionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernelStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  first | exact @GlobalTheory.TwV.DelB.pullAt_of_dict | exact GlobalTheory.TwV.DelB.pullAt_of_dict | (intros; apply GlobalTheory.TwV.DelB.pullAt_of_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullbackScalar_ne_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La La' h1 h2
  have hj' : j + 1 ≤ D.R.m := hj
  have key := fun (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i) (hLb : ((sysS H X std).Pj i).IsLatTup Lb.2) =>
    GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj i hi (clsAt X H i Lb.1 Lb.2) (J.pt std i hi Lb)
      (d.gam i hi Lb) (d.mem i hi Lb) (d.kap i hi Lb) (d.eq i hi Lb hLb)
  have n1 := (key j (Nat.le_of_succ_le hj') La h1).2.2
  have n2 := (key (j + 1) hj' La' h2).2.2
  simp only [Dec.sP, dif_pos hj', Dec.chi]
  exact div_ne_zero (mul_ne_zero n1 (Units.ne_zero _)) (mul_ne_zero n2 (Units.ne_zero _))

end GlobalTheory.TwV.DelB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePairStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | exact GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | (intros; apply GlobalTheory.TwV.DelB.pullbackScalar_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeries

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelB.serAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos d ι hι j hj La La' hLa hLa'
  have hr := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hu := GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d
  have hp := GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel S hDict d j hj La La' hLa hLa'
  have hs := GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair S d j hj La La' hLa hLa'
  exact GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam ι hι (J.rho std) hPos d.eM
    (ltC S.g S.hLT) j La La' (hu j La) (hu (j + 1) La') t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT hPair
    (hr.1 ▸ hj) hLa hLa' (d.sP S j La La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') hs hp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeriesStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  first | exact @GlobalTheory.TwV.DelB.serAt_all | exact GlobalTheory.TwV.DelB.serAt_all | (intros; apply GlobalTheory.TwV.DelB.serAt_all <;> assumption)
end
end
