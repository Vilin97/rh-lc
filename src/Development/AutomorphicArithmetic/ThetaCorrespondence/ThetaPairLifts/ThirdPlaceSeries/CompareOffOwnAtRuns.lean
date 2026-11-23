module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlDetEqOneOfMemUnip
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrimeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneOfMemBase

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem compareOffOwn_atRuns_alt : (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) := by
  refine (GlobalTheory.T.runNumericalConditions_hold_along_family 0).imp ?_
  intro eps Fm CH _ hN
  obtain ⟨x0, H⟩ := hN
  refine ⟨x0, fun x hx hx0 i p hp hM r h _ v hv j => ?_⟩
  have hn := (H x hx hx0 i).2.2.2.2
  obtain ⟨hw1, hcore, hrec⟩ := hM
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hw1
  obtain ⟨hch, -, hLU, -, -, -, hpins, hph⟩ := hL
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hch.lev, hch.grp, hch.fam, hch.models, hch.chain, hch.thP⟩
  have hio : IoExt (R2 p) := hp.ioExt
  have hone : ∀ k, OneMapRow0 p.T (R2 p) p.κ p.v₀ (om2 p) k := fun k => (hp.oneMap k).1
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core _ _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (om2 p) hn hC ⟨fw2 p⟩ hio j
    (hpins j) (hone j)
  have hdel : ∀ y, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 y : ℂˣ) : ℂ) ∈ (Fm.D x i).what₂.embLL.range := by
    intro y
    obtain ⟨z, hz⟩ := (Formalism.L2.Pj.FO_le _ (hcore.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) y))
    exact ⟨z, hz⟩
  letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg
  exact GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime _ _ _ _ _ (r.used v).full (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) (h.laws v) hC j (hpins j) (p.betaStd.1 j) hLU hio
    (hone j) (hph j) hspan v hv hch.tup.mu_on p.qGuard (hcore.fieldAt v) hrec.small.val hdel h.half (h.run v hv j) (r.lev j)
    (h.level v j) (h.action v j) (F2 p).P0
    (GlobalTheory.OneMapExact.det_eq_one_of_mem_base (R2 p) (F2 p) hC.grp) (F2 p).ψ0⁻¹
end GlobalTheory.BigOn
end
end
end
