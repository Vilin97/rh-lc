module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Formalism.LocalToGlobal.InertKernelTheory.FrameInt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosGOfLamPos

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem lamPosG_of_lamPos : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E.toCEmb pos lam ρ → RepFrame.LamPosG X E D pos lam ρ := by
  intro p _ X _ E D pos lam ρ h v s x
  rw [h v s x]
  rfl

end GlobalTheory.TwU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SitePrime



theorem resChar_not_mem_S : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J hmem
  obtain ⟨-, -, -, hg'⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨-, -, -, -, -, hT'⟩ := id hg
  rw [t.O_S u μ] at hmem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | (h | h) | h
  · exact hT' (h ▸ dvd_rfl)
  · exact hg' 0 h
  · exact hg' 1 h
  · exact J.away h

end GlobalTheory.TwV.SitePrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimesStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.site_residue_char_not_mem_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  first | exact @GlobalTheory.TwV.SitePrime.resChar_not_mem_S | exact GlobalTheory.TwV.SitePrime.resChar_not_mem_S | (intros; apply GlobalTheory.TwV.SitePrime.resChar_not_mem_S <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J
    exact ⟨hpos, fun hd => GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J, fun j _ L0 _ La' _ y => GlobalTheory.T.intOff_xi0_of_joint t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStepStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  first | exact @GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | exact GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | (intros; apply GlobalTheory.TwV.kernelSite_seriesData_below_lastStep <;> assumption)
end
end
