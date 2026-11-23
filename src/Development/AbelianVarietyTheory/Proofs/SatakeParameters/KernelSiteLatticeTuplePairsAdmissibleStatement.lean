module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiDetIdAndChiFacAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColSpanMapMulVecLin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePointStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChartStatement
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerThEntireAlgCoef
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSiteStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnReaderLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactorsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeSucc

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Joint.locSp_kerN_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa v
  obtain ⟨-, -, hker, -⟩ := hD (j + 1) hj La hLa
  obtain ⟨hTT, hLb, -⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  obtain ⟨-, hpt⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La
  have hbas := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa v
  rw [hLb] at hker
  have hcop : Nat.Coprime (I.at' j hj).st.T (D.what₂.places.resChar w) := by
    rw [hTT]
    exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  have hT0 : 0 < (I.at' j hj).st.T := by
    rcases Nat.eq_zero_or_pos (I.at' j hj).st.T with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      exact absurd hcop hp.one_lt.ne'
    · exact h0
  have hun := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have horth : ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (j + 1) hj) co :=
    ⟨_, GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ _ (J.pins.crd_orth (j + 1) hj)⟩
  have hK := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1) J.a horth (J.alg j hj _) (H.core j hj _).int (J.lbB j hj _) hT0
    _ _ (J.pt std (j + 1) hj La) hpt v hun
  have hR := @GlobalTheory.TwV.locSp_reindex _ _ _ (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (_) (_) (_) _ _ _
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk _ _ _ _ _ hker hK
  have hch := (dif_pos hj : chAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om I
    (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb (lev0At J.Gd u w hg).Uloc (j + 1) La = _)
  have hJ := congrArg PtCh.J hch
  have hB := congrArg PtCh.B hch
  have hi := congrArg (fun c => PtCh.iw c v) hch
  have hfr : (J.fd std).frM (j + 1) La v = _ :=
    congrArg (fun M => Matrix.submatrix M (finCongr rfl) (finCongr rfl))
      (congr (congrArg Matrix.map (congr (congrArg HMul.hMul (congrArg (fun Q => LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) Q).toLinearMap) hJ))
        (congrArg Units.val hB))) (congrArg DFunLike.coe hi))
  rw [hfr, hbas]
  have hiw : J.rho std v = ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).iw v := (J.iw j hj _ v).symm
  rw [hiw]
  exact hR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeSuccStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_succ | exact GlobalTheory.TwV.Joint.locSp_kerN_succ | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_succ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeZero

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem Joint.locSp_kerN_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD La hLa v
  obtain ⟨-, -, hK, -⟩ := hD 0 (Nat.zero_le _) La hLa
  rw [(J.lev0 _).1] at hK
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) := (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hT0 : 0 < (D.mem u).A.T := by
    rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : (D.what₂.places.resChar w).Prime).one_lt.ne'
    · exact h
  have hU := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have ho := GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (J.pins.crd_orth 0 (Nat.zero_le _))
  have hs := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint (J.Gd.forms u).cls0.lev (lev0At J.Gd u w hg).A J.a ⟨_, ho⟩ J.alg0 J.one.int J.lb0 hT0 La.1 _
    (J.pt std 0 (Nat.zero_le _) La) (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).2 v hU
  rw [GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa v]
  exact locSp_reindex (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ _ (lev0At J.Gd u w hg).A.rk _ _ _ _ _ hK hs

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeZeroStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_zero | exact GlobalTheory.TwV.Joint.locSp_kerN_zero | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarMemAlgebraicClosure

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hj La La' hLa hLa'
  have hjm : j < D.R.m := lt_of_lt_of_eq hj X.fl_m
  have hj' : j + 1 ≤ D.R.m := hjm
  have hχ := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).1
  have h1 : S.muT (j + 1) ((J.fd std).dt j La) ∈ TaylorLogMetric.Qbar := by
    rw [(hD j hjm.le La hLa).2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D j hjm.le _)
  have h2 : S.muT (j + 1) ((J.fd std).dt (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    rw [(hD (j + 1) hj' La' hLa').2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D (j + 1) hj' _)
  have k1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j hjm.le La hLa
  have k2 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hj' La' hLa'
  exact mul_mem (mul_mem (mul_mem h2 (inv_mem h1)) (zpow_mem (hχ _ _ k1.1 k1.2) _)) (zpow_mem (hχ _ _ k2.1 k2.2) _)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarMemAlgebraicClosureStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  first | exact @GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt | exact GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt | (intros; apply GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
open Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pairOK_allSites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  intro j hj La La' hL hL'
  have hm : (sysS H X std).mm = D.R.m := by
    first | (rfl; done) | exact X.fl_m | exact I.fl_m
  have hjm : j + 1 ≤ D.R.m := hm ▸ hj
  have hSD0 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j (by omega) La hL
  have hSD1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hjm La' hL'
  have hA : TaylorLogMetric.admitted D _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') := ⟨hSD0.1, hSD1.1, hSD0.2, hSD1.2⟩
  have hInt : ∀ x, IntOff (t.O u μ).S (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' x) :=
    fun x => GlobalTheory.T.intOff_xi0_of_joint t std J S j La La' _
  have hK := GlobalTheory.kerTh_entire_algCoef D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (ssRec t u μ) (t.rd u μ).lev _ _ _
    (t.O u μ).S hA (GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J) hInt
  have hC := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).2 _ _ hA
  have hsp : ∀ (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i), ((sysS H X std).Pj i).IsLatTup Lb.2 → ∀ v,
      locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN i Lb) =
        ((sysS H X std).latAt v i Lb.2).map ((((J.fd std).frM i Lb v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
    intro i hi Lb hLb v
    cases i with
    | zero => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_zero t std J hD Lb hLb v
    | succ k => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_succ t std J hD k hi Lb hLb v
  refine ⟨hA, GlobalTheory.T.movedPairDatum_congr t std J S hD j hj La La' hL hL', hK.1, hK.2, GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure t std J S hD j hj La La' hL hL',
    hC.1, hC.2, fun v => ⟨?_, ?_, hsp j (by omega) La hL v, hsp (j + 1) hjm La' hL' v⟩⟩
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ j La v
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ (j + 1) La' v

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_latticeTuplePairs_admissible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  first | exact @GlobalTheory.pairOK_allSites | exact GlobalTheory.pairOK_allSites | (intros; apply GlobalTheory.pairOK_allSites <;> assumption)
end
end
