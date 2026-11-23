module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormLevelZeroRealisesComplexPolyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInCharStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValuesStatement
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GmOfMapEqActC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoordsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValueStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelMoveDegree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelMoveDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTuple

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.DelA.cmp_valsAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hj h La hLa x
  have hr := (GlobalTheory.TwV.DelA.posTie_at S hPos ι hι).2
  obtain ⟨c, κ, _, hκ, hy, hiff⟩ := GlobalTheory.T.realAt_succ_iff_decomposition_values S d j hj h La hLa
  obtain ⟨g, hgb, hpt⟩ := GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart S hDict j hj La hLa
  have hH := ((H.core j hj) ((I.at' j hj).st.eC.symm La.1).1).toHyp Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
  have hv := valC_spec hH.ex ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2 hLa
  refine ⟨MvPolynomial.map D.what₂.embLL (valC ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev (embT D) D.what₂.embLL
    ((I.at' j hj).st.charts.gat ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1)
    (I.at' j hj).st.pos ((I.at' j hj).st.embN ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y
    ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2), ?_, ?_⟩
  · rw [kaAt_cmp X H hT j hj x]
    show MvPolynomial.map _ (cmpC _ _ _ _ _ _ _ _ _ _ _ _) = _
    simp only [cmpC, hLa, if_true]
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    refine congrArg (fun f => MvPolynomial.map f _) ?_
    exact RingHom.ext fun r => (hr r).symm
  · rw [hiff]
    intro z z' hz
    have h2 : trC (X.onCh j hj) (j + 1) ((ex.tw.fm u μ).emb (j + 1) x) =
        (I.at' j hj).M.emb (j + 1) ((I.at' j hj).eps.symm x) := by
      apply trC_heq
      have := (I.at' j hj).eps_emb ((I.at' j hj).eps.symm x)
      rwa [LinearEquiv.apply_symm_apply] at this
    have hp1 := hpt
    rw [d.eq (j + 1) hj La hLa, hy] at hp1
    have hk := congrArg (fun k => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g
      (GlobalTheory.TwU.ratA D.host.F (d.gam (j + 1) hj La) * (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * k)) hκ
    have hp2 := hk.mpr hp1
    have hv2 := hv.2 g hgb c (d.gam (j + 1) hj La) (d.mem (j + 1) hj La) κ hp2 z z' hz
    rw [h2, ← embN_eq_nrmR]
    exact hv2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTupleStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.comparedForm_normalisedValues_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_valsAt | exact GlobalTheory.TwV.DelA.cmp_valsAt | (intros; apply GlobalTheory.TwV.DelA.cmp_valsAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMove

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem natAct_glInv_gmOf : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp), (X.Pj j).natAct (glInv X j (BOf fd j La)) (gmOf fd j La G) = G := by
  intro p _ X D pos fd j La G
  show (X.Pj j).natAct _ ((X.Pj j).natAct (fun v => (glInv X j (BOf fd j La) v)⁻¹) G) = G
  rw [← LinearMap.comp_apply, ← Formalism.MainNotions.G.LatticeSystems.jd_natAct_mul (X.Pj j)]
  simp only [mul_inv_cancel]
  rw [Formalism.MainNotions.G.LatticeSystems.jd_natAct_one (X.Pj j)]
  rfl

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMoveStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.naturalAction_inverseFrame_undoes_move : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp), (X.Pj j).natAct (glInv X j (BOf fd j La)) (gmOf fd j La G) = G := by
  first | exact @GlobalTheory.TwV.DelA.natAct_glInv_gmOf | exact GlobalTheory.TwV.DelA.natAct_glInv_gmOf | (intros; apply GlobalTheory.TwV.DelA.natAct_glInv_gmOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYExpDeg

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_exp_deg : ∀ (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → ∀ α ∈ (polDY D s Q (N' := N')).support, ∀ τ, ∑ b, ∑ a, α (τ, b, a) = ∑ r, ν τ r := by
  intro D N N' s ν Q hQ α hα τ
  exact Formalism.L2.KerInert.SecondKernelMoveDegree.difference_polynomial_degree D N N' s ν Q hQ α hα τ

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolDYGoodDeg

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_goodDeg : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), ∀ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, GoodDeg X j (α.mapDomain (eIdx X D pos j hN)) := by
  intro p _ X D pos j hN ν hν Q hQ s α hα
  unfold GoodDeg
  intro v t
  have hsz := (GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν).2.1 (pos ⟨v, t⟩)
  unfold szT szMu at hsz
  rw [pos.symm_apply_apply] at hsz
  rw [hsz, Formalism.L2.KerInert.SecondKernelMoveDegree.blk_mapDomain X D pos j hN α v t, Finset.sum_comm,
    polDY_exp_deg D s ν Q hQ α hα (pos ⟨v, t⟩)]
  push_cast
  rfl

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSource

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA



theorem moved_forms_at_source : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hjm hne hN
  have hj : j ≤ D.R.m := hjm.le
  have h : ((sysS H X std).Pj j).m + 1 = D.R.N j := rkS _ _ hN
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm hne
  have hPT := (posTie_at S hPos ι hι).1
  have hdg : ∀ τ, (t.O u μ).dgen τ ≠ 0 := by
    intro τ h0
    have h1 := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι τ
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hV : ∀ (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j),
      ((sysS H X std).Pj j).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat j).V, ∃ V : XR ((sysS H X std).Pj j) ℂ,
        MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp j x La.1 La.2) =
          MvPolynomial.map ι V ∧ RealAt d j hj h La ((ex.tw.fm u μ).emb j x) V := by
    intro j
    cases j with
    | zero => intro hj h La hL x; exact GlobalTheory.T.comparedForm_levelZero_realises_complexPoly S hDict hPos ι hι d h La hL x
    | succ k => intro hj h La hL x; exact GlobalTheory.T.comparedForm_normalisedValues_latticeTuple S hDict hPos ι hι d k hj h La hL x
  have core : ∀ La ∈ S.Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, K2.SharpQ t ex.tw u μ j x Q →
      GoodG (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x) ∧ OddDeg (sysS H X std) j (gmS d j La x) ∧
      ∀ n, AddMonoidAlgebra.coeff (polDel (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x)) n =
        ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) •
          AddMonoidAlgebra.coeff (trDY (sysS H X std) ℂ_[D.what₂.places.resChar w] j D (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)
            (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) (polDY D (t.O u μ).dgen (Q (clsAt X H j La.1 La.2)) (N' := D.R.N (j + 1)))) n := by
    intro La hLa x Q hQ
    have hL := S.Y.Rep_lat j La hLa
    obtain ⟨V, hVm, hVr⟩ := hV j hj h La hL x
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d j hj h La
    have hmap := gmOf_map_eq_actC (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2 j La h
      (mM d j hj La) hFr.1 hFr.2.1 _ V hVm
    have hφ : ∀ y, (ex.tw.fm u μ).emb j x (clsAt X H j La.1 La.2) y =
        (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ)⁻¹ * frPoly (t.O u μ) j (Q (clsAt X H j La.1 La.2)) y := by
      intro y
      have h2 := congrFun (hQ.2 (clsAt X H j La.1 La.2)) y
      have hne : (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne j y τ)
      rw [← h2]
      simp only [ColumnChain.sharp, mulFun, LinearMap.coe_mk, AddHom.coe_mk]
      field_simp
    have hR := (GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d j hj h La ((D.chTw u μ).sSharp j) ((ex.tw.fm u μ).emb j x) (Q (clsAt X H j La.1 La.2)) hφ V).1 hVr
    have hw : (fun τ => (D.chTw u μ).sSharp j τ - cTw D j) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.sh τ).symm
    rw [hw] at hR
    exact GlobalTheory.T.operatorPolynomial_of_realising_value (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι j hN (nuT D u j) hWt.nu
      (Q (clsAt X H j La.1 La.2)) (hQ.1 _) (sPt d j hj La) _ (gmS d j La x) hR hmap (t.O u μ).dgen hdg
  refine ⟨fun La hLa x => ?_, fun La hLa x Q hQ n => ?_, fun La hLa x Q hQ α hα => ?_⟩
  · obtain ⟨Q, hQ⟩ := J.sharp j hjm x
    obtain ⟨h1, h2, -⟩ := core La hLa x Q hQ
    exact ⟨GlobalTheory.T.naturalAction_inverseFrame_undoes_move (sysS H X std) D (hT.gat_pos u w hg) d.fd2 j La _, h1, h2⟩
  · rw [(core La hLa x Q hQ).2.2 n]
    simp only [sO, dif_pos hj]
  · exact polDY_goodDeg (sysS H X std) D (hT.gat_pos u w hg) j hN (nuT D u j) hWt.nu _ (hQ.1 _) _ α hα

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSourceStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedForms_operator_degrees_at_kernelSource : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelA.moved_forms_at_source | exact GlobalTheory.TwV.DelA.moved_forms_at_source | (intros; apply GlobalTheory.TwV.DelA.moved_forms_at_source <;> assumption)
end
end
