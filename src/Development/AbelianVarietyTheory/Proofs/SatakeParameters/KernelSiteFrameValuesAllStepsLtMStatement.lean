module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicLatticeTupleDecompositionStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalf
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleReadingEqOfRealisingPolynomialStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSourceStatement
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPointStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalarStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalfStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_site | exact GlobalTheory.TwV.DelB.delPolAt_site | (intros; apply GlobalTheory.TwV.DelB.delPolAt_site <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomial

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem polD_eq_map_polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D s Q y' =
      MvPolynomial.map (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q) := by
  set v : GL3Theta.FrV D N' → ℂ := fun k => y' k.1 k.2.1 k.2.2
  have hmap : ∀ P : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ),
      MvPolynomial.map (MvPolynomial.eval v) P = MvPolynomial.mapAlgHom (MvPolynomial.aeval v) P := fun P => rfl
  rw [hmap]
  unfold GL3Theta.polD polDY
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun k => ?_

  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.mapAlgHom_apply]
  split_ifs with h
  · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_mul]
    simp [v]
  · simp

theorem applyFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame := by
  intro D N N' s Q G y'
  rw [polD_eq_map_polDY]
  unfold GL3Theta.applyAt0 framePol GL3Theta.evFr

  rw [map_sum]
  symm
  rw [← Finset.sum_subset (MvPolynomial.support_map_subset
    (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q))]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.eval_C, mul_assoc]
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff] at hα
    rw [MvPolynomial.coeff_map] at hα
    rw [map_mul, hα, zero_mul]

theorem entQFrame : Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ i c Q c' y'
  unfold Formalism.L2.KerInert.SecondKernelDifference.entQ
  rw [applyFrame]
  rfl

theorem applyFrame_and_entQFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame :=
  ⟨applyFrame, entQFrame⟩

end GlobalTheory.TwV.DelA
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomialStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  first | exact @GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | exact GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | (intros; apply GlobalTheory.TwV.DelA.applyFrame_and_entQFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtM

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem tieDel_all_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw j hj ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hj1 : j + 1 ≤ D.R.m := hj
  by_cases hne : Nonempty (Lv.comp j) ∧ Nonempty (Lv.comp (j + 1))
  swap
  · refine ⟨1, norm_one, ?_⟩
    intro La _ x c' L' _
    exact absurd ⟨⟨La.1⟩, ⟨c'⟩⟩ hne
  obtain ⟨⟨a⟩, ⟨a'⟩⟩ := hne
  obtain ⟨hn1, -, hsame⟩ := GlobalTheory.T.stepDeterminantConstant_unit_independent S hPos ι hι j hj1 a a'
  set cK := cKs S ι j hj1 a a' with hcK
  refine ⟨cK, hn1, ?_⟩
  obtain ⟨-, -, hrk, hRT⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hN := hRT j
  have h1 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := hrk (j + 1)
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hDict
  intro La hLa x c' L' hL'

  have hQ : K2.SharpQ t ex.tw u μ j x (K2.qOf t ex.tw u μ j x) := by
    have hex := J.sharp j hj x
    unfold K2.qOf
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  set cc := clsAt X H j La.1 La.2 with hcc
  set κ := clsAt X H (j + 1) c' L' with hκ
  set Q := K2.qOf t ex.tw u μ j x with hQdef
  set P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ :=
    ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j cc) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) κ) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q cc) ((t.rd u μ).Th t.seam t.amb j cc κ)) with hP
  have hPw : P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) :=
    Submodule.smul_mem _ _ ((wt_polDY_framePol D (rk_le _ D hN) (t.O u μ).dgen _ (Q cc) (hQ.1 cc)).2 _)
  set φ := K2.entRec t ex.tw u μ j cc x with hφ
  have hφκ : ∀ y, φ κ y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y := by
    intro y
    have e := (GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial).2 D L hT Gi Gl Kc Dx cX ex t u μ j cc (Q cc) κ y
    have e2 : φ κ y = entQ t u μ j cc (Q cc) κ y := rfl
    rw [e2, e, hP, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

  have hR : ∀ d : Dec J std, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj1 h1 (c', L') φ V ∧
      MvPolynomial.map ι V = cK • S.Y.DelF j ((kaAt X H hT).cmp j x La.1 La.2) (srOf S.Y j La (c', L')) := by
    intro d
    obtain ⟨V, hV, hmap⟩ := GlobalTheory.T.transportedFramePolynomial_complex_values_at_point S hPos ι hι d j hj1 h1 (c', L') φ P hPw hφκ
    refine ⟨V, hV, ?_⟩
    rw [hmap]
    obtain ⟨hMove, hOp, hDeg⟩ := GlobalTheory.T.movedForms_operator_degrees_at_kernelSource S hDict hPos ι hι d j hj ⟨a'⟩ hN
    have hEq := GlobalTheory.FrameB.equiv_frame_b S.Y d.fd2 (ltC S.g S.hLT) (GlobalTheory.FrameB.ltC_ne S.hLT)
      ((GlobalTheory.TwV.DelB.frames_invertible S).2 d) j
    have hsc : ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
        ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
        cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) *
          ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2 := by
      intro La La' _ _
      have e := GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar S hPos ι hι d j hj1 La La'
      rw [hsame] at e
      exact e
    have hDel := GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf S hDict hPair hPos hLaw d ι hι (fun j => phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j)
      (fun j c' L' => GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j (c', L'))
      (fun j c' L' => scT d S ι j c' L') (sO d ι) (gmS d) j hj cK hN hMove hOp hDeg hEq hsc
    have := hDel La hLa x Q hQ c' L' hL'
    exact this
  obtain ⟨V0, hV0, hm0⟩ := hR d0
  have hall : ∀ d : Dec J std, RealAt d (j + 1) hj1 h1 (c', L') φ V0 := by
    intro d
    obtain ⟨V, hV, hm⟩ := hR d
    have : V = V0 := MvPolynomial.map_injective ι ι.injective (hm.trans hm0.symm)
    exact this ▸ hV
  have hrd := GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial S hDict ι j hj1 h1 (c', L') hL' φ V0 hall
  exact hrd.trans hm0

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtMStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  first | exact @GlobalTheory.TwV.DelA.tieDel_all_steps | exact GlobalTheory.TwV.DelA.tieDel_all_steps | (intros; apply GlobalTheory.TwV.DelA.tieDel_all_steps <;> assumption)
end
end
