module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem iota_starProjection_Qsp (D : D7) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (hF : F ∈ D.what₂.V0 μ) :
    D.what₂.iota μ ((D.what₂.Qsp μ).starProjection F) = D.what₂.iota μ F := by
  set a := (D.what₂.Usp μ).starProjection F with ha
  have haU : a ∈ D.what₂.Usp μ := Submodule.starProjection_apply_mem _ _
  have hb : F - a ∈ D.what₂.Qsp μ := ⟨Submodule.sub_mem _ hF haU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have haQ : (D.what₂.Qsp μ).starProjection a = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Submodule.mem_orthogonal _ _).2 fun q hq => Submodule.inner_left_of_mem_orthogonal haU hq.2
  have e : (D.what₂.Qsp μ).starProjection F = F - a := by
    have h := map_add (D.what₂.Qsp μ).starProjection a (F - a)
    rw [add_sub_cancel, haQ, zero_add, Submodule.starProjection_eq_self_iff.2 hb] at h
    exact h
  rw [e, map_sub, LinearMap.mem_ker.1 haU.2, sub_zero]

theorem zeTied_of_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → D.BuRational → ZetaCompatible D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hP hH hB u μ c hfac hnz
  refine Y.ze u μ c hfac hnz ?_
  by_cases hU : Used0 D μ
  swap
  · exfalso
    obtain ⟨φ, x, hx, hne⟩ := hnz
    apply hne
    rw [hfac φ x hx, Y.junk μ hU, LinearMap.zero_apply, (D.Bu_linR u φ).map_zero, mul_zero]
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨Y.tupT μ, Y.tupTie μ hU⟩
  have hRS := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH).1
  have hFo := Y.formsA t
  have hR : LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin = LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin :=
    GlobalTheory.range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E _ _ _ _ _
  have hmem : ∀ f, Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) ∈ D.what₂.V0 (Y.tup t) := by
    intro f
    have h1 : (rV0 D A3.A F.P1 F.ψ1 t).mulVec f ∈ LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin := by
      rw [hR]; exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := h1
    refine ⟨Y.jA t g, ?_⟩
    exact (hFo.op_eq g).trans (congrArg (Y.jA t) hg)
  have hQ : ∃ x f, D.what₂.Bu u (D.jN u (C.eNu u x))
      (D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f))) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨φ0, F0, hF0, hne⟩ := hnz
    apply hne
    rw [hfac φ0 F0 hF0, iota_starProjection_Qsp D _ F0 hF0]
    have h1 : ∀ x, ∀ F ∈ D.what₂.V0 (Y.tup t), D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) F) = 0 := by
      intro x F hF
      obtain ⟨y, rfl⟩ := hF
      let L : D.what₂.Amb (Y.tup t) →ₗ[ℂ] ℂ :=
        ((D.Bu_linR u (D.jN u (C.eNu u x))).mk' _) ∘ₗ D.what₂.iota (Y.tup t) ∘ₗ D.what₂.eOp (Y.tup t)
      have hL : L = 0 := by
        refine LinearMap.ext_on_range hFo.span fun i => ?_
        have h2 : (rE D A3.A F.P1 F.ψ1 t).mulVec (Pi.single i 1) ∈ LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin := by
          rw [← hR]; exact ⟨_, rfl⟩
        obtain ⟨f, hf⟩ := h2
        have e1 : D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)) = Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) :=
          (hFo.op_eq _).trans (congrArg (Y.jA t) hf.symm)
        show D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) (D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)))) = 0
        rw [e1]
        exact hcon x f
      exact LinearMap.congr_fun hL y
    let M : D.what₂.Mu u →ₗ[ℂ] ℂ := (D.Bu_linL u (D.what₂.iota (Y.tup t) F0)).mk' _
    have hM : M = 0 := by
      refine LinearMap.ext_on_range (D.jN_basis u).2 fun i => ?_
      have h3 := h1 ((C.eNu u).symm ((D.div.Nu u).b i)) F0 hF0
      rw [LinearEquiv.apply_symm_apply] at h3
      exact h3
    rw [show D.what₂.Bu u φ0 (D.what₂.iota (Y.tup t) F0) = 0 from LinearMap.congr_fun hM φ0, mul_zero]
  obtain ⟨x, f, hx⟩ := hQ
  have hpt := C.pt u t x f
  have hf := hfac (D.jN u (C.eNu u x)) _ (hmem f)
  rw [iota_starProjection_Qsp D _ _ (hmem f)] at hf
  obtain ⟨w, hw⟩ : ∃ w : D.div.RR.V,
      D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) = D.jEE w :=
    ⟨_, by rw [← Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]; exact hRS.iota t f⟩
  rw [hw, hB] at hx hf
  refine ⟨(F.Dc (R.toCx3 F).zs).Pt (C.wU u) t x f / D.div.Bk u (C.eNu u x) w, ?_⟩
  rw [map_div₀, hpt, hf]
  exact mul_div_cancel_right₀ c hx

end GlobalTheory.Mem.R3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtension

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  let F₀ := reFace F Dc Sp Zsc
  let F₁ := reFace F Dc Sp' Zsc'
  let R₁ := (R.updS kap lam).withErr err
  let zs := (R.toCx3 F₀).zs
  have hz : (R₁.toCx3 F₁).zs = zs :=
    (RealDat3.zs_withErr (R := R.updS kap lam) (F := F₁) err).trans
      ((RealDat3.zs_updS (R := R) (F := F₁) kap lam).trans (show (R.toCx3 F₁).zs = zs from rfl))
  have transportPt : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j htp hj
    subst htp
    cases hj
    exact C.pt
  -- Transport the constructor once so its dependent fields share the source subspace.
  have build := ReadC.mk (R := R₁) (F := F₁) (X0 := X0) (Y := Y₁)
  rw [hz] at build
  exact ⟨build C.wU C.bij C.eNu C.NuC C.nu (transportPt Y₁.tup Y₁.jA h1 h2)⟩

end GlobalTheory.Mem.R3
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeUPrmRNEb

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem.R3 in

theorem GlobalTheory.Mem.Top.Bl.ze_u_prm_of_extension_with_law : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s := by
  intro hPr hL N S Γ hN K q
  have hK : ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t := by
    obtain ⟨B, f, T, w, Z, O, x⟩ := q
    obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
    obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
    obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
    simp only [ofObj, extraObj] at ker_eq
    cases ker_eq
    obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
      ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
        nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
      kT.unf kT.ok kT.served
    exact ⟨t1, (StdModel.stdKer_iff w.I w.l Z t1).2 s1, o1, heq_of_eq e1, a1, p1⟩
  obtain ⟨t, ht⟩ := hK
  let _ : Algebra q.x.what₂.r.z.core.Q.c.F (q.w.D q.Z).what₂.LL := q.x.what₂.r.z.alg
  obtain ⟨Dc, Sp₀, Zsc₀, C₀, -⟩ := _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses _ K q t ht ⟨q.x.rx⟩
  obtain ⟨kap, lam, err, hP, hH, -, -, -, Y', Z', htup, -, hjA, -⟩ := GlobalTheory.Mem.R3.reFace_scalars_errors_readings _ _ _ _ _ _ _
    q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG q.O.ex.p0 q.x.what₂.r.Y q.x.what₂.r.Z Dc Sp₀ q.x.what₂.r.z.F.Zsc (fun _ => Or.inl rfl)
    q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange
  obtain ⟨C'⟩ := GlobalTheory.Mem.R3.readC_reFace_updS q.x.what₂.r.z.R q.x.what₂.r.z.F q.O.ex.p0
    Dc Sp₀ Sp₀ Zsc₀ q.x.what₂.r.z.F.Zsc kap lam err C₀ Y' htup hjA
  obtain ⟨nb⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
  have hBk : BkLaw (q.w.D q.Z) := nb.2.down
  have hRat := GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH
  exact GlobalTheory.Mem.R3.zeTied_of_read hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH (hBk hRat)
end
end
end
