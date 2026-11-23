module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoicesStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
import Formalism.LocalToGlobal.Columns.RowFormsSel

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharWSeedStd

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.StandardWeightCharacter



theorem charW_seed_std : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (C : Formalism.L2.Pj.CoreJ X.toD7) [Algebra C.Q.c.F X.toD7.what₂.LL] (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Inputs X.toD7 → IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A → (∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A C.Q.c.F, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt) → GeoExV (famR X I hX U Xg tr₀) C (face0 X I hX U Xg tr₀).lv2 → Formalism.L2.Host.ValLL X.toD7 R₀.C → C.pb = R₀.C.P.pb → R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2 → R₀.IsInert → R₀.IsTup → R₀.AllPlaces → Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG → ∃ (tr : TrI X.B px) (dict : _) (mu : _) (chiW : _) (x₀ : _) (cE : _) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr R.toRealDat) ∧ Nonempty (@GlobalTheory.RealGeo.GeoHalf X.toD7 _ _ _ _ _ (famR X I hX U Xg tr).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) (inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL)) R.toRealDat fun _ => 1) := by
  intro X px I hX U Xg tr₀ C _ R₀ cG hI hXi hEx hGeo hVal hpb p0 i0 t0 a0 k0
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A C.Q.c.F (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, q1⟩ := analyticW_exists hI hXi hL hF
    (fun R => RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ R) ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    R₀.toRealDat p0 ⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, rfl, id, fun c hc => by cases eq_of_heq hc; exact k0⟩
  have e1 : R1.ExAt := hEx R1 p1 c1 t1 f1 g1
  have l1 : R1.toLevCh = R₀.toLevCh := q1.2.2.2.1
  have hC : R1.C = R₀.C := congrArg (fun L => L.C) l1
  obtain ⟨cutoffDeriv, hcG1⟩ : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  have pc1 : GlobalTheory.RealGeo.PreChar R1 := ⟨p1.1.lev, p1.1.red_R, p1.1.red_L, p1.1.record, p1.1.fam, p1.2,
    RealDat.chain_of_weak c1 e1, RealDat.thP_of_weak t1 e1⟩
  have hV1 : Formalism.L2.Host.ValLL X.toD7 R1.C := by rw [hC]; exact hVal
  have hpb1 : C.pb = R1.C.P.pb := by rw [hC]; exact hpb
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨geo⟩, hrat⟩ := hGeo R1 cutoffDeriv hV1 pc1 p1.1.levels hpb1 (q1.2.2.2.2.2.2.2.2.2 cutoffDeriv hcG1)
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨tr, htr⟩ : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have q5 : RealDat3.IsInert (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).toLevCh = R₀.toLevCh ∧ HEq (R1.upd5 nW FW R1.mu R1.twPl R1.err0).eG R₀.eG ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).ψ = R₀.ψ ∧ (R1.upd5 nW FW R1.mu R1.twPl R1.err0).mu = R₀.mu ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ (R1.upd5 nW FW R1.mu R1.twPl R1.err0)) ∧
      ∀ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (face0 X I hX U Xg tr₀).lv2 c := by
    rcases q1 with ⟨i, t, a, l, e, s, m, w, b, k⟩
    exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
      fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩
  obtain ⟨i1, u1, a1, l6, e6, s6, m6, w6, b6, k6⟩ := q5
  have p6 := RealDat.preliminary_of_scalar_update (RealDat.preliminary_of_index_update p1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update (RealDat.full_Y_of_index_update f1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update (RealDat.weak_chain_of_index_update c1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update (RealDat.weak_theta_props_of_index_update t1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update (RealDat.full_P_of_index_update g1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, hy.trans ?_⟩
    show _ = Formalism.IndefR.Links.cj _ (1 : ℂ) • _
    rw [map_one]
    exact (one_smul ℂ _).symm
  have kv := k6 cutoffDeriv hcG1
  obtain ⟨g', -, -, -⟩ := GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ (famR X I hX U Xg tr₀).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
    (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (fun _ => 1) kap R1.lam R1.err0 geo
  refine ⟨tr, dict, mu, chiW, x₀, cE, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, hchi⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6 f6 g6, l6, e6, hcG1, s6, m6, w6, fun hb => b6 hb, ⟨g'⟩⟩

end GlobalTheory.StandardWeightCharacter
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLargeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.eventually_definiteSpaces_standard_and_large : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  first | exact @GlobalTheory.Mem.StdSize.vstd_size_ev | exact GlobalTheory.Mem.StdSize.vstd_size_ev | (intros; apply GlobalTheory.Mem.StdSize.vstd_size_ev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineAdelicDatumOfHyp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

open Formalism.L2.Pj GlobalTheory.AtMember

namespace GlobalTheory.Mem.R3.Rw

theorem selHalf_of_pin {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (p : ColPin w) : SelHalf w.I := by
  intro a b P hP P' hP' hq
  obtain ⟨q, hq, hqP, hqP'⟩ := hq
  obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
  obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
  have hab : ∀ v, (w.I.sel v).under (𝓞 B.host.F) = v := fun v => by
    have h := p.above v
    unfold Formalism.L2.Host.aboveF at h
    rw [Set.Finite.mem_toFinset] at h
    exact h
  have hmem : ∀ v, ((q : 𝓞 B.host.E) ∈ (w.I.sel v).asIdeal) → (q : 𝓞 B.host.F) ∈ v.asIdeal := fun v h => by
    rw [← hab v]
    show (q : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal.comap (algebraMap _ _)
    rw [Ideal.mem_comap, map_natCast]
    exact h
  have := p.half v v' q hq (hmem v hqP) (hmem v' hqP')
  exact congrArg HeightOneSpectrum.asIdeal this

theorem isIdG_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl



theorem datExS_evLg (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.CasselmanWallach) (h5 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h6 : GlobalTheory.Published.DiscreteSeriesExists)
    (h7 : GlobalTheory.Published.HarishChandraFinite) :
    EvLg fun K B f T => ∀ w : ColW B f T, Pinned K B f T w → ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f →
      R3.GrpAt (w.st Z) w.I → Formalism.L2.Theta.VolTieG (w.D Z) →
      ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
    (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.T.eventually_definiteSpaces_standard_and_large GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))
  rintro K ⟨hK, hKC, hO⟩
  refine hO.imp ?_
  rintro B f T hOv hOB w ⟨pin⟩ Z hX _ hgrp hVol
  set X : Stages := w.st Z with hXd
  set I := w.I with hId
  set Wt : Set B.places.Pl := {v | B.places.resChar v ∈ T.pl} with hWt
  obtain ⟨hHH, -, -, hPos, hStd, hX', -, -⟩ := hK X hOv
  obtain ⟨hVS, hnV⟩ := hKC X hOv
  have hok := w.ok
  have hC := w.C_eq
  have hrange := w.xi_range
  have hsel : SelHalf I := selHalf_of_pin pin
  have hfin : Wt.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B T.pl
  have hconj : ∀ v ∈ Wt, B.places.conj v ∈ Wt :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f ≤ B.KsC := (GlobalTheory.Mem.Base.KsExact.lower w.exact).2.2.1
  have hval : Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) := w.val _ _ _ _ _ _
  obtain ⟨C, alg, hPin, hCe, hCL, hCK, hCE, hLJ, hAT, hVal, hmu⟩ := GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one X f hch hval hVol
  have hLC := hPin.laws
  have hpb := hPin.pb
  obtain ⟨hVals, hOk3⟩ := hOB w.px I hX hok hC hrange
  have hrange' : Set.range I.xi = T.set I.C := by rw [hC]; exact hrange
  obtain ⟨Xg, tr₀, R₀, cG, hLev, hIdG, hGood, hMu, hIdem, hPre0, hIn, hTup, hAll, hKeep, hBrg⟩ :=
    GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices X w.px I hX T Wt C.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hX' hPos hCK hCE
      (fun L hL hLC' => hmu _ L _ hL (hLC'.trans (by rw [hC])))
  have hValR : Formalism.L2.Host.ValLL X.toD7 R₀.C := by rw [hLev.C, hC]; exact hVal
  have hpbR : C.pb = R₀.C.P.pb := by rw [hLev.C, hC]; exact hpb
  have hExAt : ∀ R : RealDat X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀).A C.Q.c.F,
      R.Pre1 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt :=
    fun R hP hc ht _ _ => GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 X.toD7 _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht
  have hfinT : Finite (TupU I (usedOf I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))).1 ∨ τ ∈ tuOf I (usedOf I T Wt)} : Set _).Finite :=
      (Set.finite_singleton _).union (tuOf I (usedOf I T Wt)).finite_toSet
    exact hs.to_subtype
  have hGeoEx := GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne h3 X.toD7 _ _ _ _ _ C (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 hVol hLJ hLC hAT
    hfinT hVS hnV
  obtain ⟨tr, dict, mu, chiW, x₀, cE, R, cG', hPins, hEx, hLevEq, hEG, hCG, -, hmuEq, htw, hBrgI, hGeo⟩ :=
    GlobalTheory.StandardWeightCharacter.charW_seed_std X w.px I hX (usedOf I T Wt) Xg tr₀ C R₀ cG (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 X.toD7) hIdem hExAt hGeoEx
      hValR hpbR hPre0 hIn hTup hAll hKeep
  have hPg : R.Pg = R₀.Pg := congrArg LevCh.Pg hLevEq
  have hRC : R.C = R₀.C := congrArg LevCh.C hLevEq
  have hgood : GoodSet X (px := w.px) (R.eG.trans cG') Xg := by
    rw [trans_eq_of_heq' X R.eG R₀.eG cG' cG hPg hEG hCG]; exact hGood
  let z : Dat X I hX T Wt :=
    { Xg := Xg, tr := tr, core := GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE,
      alg := inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL), alg_eq := hCe, R := R, cG := cG', geo := hGeo.some,
      pins := hPins, lev := by rw [hLevEq]; exact hLev, idG := isIdG_of_heq' X R.eG R₀.eG hPg hEG hIdG, good := hgood,
      mu := by rw [hmuEq, htw]; exact hMu, fieldValues_mem_fixedField := hCL, Ks_le := hCK }
  have hch' := hPins.char
  have hPre : GlobalTheory.RealGeo.PreChar R.toRealDat :=
    ⟨hch'.base.lev, hch'.base.grp.red_R, hch'.base.grp.red_L, hch'.base.grp.record, hch'.base.fam, hch'.base.models,
      RealDat.chain_of_weak hch'.base.chain hEx, RealDat.thP_of_weak hch'.base.thP hEx⟩
  have hP : CorePin (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE).toCore (Fr.at X f).P.pb :=
    hPin.reCore hGeo.some.fw.laws.toLawsM
  refine ⟨z, hEx, ?_, ⟨hP.laws, hP.canon, hP.rank, hP.pb⟩, hBrgI hBrg⟩
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral h3 X.toD7 _ _ _ _ (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) R.toRealDat
    (fun _ => 1) hGeo.some hPre hch'.base.grp.chiW (by show C.pb = _; rw [hRC]; exact hpbR) hnV).1

theorem datExS_of_harishChandra_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → DatExS :=
  fun h1 h2 h3 h4 h5 h6 h7 =>
    GlobalTheory.Mem.Top.GroupRetwisting.Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg (datExS_evLg h1 h2 h3 h4 h5 h6 h7))

end GlobalTheory.Mem.R3.Rw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineAdelicDatumOfPublishedStatementsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExS := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach | exact GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach | (intros; apply GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach <;> assumption)
end
end
