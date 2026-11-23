module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransferStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModelsStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParamSizeConditions

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.LedSize



theorem evG_exists_sizeRows : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩
  rintro K rfl rfl rfl hs hx hG X hO heta hA
  have hx' := (le_max_left _ _).trans hx
  have hxL := (le_max_right _ _).trans hx
  have hP := K.ok
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  refine ⟨L, e1, ?_⟩
  have hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X' := by
    have hmem := hOk.small.1
    rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
    · exact absurd hi (hOk.small.2.2.2.1 i)
    · rw [e1]; exact hlt
  have xe : L.sc.x = K.s.x := by rw [e1]
  have ee : L.sc.eps = eps := by rw [e1]; exact hs
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes
    M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)
  rw [xe, ee]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)

end GlobalTheory.Mem.R3.LedSize

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParametersParameterSizeConditionsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.eventually_stages_parameterSizeConditions : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  first | exact @GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows | exact GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows | (intros; apply GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn

theorem rowTest_setting_dat : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L →
    GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  refine Ev.mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK B f T w Z hX Wt z hOv hG hEx L hsz
  obtain ⟨hHost, hF, -, -, -, -, -, hstdX⟩ := hK (w.st Z) hOv
  have hC := z.pins.char
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hC hEx).1
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  exact
    { size := hsz
      eser := hG.eSerTie Z.V Z.S Z.G
      host := hHost
      hF := hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := z.pins.keep.guard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := z.pins.keep.std
      stdX := hstdX
      betaX := z.pins.keep.beta.2 }

end GlobalTheory.PrimIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.hidaSetting_of_sizeRows : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f → z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  first | exact @GlobalTheory.PrimIn.rowTest_setting_dat | exact GlobalTheory.PrimIn.rowTest_setting_dat | (intros; apply GlobalTheory.PrimIn.rowTest_setting_dat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

noncomputable section

theorem GlobalTheory.RowEx.dat_choice_exists : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  classical
  intro hE
  obtain ⟨CF0, hE⟩ := hE
  refine ⟨CF0, fun CF hCF => ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩⟩
  obtain ⟨x₀, hx⟩ := hE eps CF hCF
  refine ⟨x₀, fun K _ _ _ hK hxK => ?_⟩
  have hF := hx K.s hK hxK
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if h : Ξ.Finite then Classical.choose (hF P f Ξ h) else ∅, by simp, ?_, ?_⟩
  · intro P f _ _ Ξ z hz
    by_cases h : Ξ.Finite
    · dsimp only at hz
      rw [dite_eq_left h] at hz
      exact (Classical.choose_spec (hF P f Ξ h)).1 z hz
    · dsimp only at hz
      rw [dite_eq_right h] at hz
      simp at hz
  · intro B f T _ hH _ _ w Z hX Wt z L hL hS
    obtain ⟨hq, hC, hfin, hmem⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
    have hS2 := hH.2
    dsimp only at hS2
    rw [dite_eq_left hfin] at hS2
    rw [hL]
    exact (Classical.choose_spec (hF B.toPre f (T.set f) hfin)).2 (w.st Z) f rfl HEq.rfl L hL _ _ _ _ _ _ _ hS hC hq
      (fun t => ⟨_, hmem t, HEq.rfl⟩) (fun y hy => hS2 y hy)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  exact @GlobalTheory.RowEx.dat_choice_exists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatRowTest

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.RowAt

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩



theorem atDat_rowTest : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK →
    RatioK → GlobalTheory.RowEx.ExField → StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt →
      GlobalTheory.RealGeo.InGeo z.geo → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  intro hG hC h1 h2 h3 h4 h5 h6 h7 hEF
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.rowTest_at_realisation_of_hilbertModels hC h1 h2 h3 h4 h5 h6 h7
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData hEF
  have hCh := H2 (max CF1 CF2) (le_max_right _ _)
  have e1 := ((evG_of_ev (ev_scale fun eps _ => H1 eps (max CF1 CF2) (le_max_left _ _))).inter GlobalTheory.T.eventually_stages_parameterSizeConditions).inter
    (evG_of_ev GlobalTheory.T.hidaSetting_of_sizeRows)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg hCh)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨⟨x₀, hx, hH⟩, hLed⟩, hSet⟩ B f T hO - - hch w - Z hX Wt z g1 - hEx -
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz⟩ := hLed (w.st Z') hO hη hA
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  exact (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer B w.C Z Z' w.px w.I hX T Wt s z).2 (by
    have hEx' := DatCopy.copy_exAt Z' s hEx
    generalize DatCopy.copy Z' s z = y at hEx' ⊢
    have hS := hSet B f T w Z' hX Wt y hO g1' hEx' L hsz
    exact hH (w.st Z').toD7 L (by rw [hsc]) (by rw [hsc]; exact hx) _ _ _ _ _ _ y.R y.F hS (hch w Z' hX Wt y L hsc hS))

end GlobalTheory.Mem.R3.Rw.RowAt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatRowTestOfExField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.RowClaim

namespace GlobalTheory.Twist

theorem atDat_rowTest_of_exField : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → GlobalTheory.RowEx.ExField → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun hG hC h1 h2 h3 h4 h5 h6 h7 hE => GlobalTheory.Mem.R3.Rw.RowAt.atDat_rowTest hG hC h1 h2 h3 h4 h5 h6 h7 hE

end GlobalTheory.Twist
end
end
