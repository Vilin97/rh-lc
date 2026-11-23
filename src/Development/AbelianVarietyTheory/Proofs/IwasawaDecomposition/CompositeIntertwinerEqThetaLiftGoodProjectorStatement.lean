module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowProjHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

section TopLevProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsExist_top (R : RealDat D A Ks) (hl : R.toLevCh.Is A.μ0) (t : T) (g0 : G0 R.Pg D.R.r) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ := by
  obtain ⟨c, hc⟩ := hl.βX
  exact GlobalTheory.T.parahoricLevel_liftsExist D.sp.X' R.βX (R.datXt t) _ _ hc (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 g0



theorem topLev_of_clauses (R : RealDat D A Ks) (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hc : R.IsChain)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) : TopLev R F := by
  intro b t y hy
  have hm : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  have hrel : ∀ p : (R.levR F b).H, GlobalTheory.ChainEquiv.Rel R t p (D.R.m - 1) (R.ioX t y)
      ((((R.levR F b).chi p : ℂˣ) : ℂ) • R.ioX t y) := by
    intro p
    have hL := liftsExist_top R hl t (p : G0 R.Pg D.R.r)
    refine hL.elim fun κ' hκ' => ?_
    intro κ hκ v g
    have hF : ∀ w h, (((((R.levR F b).chi p : ℂˣ) : ℂ) • y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w h =
        (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ * (y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w (h * κ') := by
      intro w h
      have hT : HasType D.sp.X' R.βX (withP (R.datXt t) (R.levR F b)) ((y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) :=
        (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ hy w).2
      rw [← GlobalTheory.KeepLevel.eigen_of_hasType hT p hκ' h]
      rfl
    have key := GlobalTheory.ChainEquiv.step R.ψ R.θ hM.inf _ _ (R.ωX t) (hc.ωX t) _ _ _ _ (R.vX t) (hc.ptX t) (R.MY (D.R.m - 1))
      (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) rfl _ (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).1 _
      (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).2
      (hS t _ hm) R.ItX (hc.ItX t).ne _ (GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hM.HX t).2.1) R.βX (R.datXt t) _
      (hM.νX t).1.1 _ (hM.νX t).2 (R.ioX t) (hc.ioX t) (p : G0 R.Pg D.R.r) κ hκ (p : G0 R.Pg D.R.r) κ' hκ' _
      (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hl hM.inf hc.ωX hc.vX t (p : G0 R.Pg D.R.r) κ κ' hκ hκ') y _ hF v g
    have e := (R.ioX t).map_smul (((R.levR F b).chi p : ℂˣ) : ℂ) y
    exact (congrArg (fun U : R.CC t (D.R.m - 1) => (U : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) v g)
      e).symm.trans key
  have hU := (GlobalTheory.KeepLevel.mem_lvlPart_iff (R := R) (R.levR F b) t (D.R.m - 1) (R.ioX t y)).2 hrel
  exact (mem_multT R.θ (R.MY (D.R.m - 1)) _ _ _).2 hU

end TopLevProof



theorem topLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH
  exact topLev_of_clauses R.toRealDat F.lv2 hP.char.base.lev hP.char.base.models
    (RealDat.chain_of_weak hP.char.base.chain hH.aux.ex)
    (fun _ _ _ => GlobalTheory.MultFinite.schurMult hC.2.2.2.2 _ _)

end GlobalTheory.Mem.R3.DTheta
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.lastThetaStep_keeps_faceLevel : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2  := by
  first | exact @GlobalTheory.Mem.R3.DTheta.topLev_holds | exact GlobalTheory.Mem.R3.DTheta.topLev_holds | (intros; apply GlobalTheory.Mem.R3.DTheta.topLev_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjector

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta



theorem composite_eq_lift : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hPins.char.base.chain hHolds.aux.ex
  have hS : StepLev R.toRealDat F.lv2 := GlobalTheory.T.innerThetaSteps_preserve_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hT : TopLev R.toRealDat F.lv2 := GlobalTheory.T.lastThetaStep_keeps_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hP : RowProj R.toRealDat F.lv2 := rowProj_holds hC.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hUsed : ∀ t, Used0 D (Y.tup t) := by
    intro t
    rcases hPins.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h]
      exact Y.tup0
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · rw [iota_sharp]
    exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP (RowSide.sharp D) true Y.Ish Y.tied.sharp
      (Y.tup t) (hUsed t) (Y.jA t x) t (Y.tupT_tup t) _ (Y.topRead t (hUsed t) x)
  · exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP X0.s false Y.Iz Y.tied.base
      (Y.tup t) (hUsed t) (Y.jA0 t x) t (Y.tupT_tup t) _ (Y.topRead0 t (hUsed t) x)

end GlobalTheory.Mem.R3.DTheta
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  first | exact @GlobalTheory.Mem.R3.DTheta.composite_eq_lift | exact GlobalTheory.Mem.R3.DTheta.composite_eq_lift | (intros; apply GlobalTheory.Mem.R3.DTheta.composite_eq_lift <;> assumption)
end
end
