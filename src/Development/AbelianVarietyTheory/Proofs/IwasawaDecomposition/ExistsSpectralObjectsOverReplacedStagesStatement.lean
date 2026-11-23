module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRowsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevelStatement
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSRestRe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConjStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrank

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowIsometryConjugatedGoodRowsFinrankStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  first | exact @GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | exact GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | (intros; apply GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoicesStatement

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensio

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelColumnsGoodRowsLePrincipalAndFiniteDimensioStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  first | exact @GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | exact GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | (intros; apply GlobalTheory.Mem.SRe.levCols_le_triv_and_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStages

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

namespace GlobalTheory.Mem.SRe



theorem exists_sRest_top : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro hDS hHC hCusp hDSU hRF D G' _ _ Pl0 T A Ks _ _ _ R F F0 P eE hGap hph hL hR hDs hLev hGrp hPin hE0 hM hRange hNorm hDall
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel D G' Pl0 T A Ks R F P.X P.inst P.pin hLev hGrp hPin hE0
  obtain ⟨v₀, hv, c, hc, hev⟩ :=
    GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj hDS hCusp hDSU hRF D G' Pl0 T A Ks R F P.X P.inst t P.pin hGap hLev hM.inf hM.ν0 ht
  have hg := GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c hLev hM.inf hv ht hev
  have hle := (GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional hHC hCusp D G' Pl0 T A Ks R F hLev hM.inf hM.ν0).1
  obtain ⟨hfr, j, hj⟩ :=
    GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c eE hc hv hM.HE hRange hNorm hle hev hg.1
  refine ⟨hfr hDall, j, t, c, hc, ht, hg.2, hj, ?_⟩
  intro N hh F' hs
  have hF := GlobalTheory.T.finX_spectralRedivisionFullChoices D ⟨P.toNew (hfr hDall) j, N, hh⟩ P.X P.Y P.fin
  obtain ⟨S, hS⟩ := exists_sRest_re D F0 P (hfr hDall) j N hh F' hs hF hph hL hR hDs
  exact ⟨hF, S, hS⟩

end GlobalTheory.Mem.SRe
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

theorem _root_.GlobalTheory.T.exists_spectralLevel_objects_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  first | exact @GlobalTheory.Mem.SRe.exists_sRest_top | exact GlobalTheory.Mem.SRe.exists_sRest_top | (intros; apply GlobalTheory.Mem.SRe.exists_sRest_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStages

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.SRe

section Parts

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
  {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
  {F0 : ∀ u, Forms0 a.D u} (P : SPack a.D F0) {F₁ : ∀ u, Forms0 (reL a Z).D u} (hs : SameL a Z F0 F₁)
  (hF : FinX (reY Z P.Y))



def packL : SPack (reL a Z).D F₁ := (by with_unfolding_all exact ((P.re Z hs hF) :))



def restL (S : SRest (P.re Z hs hF)) : SRest (packL a Z P hs hF) := (by with_unfolding_all exact (S :))



theorem restL_j (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) :
    (restL a Z P hs hF S).j = (by with_unfolding_all exact (j.trans (eEECre Z P.G) :)) := (by with_unfolding_all exact (hS :))



theorem nonempty_sAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H)
    (t : GA a.D (a.D.sp.Y 0)) (c : ℝ) (hc : 0 < c) (see : SeeAt R F P.X P.inst t)
    (ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c)
    (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (rowJ : RowJ R eE P.X P.inst P.G t j)
    (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) : Nonempty (SAtL a Z R F eE F₁) := by
  have h1 := mvRowJ a Z R P.X P.inst P.G t eE j rowJ
  have h2 := restL_j a Z P hs hF j S hS
  letI := alg (reL a Z) iK
  exact ⟨{ P := packL a Z P hs hF
           S := restL a Z P hs hF S
           t := tL a Z t
           c := c
           c_pos := hc
           see := (by with_unfolding_all exact ((mvSee a Z R F P.X P.inst t see) :))
           ev := (by with_unfolding_all exact ((mvEv_holds a Z R F P.X P.inst P.G t c ev) :))
           rowJ := by rw [h2]; exact (by with_unfolding_all exact (h1 :)) }⟩

end Parts



theorem satOfDiscreteSeries : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  intro h1 h2 h3 h4 h5 B C a G' _ _ Pl0 T A Ks _ _ _ R F F0 eE P hG hI hL hRT hDs hLev hgl hPin hE0 hMod hRg hN hDall
  obtain ⟨hD, j, t, c, hc, see, ev, rowJ, rest⟩ := GlobalTheory.T.exists_spectralLevel_objects_replacedStages h1 h2 h3 h4 h5 a.D G' Pl0 T A Ks R F F0 P eE hG hI hL hRT hDs
    hLev hgl hPin hE0 hMod hRg hN hDall
  refine ⟨P.toNew hD j, fun N hh F₁ hs => ?_⟩
  obtain ⟨hF, S, hS⟩ := rest N hh _ hs
  exact nonempty_sAtL a _ P hs hF R F eE t c hc see ev j rowJ S hS

end GlobalTheory.Mem.SRe

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStagesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_spectralObjects_over_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  first | exact @GlobalTheory.Mem.SRe.satOfDiscreteSeries | exact GlobalTheory.Mem.SRe.satOfDiscreteSeries | (intros; apply GlobalTheory.Mem.SRe.satOfDiscreteSeries <;> assumption)
end
end
