module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFunStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRows
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSer
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodOpStarTranslatedEvalEqGoodProjectorStatement
public import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNormStatement
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_continuousRep_intertwinerImage_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  exact @GlobalTheory.ConjRowRepR.exists_contRep_rows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMap

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

theorem conj_row_eq_eval_mult : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hH hιE t c v₀ ht hCL hc hv₀ φ hφ
  have hL := (GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hH).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuousRep_intertwinerImage_rows hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, Submodule.subset_span
    ⟨GlobalTheory.T.conjugatedIntertwiner_values_smoothAutomorphic hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     GlobalTheory.T.conjIntertwinerMap_values_isCuspFun hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep, ?_, ?_⟩, ?_⟩
  · intro τ g hg v w hw
    exact GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ g hg v w hw
  · intro τ v x
    exact GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ v x
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      apply (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
      erw [e, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.ConjRowMult

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  exact GlobalTheory.ConjRowMult.conj_row_eq_eval_mult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  first | exact @GlobalTheory.SeeInt.conjModel_of_setting | exact GlobalTheory.SeeInt.conjModel_of_setting | (intros; apply GlobalTheory.SeeInt.conjModel_of_setting <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  first | exact @GlobalTheory.TranslatedEvalInj.eq_zero | exact GlobalTheory.TranslatedEvalInj.eq_zero | (intros; apply GlobalTheory.TranslatedEvalInj.eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeEval
section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem postOn_eq_of_mem (R : RealDat D A Ks) (F : Face D A) {S : MMap (MP R)} (hS : S ∈ EP R F) :
    postOn (MP R) R.e0 S = S :=
  sub_eq_zero.mp (LinearMap.mem_ker.mp hS.2)

theorem rg_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (φ : L2X X) (h2 : star (Gd.Rg (star φ)) = φ) :
    Gd.Rg (star φ) = star φ :=
  calc Gd.Rg (star φ) = star (star (Gd.Rg (star φ))) := (star_star _).symm
    _ = star φ := by rw [h2]

theorem ev_sub (R : RealDat D A Ks) (v₀ : (MP R).Vec) (S S' : MMap (MP R)) (y : GA D (Yc D 0)) :
    ev (MP R) v₀ (S - S') y = ev (MP R) v₀ S y - ev (MP R) v₀ S' y := by
  simp [ev_apply]
  rfl

end SlopeTestRemainingChoices

theorem evalTieT_of_levelMatch : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hE Gd t ht hConj hRow
  obtain ⟨c, hc, hsm⟩ := GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep hDS R F X h hLev hGrp hMod hHost hE
  let v₀ : (MP R).Vec := fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by
    simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(c τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  have hne : ∀ τ, (v₀ τ : (MP R).H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨σ, red, hA, -, -⟩ := id hRow
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  refine ⟨c0, Formalism.IndefR.AutomorphicEvaluation.evalTieT_of _ _ _ _ X Gd _ t c0 v₀ hnorm ?_ ?_ ?_⟩
  · intro S hS
    obtain ⟨hmem, hint, -⟩ := hN v₀ hnorm S hS
    have hHH := GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace R F X h hLev hGrp hMod hHost hE t c v₀ ht hA hc hv₀ S hS _ hmem.coeFn_toLp
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hS.1 _ hmem.coeFn_toLp
    rw [postOn_eq_of_mem R F hS] at h1
    have hfix : Gd.Rg (star (hmem.toLp _)) = star (hmem.toLp _) :=
      rg_fix X Gd _ (Lp.ext (h1.trans hmem.coeFn_toLp.symm))
    refine ⟨⟨hmem.toLp _, Submodule.mem_inf.mpr ⟨hHH, LinearMap.mem_ker.mpr (sub_eq_zero.mpr hfix)⟩⟩,
      hmem.coeFn_toLp, ?_⟩
    show ‖(hmem.toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hmem]
    exact hint
  · intro Φ
    have hF : star (Φ : L2X X) ∈ goodSub X Gd := Φ.2
    have hfix : Gd.Rg (star (Φ : L2X X)) = star (Φ : L2X X) :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hF).2)
    obtain ⟨S, hSM, hSF⟩ := GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap hDS R F X h hLev hGrp hMod hHost hE t c v₀ ht hConj hc hv₀ (Φ : L2X X)
      (Submodule.mem_inf.mp hF).1
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hSM _ hSF
    rw [hfix, star_star] at h1
    have hz := GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero R F X h hLev hGrp hMod t v₀ hne S hSM _ rfl (by
      filter_upwards [h1, hSF] with x h1x h2x
      refine (ev_sub R v₀ _ _ _).trans ?_
      exact sub_eq_zero.mpr (h1x.symm.trans h2x))
    exact ⟨S, ⟨hSM, LinearMap.mem_ker.mpr hz⟩, hSF⟩
  · intro S hS h0
    obtain ⟨-, hint, hzero⟩ := hN v₀ hnorm S hS
    have hI : ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [h0] with x hx
      have : ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = 0 := hx
      simp [this]
    rw [hI] at hint
    have hre : (ipM (MP R) R.ν0 R.fd0 S S).re = 0 := by
      rcases mul_eq_zero.mp hint.symm with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact hzero hre

end GlobalTheory.SeeEval
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  exact @GlobalTheory.SeeEval.evalTieT_of_levelMatch
end
end
