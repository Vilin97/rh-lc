module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLawsStatement
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ToricLatticeDenominators
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan

section

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Exp


open GlobalTheory.TraceIncl in
theorem clSum_equiv_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (g : G) (f : (A.MtCSD i t).Forms) :
    clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g f) = actS R i g (clSum (presV R i t) (kern R i t) f) := by
  refine clSum_act (presV R i t) (kernelLaws hS.models hS.thP hS.typ) (R.B.L i t).act_tie (envV R i t).J_le (actS R i)
    (fun q y w => funext fun v => ?_) g f
  exact (GlobalTheory.T.thetaKernelFiniteAdelic_laws R i t hS.models.inf hS.models.cV hS.thP.ωP hS.thP.pt_theta hS.thP.ioP hS.typ).2.2.2 _ q (hS.red i t q)
    (hl _) y w v


open GlobalTheory.TraceIncl in
theorem clSum_trU_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (f : (A.MtCSD i t).Forms)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    clSum (presV R i t) (kern R i t) (trU (A.leftGroupActionLift i t) U ψ f) v =
      levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
  unfold levelTrace gaL

  rw [trU_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, clSum_equiv_of_lift hS hl, LinearMap.smul_apply, invChar, apply_dite D.what₂.embLL, map_zero]
  rfl


open GlobalTheory.TraceIncl in

theorem exists_adForm_levelTrace {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : ∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (hχ : ∀ k, ∃ a : D.what₂.LL, D.what₂.embLL a = (((envV R i t).χ k : ℂˣ) : ℂ))
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t U ψ 1 θ) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) {w : (R.cV i).W} (hw : InCoefLat R i h w) :
    ∃ y ∈ LinearMap.range θ, ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      adForm R i y (fun ρ => v ρ) = levelTrace R i U ψ (singleSeries R i (R.ωP i t) (R.vP i t) h w v) := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  obtain ⟨e, r, h1, hL⟩ := exists_latSys (i := i) (t := t) hS.lev hT
  obtain ⟨f, hf, j, hj⟩ := hL.exists_trace (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder _ _ _)
    (kernelLaws hS.models hS.thP hS.typ) (h := fin _ h) (x := e.symm P)
    (Submodule.mem_comap.2 ((e.apply_symm_apply P).symm ▸ hP : e (e.symm P) ∈ nabAtr (labLL D) (lamV D i) _))
  obtain ⟨y, -, ey⟩ := exists_src_trU i t U ψ hS.act hf
  have hcw : (presV R i t).coef (e.symm P) = c0L i P := (h1 _).trans (congrArg (c0L i) (e.apply_symm_apply P))
  obtain ⟨a, ha⟩ := hχ j
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  refine ⟨θ (a⁻¹ • y), LinearMap.mem_range_self _ _, fun v => ?_⟩
  have e1 : singleSeries R i (R.ωP i t) (R.vP i t) h (c0L i P) v =
      ((((envV R i t).χ j)⁻¹ : ℂˣ) : ℂ) • clSum (presV R i t) (kern R i t) f v :=
    (hS.kern_fin hh _ v).symm.trans ((congrArg (fun w' => kern R i t (fin _ h) w' v) hcw.symm).trans (congrFun hj v))
  have e2 : adForm R i (θ y) (fun ρ => v ρ) = (1 : ℂ) • levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
    rw [hS.adForm_theta hθ y v, ey, clSum_trU_of_lift hS hl]
  have e3 : adForm R i (θ (a⁻¹ • y)) (fun ρ => v ρ) = D.what₂.embLL a⁻¹ • adForm R i (θ y) (fun ρ => v ρ) := by
    rw [map_smul, adForm_smul]
    rfl
  rw [e3, e2, one_smul, e1, (levelTrace R i U ψ).map_smul, map_inv₀, ha, Units.val_inv_eq_inv_val]

end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCharacterRationalValues

section

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.LevVal

theorem envV_chi_mem {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.Char F)
    (j : Fin D.R.m) (t : T0) (k : (GlobalTheory.TraceIncl.envV R j t).J) :
    ∃ a : D.what₂.LL, D.what₂.embLL a = (((GlobalTheory.TraceIncl.envV R j t).χ k : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := hχ_of R j t
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.ConjForms.chi_mem R h.grp.chiW j PP hP u; ⟨a, ha.symm⟩)
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.PinsOverField.xiR_mem R h.lev h.fam t PP hP u; ⟨a, ha.symm⟩) k
  exact ⟨a, ha.symm⟩

end GlobalTheory.BigOn.LevVal
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiVal

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.LevVal
theorem chi_val_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ p hr hm _ _ j k =>
    envV_chi_mem (R2 p) (F2 p) (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1 j _ k
end GlobalTheory.BigOn.LevVal
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiValStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_character_rational_values' : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.BigOn.LevVal.chi_val_alt | exact _root_.GlobalTheory.BigOn.LevVal.chi_val_alt | (intros; apply _root_.GlobalTheory.BigOn.LevVal.chi_val_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieLift
theorem lift_principal_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0
end GlobalTheory.TieLift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipalStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
  ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' := by
  first | exact @_root_.GlobalTheory.TieLift.lift_principal_alt | exact _root_.GlobalTheory.TieLift.lift_principal_alt | (intros; apply _root_.GlobalTheory.TieLift.lift_principal_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRational

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
theorem adForm_eq_levelTrace_singleSeries' : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  intro _ _ _ _
  have hR := _root_.GlobalTheory.T.rational_estimate_statement'
  have hC := _root_.GlobalTheory.T.twisted_character_rational_values'
  have hN := _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points
  unfold _root_.GlobalTheory.BigOn.RationalityStatement' _root_.GlobalTheory.BigOn.AtPtsAlt at hR
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hC hN ⊢
  refine ((hR.and hC).and hN).imp fun Fm CH _ H => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := H
  obtain ⟨x0, hE⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx hle i p hp hM w hw j h hh w' hw' => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hE x hx hle i p hp
  obtain ⟨θ, hθ⟩ := a1 hM _ hw j
  obtain ⟨hCh, hOk, hU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hS : GlobalTheory.TraceIncl.HidaSetting (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w)) :=
    ⟨hCh.lev, hCh.grp.red_L, hCh.fam.tie, hCh.models, hCh.thP, hU, ⟨_, ((fw2 p).hv₀ j _).1⟩, (hOk.lifts _ _).act,
      fun g0 κ κ' k1 k2 => GlobalTheory.VecInv.omega_lifts_vP (R2 p) hCh.lev hCh.models.inf hCh.thP.ωP hCh.thP.vP j _ g0 κ κ' k1 k2⟩
  obtain ⟨y, -, hy⟩ := exists_adForm_levelTrace hS (a3 hM w hw j) (a2 hM w hw j) hθ hh hw'
  refine ⟨y, ?_, hy⟩
  obtain ⟨n, b, hbK, -, -, -, hsp⟩ := (fw2 p).ks j
  have hy0 := hsp.symm ▸ (Submodule.mem_top (x := y))
  refine Submodule.span_le.2 ?_ hy0
  rintro _ ⟨k, rfl⟩
  have hk : (p.nexp.fi j).e ((p.nexp.fi j).e.symm (b k)) = b k := (p.nexp.fi j).e.apply_symm_apply (b k)
  refine Submodule.subset_span ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 ?_, hk⟩
  first
    | exact hk.symm ▸ hbK k
    | exact (congrArg (fun z => z ∈ (p.R.FW j).WK) hk).mpr (hbK k)
    | (rw [hk]; exact hbK k)
end GlobalTheory.BigOn.Exp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRationalStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adForm_eq_levelTrace_singleSeries : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | exact _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | (intros; apply _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' <;> assumption)
end
end
end
