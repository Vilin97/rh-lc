module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesStStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceStStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct



open GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TupLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem baseOf_of_pin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.BigOn.Exp.TupLe

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe.CoefPf
theorem coefSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm B hB hBo c hc hS u hu O' hO' h hh v hv
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hS
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨F, hF0, rfl⟩ := GlobalTheory.T.coefLattice_indep_coefMap_proof D _ _ _ p.P.A3.A _ (R2 p) (F2 p) hC j c0L ⟨gramR, c0R, hft⟩ h v hv
  have hio : IoExt (R2 p) := hr.ioExt
  have hv0 : IsChosenExtremalVector (R2 p) j (sg0 D p.P.A3.A) (p.v₀ j _) := (hL.2.2.2.2.2.2.1 j).2.lift.v0
  have hval : ∀ w, (R2 p).ioP j (PiTensorProduct.tprod ℂ u') w ∈ harm (Wc D j).rank B.w B.F.BS := by
    have hcV : ((R2 p).cV j).Is := hC.models.cV j
    obtain ⟨u'', w₀, hu'', -, hw⟩ := IsChosenExtremalVector.io _ hv0 hio
    have huu : u'' = u' := funext fun ρ => Subtype.ext ((hu'' ρ).trans (hu ρ).symm)
    rw [huu] at hw
    have hT := GlobalTheory.SeriesTie.Scale.io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta
      (PiTensorProduct.tprod ℂ u')
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u'))) (fun g => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 g
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h0 | h0
    · have h1 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h0 ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap
        ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')))
  have hL0 : (B.F.ΛS : Set (Fin (Vc D j).rank → D.host.E)) = L0c D (Vc D j) := by
    rw [hBo.ΛS]
    exact GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hL.1.lev.βV j)
  refine ⟨c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F), ?_, (smul_inv_smul₀ hc _).symm⟩
  refine (mem_harmLat _ _ _).2 ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
  have hF' : harmFn (Wc D j).rank B.w B.F.BS ((R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := hF F
  rw [map_smul, hF', inv_smul_smul₀ hc, hBo.lam, GlobalTheory.LatAtHLat.latAt_eq_hLat D _ _ B hL0]
  exact Submodule.subset_span ⟨F, hF0, rfl⟩
end GlobalTheory.BigOn.Exp.TupLe.CoefPf
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefStStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.tuple_coef_le : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SmallSpan
variable {D : D7} {m n : ℕ}
theorem smallSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP
end GlobalTheory.SmallSpan
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBisStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.small_tuple_statement_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.SmallSpan.smallSt_alt | exact _root_.GlobalTheory.SmallSpan.smallSt_alt | (intros; apply _root_.GlobalTheory.SmallSpan.smallSt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLe

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twLe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  intro _ _ _ hA hX
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hX) fun Fm x hx i p hr hm w hw j ⟨a, c⟩ ρ hρ ν rd hf hc => ?_
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have h0 := baseOf_of_pin (cG := p.cG) p.charW.base.lev hρ hf.pin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  obtain ⟨c1, c2⟩ := c ρ hρ hf.adapted
  obtain ⟨-, e, h1, h2⟩ := hf.adapted
  exact _root_.GlobalTheory.BigOn.Exp.TupLe.realTw_le_alt _root_.GlobalTheory.T.seesaw_places_statement _root_.GlobalTheory.T.tuple_flat_estimate _root_.GlobalTheory.T.tupLe_traceSt _root_.GlobalTheory.T.tuple_coef_le _root_.GlobalTheory.T.small_tuple_statement_alt hr hm hL hw a.1 hρ hf.pin hf.level
    { h0 with } e h1 h2 c1 c2 hf.norm hf.rat hc
end GlobalTheory.BigOn.Exp.TupLe
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twist_upper_bound_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt <;> assumption)
end
end
end
