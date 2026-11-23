module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlaceStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem.R3

namespace GlobalTheory.KapIsotRead




theorem isot_ne_bot_read : GlobalTheory.Published.HarishChandraFinite → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.L2.DIV.GoodStable A3.A.X → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥ := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPin hH hME hGS hgen σ i
  have hL := Y.tied.lift
  obtain ⟨w, hw, hw0⟩ := GlobalTheory.KapIsot.exists_mem_isotL hP R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hPin.char hH.aux.ex).1 hME hGS hgen Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ))) (principalLevelFrame.rowRepR_occ _ _)
  intro hbot
  let L := RecTie.toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj
  let lw : L.AmbW i := (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i) w
  have hgood : lw ∈ L.Wc i := Submodule.mem_map_of_mem hw.1
  let y : D.what₂.Mj ((i : ℕ) + 1) := (Y.IL.jMj i).symm ⟨lw, hgood⟩
  have hjy : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) = lw := by
    simp only [y, LinearEquiv.apply_symm_apply]
  have hmem : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) ∈ Y.IL.prtW i (D.what₂.ft σ) := by
    rw [hjy, Y.prtWE]
    exact ⟨w, hw, rfl⟩
  have hy0 : y ∈ D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) := (hL.isot i _ y).2 hmem
  rw [hbot, Submodule.mem_bot] at hy0
  apply hw0
  have h1 : lw = 0 := by rw [← hjy, hy0, map_zero]; rfl
  exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i).injective (h1.trans (map_zero _).symm)

end GlobalTheory.KapIsotRead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HarishChandraInputsCombined

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i



theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows


end GlobalTheory.Fc.KapLinked

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HarishChandraInputsCombined

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fc.KapLinked
section Rows
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Rows

theorem row_kap_of_row_lam_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  intro a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a15 a16 a17 hL N S Γ h
  obtain ⟨R, hR, h⟩ := h
  refine ⟨R, hR, Row.imp h fun 𝒜 σ s hl => ?_⟩
  have key : AtAll (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) 𝒜 σ := by
    intro eps Fm hc x hx i
    obtain ⟨κ, -, -, hb⟩ := s Fm hc
    refine Built.ind (Bd := _root_.GlobalTheory.Fc.BundleCondition) (R := fun D _ _ b => (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → Formalism.L2.Rows.RowsHoldLam3 b.P →
      Formalism.L2.Rows.RowsHoldKap3 b.P) ?_ (hb x hx i).1 ⟨_, ⟨Fm.params x hx i⟩⟩ (hl Fm hc x hx i)
    intro K β c b _ _ hk
    obtain ⟨q, b', ⟨w⟩, he⟩ := hk
    have e := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (∃ L : SizeData₂ s.1, Nonempty (ParameterChoice' s.1 L)) →
      Formalism.L2.Rows.RowsHoldLam3 s.2.2.P → Formalism.L2.Rows.RowsHoldKap3 s.2.2.P) he
    refine cast e.symm fun hP hLam => ?_
    have hb' : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
    change Formalism.L2.Rows.RowsHoldLam3 b'.P at hLam
    change Formalism.L2.Rows.RowsHoldKap3 b'.P
    rw [hb'] at hLam ⊢
    have hM : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat :=
      _root_.GlobalTheory.T.twisted_multiplicity_one a6 a7 a2 a1 a8 a9 a10 a15 a16 a17 q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
        q.x.what₂.r.z.pins.char q.x.what₂.exAt w.y.y.host hP q.B.ccK_top q.x.what₂.r.z.pins.keep.guard (goodTypes_of_rows q.x.what₂)
    exact GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace ⟨a3, a4, a5, a1, a2⟩ _ _ _ _ _ w.x.A3 _ w.x.R w.x.F w.x.cG _ w.x.Y w.x.Z _ w.x.pins w.y.intersectionNumber_baseChange hLam
      (isot_ne_bot_of_rows a1 a17 q.x.what₂ hM) q.x.obj.kapR
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => Ind.ev_of_atAll key Fm (w3_a hc)⟩⟩
end GlobalTheory.Fc.KapLinked
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

theorem _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowKappaCondition := by
  first | exact @_root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | exact _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt | (intros; apply _root_.GlobalTheory.Fc.KapLinked.row_kap_of_row_lam_alt_alt <;> assumption)
end
end
end
end
