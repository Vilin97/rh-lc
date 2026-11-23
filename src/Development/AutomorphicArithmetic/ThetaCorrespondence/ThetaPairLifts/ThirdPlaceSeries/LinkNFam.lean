module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.NchTieTr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPointMultiplicityLeRankProofStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusionStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivisionStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LinkNOfGd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.At23OfAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtraBoundOfTwistingEigenFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTailStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalTypeDeterminedAtAllPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivisionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeightsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeightsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

def ThetaScalarNonzero (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ D.what₂.isot j σ,
    D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = lam • f

theorem thetaT_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) (hI : DirectSum.IsInternal (D.what₂.isot j))
    (h : ThetaScalarNonzero D μ j) : Function.Injective (D.what₂.thetaT μ j) := by
  classical
  choose lam hlam0 hlam using h
  set T : Module.End ℂ (D.what₂.Mj j) := (D.what₂.thetaP μ j).comp (D.what₂.thetaT μ j) with hTdef
  have hsub : ∀ σ, D.what₂.isot j σ ≤ Module.End.eigenspace T (lam σ) := by
    intro σ f hf
    rw [Module.End.mem_eigenspace_iff]
    exact hlam σ f hf
  have htop : (⊤ : Submodule ℂ (D.what₂.Mj j)) ≤ ⨆ (c : ℂ) (_ : c ≠ 0), Module.End.eigenspace T c := by
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun σ => le_trans (hsub σ) ?_
    exact le_iSup₂_of_le (lam σ) (hlam0 σ) le_rfl
  have hind : iSupIndep (Module.End.eigenspace T) := by
    first
      | exact Module.End.eigenspaces_iSupIndep T
      | exact Module.End.eigenspaces_independent T
  have hdis : Disjoint (Module.End.eigenspace T 0) ⊤ := (hind 0).mono_right htop
  have hker : LinearMap.ker T = ⊥ := by
    rw [← Module.End.eigenspace_zero]
    exact disjoint_top.mp hdis
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  exact Function.Injective.of_comp (f := D.what₂.thetaP μ j) hTinj

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

end Formalism.MainNotions.N

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBoundsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  first | exact @GlobalTheory.LinkFam.main | exact GlobalTheory.LinkFam.main | (intros; apply GlobalTheory.LinkFam.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lg1EntryOfMembership

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.NRows.AtPt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def OverNEAlt (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
def membershipLocation (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : V4.Slot := fun K X f T _ =>
  ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K X.B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
    P K X.B f T w Z Wt p0 t nch n c
abbrev WitnessAtPoint (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : Prop :=
  P K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n q.core_data_of_point
theorem lgSlotG_memSlot' {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (Q : V4.Slot) : LargeBaseConditionG KPx Q (_root_.GlobalTheory.NRows.AtPt.membershipLocation P) :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ _ _ _ _ _ _ => H kp
section
variable {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
theorem exists_wPt_entC_atWit_of_heq (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx, hP w Z _ _ _ _ _ _ x.nx.1 (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2) ⟨x.rx⟩ x.pin⟩

theorem exists_wit_pt_alt (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    {O : Obj2 (w.D Z)} (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit_of_heq hN hP (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

theorem exists_wPt_entC_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} (β : BPt K)
    (hβ : β.Is (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P))) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is β.D β.O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q :=
  positionOf_ind (P := GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (R := fun K X f T c => _root_.GlobalTheory.NRows.AtPt.membershipLocation P K X f T c →
      ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q)
    (fun _ _ _ _ _ _ _ g hP => g.1.elim fun b hb => _root_.GlobalTheory.NRows.AtPt.exists_wit_pt_alt hN H hP (b.wit g.2) hb)
    hβ.1 hβ.2 β.Y β.hY β.p
theorem memSlot_entry_of_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P)) Lk fun _ D O _ _ => r D O :=
  RowE.of_all fun _ K β _ _ _ hβ _ => let ⟨q, a, b, c⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN H β hβ; of_is a (hr K q b c)
end
theorem lg1_entry_of_atWit {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N)
    (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    Lg1 KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) fun U => RowE U Lk fun _ D O _ _ => r D O :=
  linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' h _) (_root_.GlobalTheory.NRows.AtPt.memSlot_entry_of_atWit hN H hr Lk)
end GlobalTheory.NRows.AtPt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OverNEOfNEb

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.Mem.AtPtTransport
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem overNE_of_NEb_alt {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    _root_.GlobalTheory.NRows.AtPt.OverNEAlt N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩
theorem atMem_at_wit_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := _root_.GlobalTheory.Mem.AtPtTransport.overNE_of_NEb_alt hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact _root_.GlobalTheory.NRows.AtPt.lg1_entry_of_atWit hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _
end GlobalTheory.Mem.AtPtTransport
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPin

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.NLink.Final
section Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

theorem slot_mv_extension_with_list_geo_cl (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP) :
    PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl Γ)).s := by
  intro K B f T w Z O x N h O' hO' col n
  have hrows := _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights
    K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := hrows
  obtain ⟨nch', xd', -, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, c.2, ⟨hlp⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end Slot
end GlobalTheory.NLink.Final
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkNFam

section

@[expose] public section



section
noncomputable section
namespace UpperTheory.GalC
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.NLink
def CutGivesAlt : Prop := ∀ (D : D7) (nch : NChoice D), _root_.UpperTheory.GalC.GaloisPreconditions D nch → Tie4 D →
  ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchTr c nch) ∧ Tie4 (cut D c)
theorem linkN_of_twGood_galoisPreconditions (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) {eps : ℝ} (Fm : FamP eps) (hTw : TwGood Fm)
    (hF : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.UpperTheory.GalC.GaloisPreconditions (Fm.D x i) (Fm.ex x hx i).nch ∧ Tie4 (Fm.D x i)) : LinkN Fm := by
  classical
  obtain ⟨C, CT, hC, hEx⟩ := _root_.GlobalTheory.T.exists_const_tieChi_bound_of_facts hP
  have key : ∀ x (i : Fm.Ix x), ∃ c : CutD (Fm.D x i), ∀ hx : Fm.x1 < x, c.Good ∧
      _root_.GlobalTheory.NFacts.NormChoiceFacts (cut (Fm.D x i) c) (nchTr c (Fm.ex x hx i).nch) ∧ Tie4 (cut (Fm.D x i) c) := fun x i => by
    by_cases hx : Fm.x1 < x
    · obtain ⟨c, h⟩ := hG _ _ (hF x hx i).1 (hF x hx i).2
      exact ⟨c, fun _ => h⟩
    · exact ⟨CutD.all _, fun h => absurd h hx⟩
  choose c hc using key
  have hFF : _root_.GlobalTheory.NLink.FactsFAlt (gd Fm c) C CT := fun x hx i =>
    ⟨(hc x i hx).2.1, hEx _ _ (hc x i hx).2.1 (hc x i hx).2.2⟩
  refine linkN_of_gd Fm c (fun x hx i => ⟨(hc x i hx).1, ?_, (hF x hx i).1.what₂.rank _⟩)
    (GlobalTheory.T.linkN_along_family_of_localBounds _ (_root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three hP _ C CT hC (twGood_gd Fm c hTw) hFF (_root_.UpperTheory.N.at23_family_alt hP _)))
  have p := (hF x hx i).1
  exact GlobalTheory.T.goodPointMultiplicityLeRank_proof _ _ p.Conclusion1.2.2 p.z p.adm.2.2 p.c2
theorem linkN_of_boundAtTwoThree_slot (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition)
    (hE : GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h23 : _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  exact _root_.UpperTheory.GalC.linkN_of_twGood_galoisPreconditions hP hG Fm hc.1.2 fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
theorem linkedAt_linkN_of_boundAtTwoThree (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
    (h1 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h3 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and r3, ?_⟩
  refine _root_.UpperTheory.GalC.linkN_of_boundAtTwoThree_slot hP hG _ _ ?_ ?_
  · exact GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩) e3
open Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc in
theorem final_of_alt (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (prN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hX : _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility)
    (dzs : GlobalTheory.Published.DepthZeroSupport) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
    (hF : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ nch _ _ => _root_.UpperTheory.GalC.GaloisPreconditions (w.D Z) nch)
    (hAt : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  have hW : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s :=
    GlobalTheory.T.witnesses_pass_along_set_division _ (_root_.GlobalTheory.NLink.Final.slot_mv_extension_with_list_geo_cl hL cDep anyGeometry)
  have hTf := _root_.GlobalTheory.T.tieChi_at_members_of_depthZero hX.ht prN dzs hL
  have hTr := (_root_.GlobalTheory.Mem.AtPtTransport.atMem_at_wit_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hW
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ e => ⟨e.1⟩)).2
  exact _root_.UpperTheory.GalC.linkedAt_linkN_of_boundAtTwoThree hP hG hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep)
    (hTr (fun D nch => _root_.UpperTheory.GalC.GaloisPreconditions D nch ∧ Tie4 D) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z hF hTf)) hAt
end UpperTheory.GalC
end
end
end
end
