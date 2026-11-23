module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImagesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpan
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedData

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.goodForms_lift_baseLevel_extension_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        z'.R.toRealDat.WL z'.F.lv2 false j' = Submodule.span (w'.st Z').toD7.what₂.LL {x' | ∃ x ∈ z.R.toRealDat.WL z.F.lv2 false j, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  first | exact @GlobalTheory.Mem.R3.Rw.goodForms_lift_bc | exact GlobalTheory.Mem.R3.Rw.goodForms_lift_bc | (intros; apply GlobalTheory.Mem.R3.Rw.goodForms_lift_bc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.reading_coordinatewiseImage_eq_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  first | exact @GlobalTheory.Mem.R3.LiftRead.read_ext | exact GlobalTheory.Mem.R3.LiftRead.read_ext | (intros; apply GlobalTheory.Mem.R3.LiftRead.read_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeA

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms



theorem extendedData_liftFormsLattice_baseLevel_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and (StepW.and (GlobalTheory.T.goodForms_lift_baseLevel_extension_span h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.extendedData_lift_baseLattice_eq_span_images h1 h2 h3 h4 h5 h6 h7)) (GlobalTheory.T.reading_coordinatewiseImage_eq_extendedData h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, ⟨H1, H2⟩, H3⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hM := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hJ := H3 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  obtain ⟨G, hGb, hGid⟩ := GlobalTheory.Mem.R3.LiftForms.exists_mat φ hn _ _ hW
  refine ⟨G, hGb, ?_, ?_⟩
  · exact GlobalTheory.Mem.R3.LiftForms.lat_coords φ hn _ _
      ((Module.finBasis _ _).linearIndependent.map' _ (Submodule.ker_subtype _)) G hGid _
      (fun x hx => GlobalTheory.Mem.R3.LiftForms.mem_span_basis _ ((z.R.FW j).Mj_sub_Wgood _ _ _ hx)) _ hM
  · intro y
    exact HEq.trans (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z'.R z'.F j' _)
      (HEq.trans (hJ _ _ (hGid y)) (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z.R z.F j y).symm)

end GlobalTheory.Mem.R3.LiftForms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeAStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  first | exact @GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | exact GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | (intros; apply GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange <;> assumption)
end
end
