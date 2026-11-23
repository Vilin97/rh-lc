module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemIsot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplitData

theorem fixed_ne_bot_of_fixed_vector_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ h hloc f hf hf0 hfix
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf L n) (g : Formalism.AUTREP.GAf L n → ℂ), NG.rt L n (a * b) g = NG.rt L n a (NG.rt L n b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf L n → ℂ, NG.rt L n 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf L n, TrivOutside {s.v} a → TrivOutside {s.v} b → TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine GlobalTheory.FixedAtSplit.fixed_ne_bot_of_fixed_vector L n π s τ hloc (NG.rt L n x⁻¹ f) ?_ ?_ ?_
  · exact π.stable _ f hf
  · intro h0
    apply hf0
    rw [← hone f, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hfix (x * κ * x⁻¹) (hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx)) (by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc n κ * h⁻¹) * h = s.loc n κ by group]
      exact hk)
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]

end GlobalTheory.RowLevelSplitData

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowDepthTrue



theorem rowDepth_rowRepR : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    GlobalTheory.HeightCounting.RowDepth D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF σ k v
  obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D k v
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF σ s
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hA⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one GlobalTheory.ConjLt.frame_mat_sub_one_lt GlobalTheory.SplitFrameW.main
      GlobalTheory.PlaceOverSplit.eq_or_eq_cP) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _ Y.stdPsi.1 hβ s
  have hh : ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ →
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧
        levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
    intro b κ hκ hk
    classical
    exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left
      Finset.subset_union_right (Y.PY.into κ) (hA κ hκ hk _)
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.RowFix.exists_fixed_rowRep D (Yc D 0) D.R.r _ R.θ Y.PY (R.MY 0) _ _ _ (Y.eFT σ)
    (fun κ => TrivOutside {s.v} κ ∧
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r))
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  exact ⟨s, τ, hs, hτ, GlobalTheory.RowLevelSplitData.fixed_ne_bot_of_fixed_vector_conj D.host.E D.R.r _ s τ h hτ f hfS hf0
    (fun κ h1 h2 => hfix κ ⟨h1, h2⟩)⟩


open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in
theorem stepW_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)



end GlobalTheory.RowDepthTrue

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowDepthTrue
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in

theorem rowDepth_allSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  intro hPr
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine (hId.and (GlobalTheory.RowDepthTrue.stepW_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x
  obtain ⟨hHo, hF, -⟩ := H.2 (w.st x.o.Z) hO
  exact rowDepth_rowRepR hPr.hc hPr.decay _ _ _ _ _ _ _ _ _ _ _ _ x.m.z.pins x.m.intersectionNumber_baseChange hHo hF
end GlobalTheory.RowDepthTrue
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.depth_of_repOf_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @_root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | exact _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | (intros; apply _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt <;> assumption)
end
end
end
end
