module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentSupportPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeedsStatement
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBelowOfRange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw

end GlobalTheory.Mem.R3.Rw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLtGrpTrue

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem exists_lt_grpTrue (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (hX : B.fields.Ok) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) := by
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  obtain ⟨kb, ks, hk⟩ := GlobalTheory.Mem.Df.Model.exists_ka B
  let W' : RowsRest B w.C :=
    { R.W with
      eOp := fun _ => 0
      eOp_idem := fun _ => LinearMap.comp_zero _
      eOp_sa := fun _ => LinearMap.IsSymmetric.zero
      kaBig := kb
      kaSmall := ks }
  obtain ⟨V, -⟩ := GlobalTheory.Mem.DivModel.exists_divStage B w.C W'
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C W' G.cd hO (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l hX)
    (show R.W.Drows ≤ R.W.Dall by rw [R.std.drows, R.std.dall])
  have hMt : ∀ (μ : w.C.Tup) (j : ℕ), W'.eMt μ j = 0 := fun μ j => by
    haveI := R.std.mt μ j
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.Mem.Top.exists_nStage_grpTrue hG B w.C W' R.std.sha (fun j v _ _ => R.std.eta j v)
    (fun _ => rfl) hMt f
  refine ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN),
    hk w.C W' rfl rfl V S N G⟩

end GlobalTheory.Mem.R3.Rw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff ).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.placesOverFixedField_same_coefficient_place : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  first | exact @GlobalTheory.Mem.Top.Bl.below_of_overOne | exact GlobalTheory.Mem.Top.Bl.below_of_overOne | (intros; apply GlobalTheory.Mem.Top.Bl.below_of_overOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharEqOfOverOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.UntwSat

theorem stepW_seed_fixed : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      (∃ F₀, SeedW K B.toPre f B.KsC F₀ px Set.univ ⊤) → ∃ F₀, SeedW K B.toPre f B.KsC F₀ px ↑T.pl B.fixedCoefficientFieldInComplex := by
  refine evG_all fun K => ?_
  choose S S₁ hS using GlobalTheory.T.exists_uniform_normalisedAdelicSeeds K
  refine ⟨fun P f F => S₁ P f F, fun P f F _ => S P f F ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun _ _ _ _ _ => ∅, fun P f F => (hS P f F).1, by simp, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => ?_⟩
  obtain ⟨F₀, h⟩ := (hS _ _ _).2 px hs
  refine ⟨F₀, h.mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.1 z hz

theorem isBaseEnlargementFixedCoefField_of_same_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hLL : B₀.LLC ≤ B.fixedCoefficientFieldInComplex) : Enl0 B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, -, rfl⟩
    exact (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (B.fixedField_le_coefficientField (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩)))

theorem dat_saturated_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧
        DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧
        (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧
        ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep).and stepW_seed_fixed).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨F₀, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, -, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ :=
    hsd w.px ⟨_, hs⟩
  have hE : Enl0 B₀ B := isBaseEnlargementFixedCoefField_of_same_fields hB₀ hKs hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  have hsub : ∀ x : (w₀.D Z₀).what₂.LL, ∃ y ∈ (w.D Z).LL0, (w.D Z).what₂.embLL y = (w₀.D Z₀).what₂.embLL x :=
    fun x => (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine', ?_, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl
  · intro v₁ v₂ hov hv₁
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).1 hv₁ with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v₁
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v₁ hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).2 (Or.inl h))
      have hB₂ := GlobalTheory.T.placesOverFixedField_same_coefficient_place (w₀.D Z₀) (w.D Z) hsub v v₁ v₂ hov hB
      have hv₂ := (hExt.W1 v v₂ hB₂).1 hv
      rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).1 hv₂ with h₂ | h₂
      · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inl h₂)
      · obtain ⟨j, y, -, hne⟩ := h₂
        exact absurd rfl hne
    · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inr (GlobalTheory.Mem.SatForced.mem_W1F_of_overOne K (w.D Z) v₁ v₂ hov h))

end GlobalTheory.Mem.R3.Rw.UntwSat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | exact GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | (intros; apply GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw <;> assumption)
end
end
