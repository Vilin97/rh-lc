module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelComparisonChoicesExistAtAllPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesCoverOfPrimitive

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ChoiceEx

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

theorem readsAt_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl}
    (h : ReadsAt i b w) : ReadsAt i (!b) (D.what₂.places.conj w) := fun x => by
  have h2 : IsIntegral ℤ (star ((x : ↥D.LL0) : D.what₂.LL)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) ((starRingEnd D.what₂.LL).comp (algebraMap ↥D.LL0 D.what₂.LL))
      (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
  let y : 𝓞 ↥D.LL0 := ⟨⟨_, hs x⟩, (isIntegral_algebraMap_iff ).1 h2⟩
  have hy : ((y : ↥D.LL0) : D.what₂.LL) = star ((x : ↥D.LL0) : D.what₂.LL) := rfl
  rw [sideEmb_not i b hy, D.conj_val, ← hy]
  exact h y

theorem exists_settings_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hc : ∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D w i true) :
    ∃ s : D.what₂.places.Pl → D.ntw.Tw, (∀ v, ∃ b, ReadsAt (s v) b v) ∧ ∀ v, s (D.what₂.places.conj v) = s v := by
  choose t _ ht using hc
  have hr : ∀ w, ReadsAt (t w) true w := fun w x => Formalism.L2.emb0_mem_maximalIdeal_iff_val_pos_of_sidePl D w (t w) (ht w) (x : D.LL0)
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨fun v => t (o v), fun v => ?_, fun v => by simp only [(ho v).2]⟩
  rcases (ho v).1 with h | h
  · exact ⟨true, by simpa only [h] using hr v⟩
  · have h1 := readsAt_conj hs (hr (D.what₂.places.conj v))
    rw [D.what₂.places.conj_conj] at h1
    exact ⟨_, by simpa only [h] using h1⟩

end GlobalTheory.HeightCounting.Up.ChoiceEx

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScOfSck

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem sc_of_sck_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (h : _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL) : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesCoverOfPrimitive

section

@[expose] public section



section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem stage_c_nonempty_of_published_inputs : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  fun hCo hCW hHM a b hL => _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.sc_of_sck_alt (_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM a b hL)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.stage_c_nonempty_of_prints_third_layer : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ChoiceEx.stage_c_nonempty_of_published_inputs <;> assumption)
end
end
end
end
