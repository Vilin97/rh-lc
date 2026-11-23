module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLatticStatement
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLatticeStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_conjugatePlace_cmField : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  first | exact @GlobalTheory.ConjPlace.exists_conj_place | exact GlobalTheory.ConjPlace.exists_conj_place | (intros; apply GlobalTheory.ConjPlace.exists_conj_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransport

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevMov

theorem finE_mem_St_of_isMov : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  intro D V L β hβ k hk
  have h1 := GlobalTheory.LevSplit.mem_St_iff β L hβ (Lev.finE V k)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff L) (finHom V k)
  refine h1.2 (h2.1 ?_)
  have hk' : ∀ u, u ∈ hatV L ↔ ∃ u₀ ∈ hatV L, u = (finHom V k).1 *ᵥ u₀ := hk
  intro y
  constructor
  · intro hy
    exact (hk' _).2 ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨u₀, hu₀, e⟩ := (hk' _).1 hy
    have e2 : y = u₀ := by
      have := congrArg (fun z => ((finHom V k)⁻¹).1 *ᵥ z) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
      exact this
    rw [e2]; exact hu₀

end GlobalTheory.LevMov
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransportStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LevMov.finE_mem_St_of_isMov | exact GlobalTheory.LevMov.finE_mem_St_of_isMov | (intros; apply GlobalTheory.LevMov.finE_mem_St_of_isMov <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruenceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E), b ∉ PP.asIdeal → (∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | exact GlobalTheory.LevRedTriv.redFn_eq_one_of_cong | (intros; apply GlobalTheory.LevRedTriv.redFn_eq_one_of_cong <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | exact GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | (intros; apply GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianThetaLevelGroupStabilizesSelfDualLattic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevKFrame

theorem levK_frame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C Lv ΛT hsd hAA βT hfr Pg hPg hJ k κ hk
  obtain ⟨-, hmov, κ', hκ', hc⟩ := hk
  have hmovT := GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice D C.X.Λ ΛT (fmt T k) hAA hmov
  have hSt := GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport D T ΛT βT hfr k hmovT
  refine ⟨hSt, fun PP hPP => ?_⟩
  obtain ⟨PP', hPP', hcj⟩ := GlobalTheory.T.exists_conjugatePlace_cmField D PP
  have hI : ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ PP'.asIdeal := by
    rw [hPP']; exact hJ κ κ.2 κ' hκ' PP hPP
  have h1 := GlobalTheory.T.latticeTransport_congruence_of_frameVectors D C.X.Λ Lv.β Lv.𝔪 PP'.asIdeal Lv.β_mem Lv.β_span (hPP' ▸ hPg PP hPP) (fmt T k) κ' hI hmov hc
  have h2 := GlobalTheory.T.mulVec_sub_mem_latticeCompletion_of_lattice D C.X.Λ (PP'.asIdeal • C.X.Λ) (fmt T k) h1
  obtain ⟨b, hb, h3⟩ := GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice D C.X.Λ ΛT PP'.asIdeal PP'.isPrime hAA (fmt T k) h2
  have h4 := GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence D T ΛT βT hfr k hSt PP' b hb h3
  exact GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual D T ΛT hsd βT hfr k hSt PP PP' hcj h4

end GlobalTheory.LevKFrame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianThetaLevelGroupStabilizesSelfDualLatticStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianThetaLevelGroup_stabilizes_selfDualLatticeFrame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  first | exact @GlobalTheory.LevKFrame.levK_frame | exact GlobalTheory.LevKFrame.levK_frame | (intros; apply GlobalTheory.LevKFrame.levK_frame <;> assumption)
end
end
