module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEqStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClassesStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicatorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalfStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  first | exact @GlobalTheory.LiftIdeal.liftI_props | exact GlobalTheory.LiftIdeal.liftI_props | (intros; apply GlobalTheory.LiftIdeal.liftI_props <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.PairTriv

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := by
  ext i j
  rfl

theorem hatA_tens_mono {S T : HSp D} (Λ : Lt D.host.E S.rank) {L L' : Lt D.host.E T.rank} (h : L ≤ L') :
    hatA S T (tens Λ L) ≤ hatA S T (tens Λ L') := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, y, hy, rfl⟩
  refine ⟨α, hα, y, ?_, rfl⟩
  refine (AddSubgroup.closure_mono ?_) hy
  rintro z ⟨v, hv, u, hu, rfl⟩
  exact ⟨v, hv, u, h hu, rfl⟩

theorem actO_back {S T : HSp D} (k : GA D S) (x : WO S T) : actO S T k 1 (actO S T k⁻¹ 1 x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) k⁻¹ (1 : GA D T) x
  simpa using this

theorem pair_trivial : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg hodd e he a k₀ Λ' hab hmov hgen hmv Lv hLv u hu t ht
  have hsd : SelfD C.X (Lv.sh C.X.Λ) :=
    GlobalTheory.SW.Lev.selfD_idq Lv.ne_bot Lv.proper Lv.cop (GlobalTheory.SW.Lev.selfD_of_sympl C.sympl)
  have hV := GlobalTheory.SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmv
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩

  obtain ⟨ht1, ht2, ht3⟩ := ht
  have hh0 : IsHalf (cA D e) (actO S T k₀⁻¹ 1 t) := GlobalTheory.WeilVacMove.isHalf_actO _ _ _ ht1
  have hfr := hmov.2.2 _ hh0
  rw [actO_back] at hfr
  have ht0 : actO S T k₀⁻¹ 1 t ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ)) :=
    ((hgen _ hh0).2).1 ⟨hfr ▸ ht2, fun PP hPP => hfr ▸ ht3 PP hPP⟩
  rw [← hLv] at ht0
  have ht0' := hatA_tens_mono (stdL D.host.E S.rank) (GlobalTheory.SW.Lev.smul_le_idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ) ht0
  have hF := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  set t₀ := actO S T k₀⁻¹ 1 t with ht₀
  set w := actO S T k₀⁻¹ 1 u with hw₀
  have et : t = actO S T k₀ 1 t₀ := (actO_back k₀ t).symm
  have eu : GlobalTheory.LiftLevel.partAt e u = actO S T k₀ 1 (e • w) := by
    rw [partAt_eq_smul, GlobalTheory.OneMapRef.Term.actO_smul, actO_back]
  have hhalf : cA D e • t₀ = t₀ := by
    ext i j
    exact hh0 i j
  have key : symplO S T t (GlobalTheory.LiftLevel.partAt e u) = symplO S T t₀ w := by
    rw [et, eu, hF.2.2.2.2.2.2.1, (hF.2.2.2.2.2.1 t₀ (e • w) 0).2, GlobalTheory.SplitScalar.symplO_smul, hhalf,
      ← (hF.2.2.2.2.2.1 t₀ w 0).2]
  rw [key]
  exact GlobalTheory.OneMapRef.Term.char_hatA C hV hsd t₀ ht0' w hw

end GlobalTheory.LiftLevel.PairTriv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  first | exact @GlobalTheory.LiftLevel.PairTriv.pair_trivial | exact GlobalTheory.LiftLevel.PairTriv.pair_trivial | (intros; apply GlobalTheory.LiftLevel.PairTriv.pair_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.partAt_off_mem_latO | exact GlobalTheory.LiftLevel.partAt_off_mem_latO | (intros; apply GlobalTheory.LiftLevel.partAt_off_mem_latO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPointsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  first | exact @GlobalTheory.LiftLevel.partAt_mem_liftL | exact GlobalTheory.LiftLevel.partAt_mem_liftL | (intros; apply GlobalTheory.LiftLevel.partAt_mem_liftL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isFullLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsFullLattice E (stdL E n) := by
  letI := isLattice_stdL E n
  refine ⟨?_⟩
  rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2
  funext i
  exact (Pi.basisFun_apply E (Fin n) i).symm

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isFullLattice_stdL D.host.E S.rank) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hΛT)
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | exact GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | (intros; apply GlobalTheory.LiftLevel.liftL_nsmul_mem_latO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLevelDatumSumOfTranslates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem lift_level_datum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime D Pg Q e hPg h2 he
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₀, Λ', hmov, hM⟩ := GlobalTheory.T.exists_finite_unitary_mover_standard_lattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a ha
  obtain ⟨Lv, h𝔪, hw, hJ, hD2⟩ := GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ ha hmov hgen hI1 hI2 hI3 hI4
  obtain ⟨m1, hm1, hm1'⟩ := GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨m2, hm2, hm2'⟩ := GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hfin := GlobalTheory.T.finite_levelDatumClasses D S T C Lv
  refine ⟨Lv, k₀, Λ', liftL S T βS βT Pg Q e, hw, ?_, hJ, hmov.1, hM, hfin, fun x hx => hx.1,
    ⟨m1, hm1, hm1'⟩, ⟨m2, hm2, hm2'⟩,
    fun u hu => ⟨GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu, fun t ht => GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu t ht, GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu⟩,
    GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪, GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 hfin hD2⟩
  intro PP hPP
  rw [h𝔪]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hPP))

end GlobalTheory.LiftLevel

end
end
end
