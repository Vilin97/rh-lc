module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
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
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMuStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.auxiliary_place_not_dvd_different_base_field : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc), ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DifferentAtBasePlace.not_dvd_different | exact GlobalTheory.DifferentAtBasePlace.not_dvd_different | (intros; apply GlobalTheory.DifferentAtBasePlace.not_dvd_different <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedIdeleBasePlace

theorem ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 →
      ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hL t v e he hv i j hU
  subst hv
  have hw : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ G.pl.v0 e he hU _ hw
  exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j
    ((GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) _).1 h1)

end GlobalTheory.RamifiedIdeleBasePlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceIdStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | exact GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | (intros; apply GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.large_place_not_dvd_different : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DiffSOne.not_dvd_differentIdeal | exact GlobalTheory.DiffSOne.not_dvd_differentIdeal | (intros; apply GlobalTheory.DiffSOne.not_dvd_differentIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtSmallPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 →
      ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ _ _ v ε hε hv hns
  obtain ⟨e, he⟩ := G.pl.w_split v hv
  have hb := Formalism.IndefR.Fin.below_of_idemAt he
  have hbv : Formalism.IndefR.Fin.belowPl (G.pl.w v) = v := by
    refine HeightOneSpectrum.ext ?_
    have a := congrArg HeightOneSpectrum.asIdeal (G.pl.under_w hv)
    rw [← a]
    rfl
  rw [hbv] at hb
  refine hns.2 ⟨e, he.1, ?_⟩
  rw [hb, Formalism.IndefR.Fin.placeIdem_eq hε]
  rfl

end GlobalTheory.SplitAtSmallPlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.small_place_not_nonsplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | exact GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTwistPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ hμ t v e he PP hPP hv hns
  obtain ⟨f, hf⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt ((hμ.Q_pl t PP hPP).2 PP hPP)
  exact GlobalTheory.AdTh.RecPair.under_ne hf hns hv

end GlobalTheory.SplitTwistPlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_place_under_not_nonSplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitTwistPlaces.not_nonSplitAt | exact GlobalTheory.SplitTwistPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitTwistPlaces.not_nonSplitAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRam

open GlobalTheory.WeilParts

variable {D : D7}

theorem unramAt_mul {e : AF D.host.F} {a b : (AE D)ˣ →* Circle} (ha : UnramAt e a) (hb : UnramAt e b) : UnramAt e (a * b) := by
  intro x h1 h2 h3
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem unramAt_pow {e : AF D.host.F} {a : (AE D)ˣ →* Circle} (ha : UnramAt e a) (n : ℕ) : UnramAt e (a ^ n) := by
  intro x h1 h2 h3
  rw [MonoidHom.pow_apply, ha x h1 h2 h3, one_pow]

theorem bottom_ram : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hr T Lc μ₀ hμ G => ?_⟩⟩
  intro W i j A A' WW X _ t v e he
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    rw [mul_div_mul_right_eq_div]
    rcases hS with hS | ⟨PP, hPP, hPv⟩
    · refine ⟨GlobalTheory.T.small_place_not_nonsplit G μ₀ hμ t v e he hS, ?_, ?_⟩
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · subst h0; exact GlobalTheory.T.auxiliary_place_not_dvd_different_base_field G
        · exact GlobalTheory.T.large_place_not_dvd_different large₂ hr v h1
    · refine ⟨GlobalTheory.T.twist_place_under_not_nonSplit G μ₀ hμ t v e he PP hPP hPv, ?_, hPv ▸ GlobalTheory.T.twist_place_under_not_dvd_differentIdeal Lc μ₀ hμ t PP hPP⟩
      by_cases h0 : v ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h0 with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · exact GlobalTheory.T.square_mu_div_chi_ramified_at_twist_place G μ₀ hμ t v e he h0 PP hPP hPv i j
  · left
    push_neg at hS
    obtain ⟨h1, h2⟩ := GlobalTheory.T.grid_characters_unramified G μ₀ hμ t v e he hS.1 i
    exact ⟨unramAt_mul (GlobalTheory.T.level_character_unramified_mu G μ₀ hμ t v e he hS.1 hS.2 j) (unramAt_pow h2 _), unramAt_mul h1 (unramAt_pow h2 _)⟩

end GlobalTheory.BotRam

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.BotRam.bottom_ram | exact GlobalTheory.BotRam.bottom_ram | (intros; apply GlobalTheory.BotRam.bottom_ram <;> assumption)
end
end
