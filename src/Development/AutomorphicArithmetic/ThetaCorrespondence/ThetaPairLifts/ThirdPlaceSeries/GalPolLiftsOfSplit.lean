module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepUniform

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
theorem exists_rep_uniform_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
          IsFrob (F := D.host.E) B (normV w) σ →
          ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
            galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
  have := host_isCMField D.host
  have hr' : (C.e a π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := _root_.UpperTheory.GalS.exists_aw_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'
  refine ⟨r, h1, fun w hl hu B σ hB hσ => ?_⟩
  have hu' := (D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    have hu2 := (T.unr w _).1 hu'
    rw [T.tw, C.loc] at hu2 ⊢
    exact ((h3 w hl _ _).eq_unr hu2).symm
  rw [galPol, T.frobEig w _ hu', e]
  exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ
end GlobalTheory.GalAllPlaces
end
section
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalPolLiftsOfSplit

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem galPol_lpTw_mem_lifts_eventually : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → ∀ (K : Type) [Field K] (e : K →+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e := by
  intro hL hF hG hCh D T C K _ e π hc hr hsplit
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] :=
    fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP
  have hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w) :=
    (eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)
  obtain ⟨ρ, hρc, hρ⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 ι ha π hc hr
  letI : Algebra K ℂ := e.toAlgebra
  have key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) →
      (P w).map (γ : ℂ →+* ℂ) = P w := by
    intro γ
    obtain ⟨ρ', hρ'c, hρ'⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr
    have hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w :=
      hsplit.mono fun w hw hs => by
        obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 (hw hs)
        simp only [hP]
        rw [← hq, Polynomial.map_map]
        congr 1
        ext x
        exact γ.commutes x
    have hall := hU.and hfix
    rw [Filter.eventually_cofinite] at hall
    set S := hall.toFinset with hS
    have hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map
        (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ)) := by
      intro g
      rw [Polynomial.map_map]
      rfl
    have heq := GlobalTheory.charpoly_eq_of_eqOn_dense
      (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)))
      (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _
      (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by
        rintro g ⟨w, hwS, hsp, B, hB, hFr⟩
        have hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧
            (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w) := by
          by_contra h
          exact hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)
        apply Polynomial.map_injective ι.toRingHom ι.injective
        rw [hρ w hw.1.1 hw.1.2 B g hB hFr]
        apply Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective
        rw [← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])
    intro w hw
    obtain ⟨σ, hσ⟩ := exists_isFrob (D.nd.plOm.2 w)
    have h1 := hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    have h2 := hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    rw [hmap, ← heq σ, h1] at h2
    exact h2
  filter_upwards [hU] with w hw
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)
    simpa [Polynomial.coeff_map] using this
end GlobalTheory.GalAllPlaces
end
end
end
end
