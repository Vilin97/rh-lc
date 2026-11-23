module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelChoiceMuUnramifiedOutsideTypePlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlaceUnram

open GlobalTheory.IdemSupport GlobalTheory.LevelPlaces GlobalTheory.SplitOffPlaces

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem unramOutside_mu0_of_splitSet : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → SplitSet L.Pg → ∀ j : Fin D.R.m, UnramOutside (L.mu0 ((j : ℕ) + 1)) L.Pg := by
  intro D T0 L μ0 hL hS j x hinf h1 h2 hx
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hk : ∀ PP ∈ L.Pg, idemAt PP * idem L.Pg = idemAt PP := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hS.isIdemAt ha).1) (fun a ha b hb hab => hS.mul_eq_zero ha hb hab) hl
  have hc0 : ∀ PP ∈ L.Pg, idemAt PP * cA D (idem L.Pg) = 0 := fun PP hPP => by

    rw [idem, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => hS.mul_conj hPP hi
  have hc1 : ∀ PP ∈ L.Pg, cA D (idemAt PP) * idem L.Pg = 0 := fun PP hPP => by
    rw [idem, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact hS.mul_conj hi hPP
  have hx1 : ∀ PP ∈ L.Pg, Φ (x : AE D) PP = 1 ∧ Φ (x : AE D) (cP PP) = 1 := fun PP hPP => by
    have hd := delta_of_isIdemAt hΦ (hS.isIdemAt hPP)
    have hd' := delta_conj hΦ hd
    have a : idemAt PP * (x : AE D) = idemAt PP := by
      have e : idemAt PP * (idem L.Pg + cA D (idem L.Pg)) = idemAt PP := by rw [mul_add, hk PP hPP, hc0 PP hPP, add_zero]
      calc idemAt PP * (x : AE D) = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = idemAt PP := e
    have b : cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) := by
      have e : cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) = cA D (idemAt PP) := by
        rw [mul_add, hc1 PP hPP, zero_add, ← map_mul, hk PP hPP]
      calc cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = cA D (idemAt PP) := e
    constructor
    · have h := congrArg (fun z => Φ z PP) a
      rwa [ev_mul, hd.2.1, one_mul] at h
    · have h := congrArg (fun z => Φ z (cP PP)) b
      rwa [ev_mul, hd'.2.1, one_mul] at h
  have hg : ∀ k, (D.host.g k : D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  set m : ℕ := D.host.g 0 * D.host.g 1 with hmdef
  have hm0 : (m : D.host.E) ≠ 0 := by rw [hmdef, Nat.cast_mul]; exact mul_ne_zero (hg 0) (hg 1)
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → (L.C.mu0 j).UnrAt P :=
    fun P hP => (L.C.isMu0 j).unr P fun k hk => hP (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
      rw [hmdef, Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk'
      · exact Ideal.mul_mem_left _ _ hk')
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ (L.C.mu0 j) (hL.mu0 j) (L.C.isMu0 j).tame m hunr x ⟨hinf, h1, h2⟩
    ⟨finPart D (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · have e : Φ (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)) Q =
        (Φ (x : AE D) Q - 1) * algebraMap D.host.E (Q.adicCompletion D.host.E) ((m : D.host.E)⁻¹) := by
      rw [ev_mul, hΦ.inc, map_sub, map_one]
      rfl
    rw [e]
    by_cases hQ : (m : 𝓞 D.host.E) ∈ Q.asIdeal
    · have hq : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
        rw [hmdef, Nat.cast_mul] at hQ
        rcases Q.isPrime.mem_or_mem hQ with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨k, hk⟩ := hq
      have h1Q : Φ (x : AE D) Q = 1 := by
        rcases div_or_div_conj L.C.P k Q hk with h | h
        · exact (hx1 Q ((hL.Pg Q).2 ⟨k, h⟩)).1
        · have e2 : conjSpec Q = cP Q := (isConjPl_iff _ _).1 (isConjPl_conjSpec Q)
          rw [e2] at h
          have := (hx1 (cP Q) ((hL.Pg _).2 ⟨k, h⟩)).2
          rwa [cP_cP] at this
      rw [h1Q, sub_self, zero_mul]
      exact zero_mem _
    · refine mul_mem (sub_mem ((hΦ.int _).1 h1 Q) (one_mem _)) ?_
      have hm' : (m : 𝓞 D.host.E) ≠ 0 := fun h => hm0 (by exact_mod_cast congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h)
      have := (inv_mem_iff Q hm').2 hQ
      simpa using this
  · rw [nsmul_eq_mul, ← map_natCast (finPart D) m, ← map_mul, ← map_natCast (incA D) m, ← mul_assoc, mul_comm _ ((x : AE D) - 1),
      mul_assoc, ← map_mul, mul_inv_cancel₀ hm0, map_one, mul_one, map_sub, map_one]

end GlobalTheory.TypePlaceUnram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelChoiceMuUnramifiedOutsideTypePlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelChoice_mu_unramified_outside_type_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → SplitSet L.Pg → ∀ j : Fin D.R.m, UnramOutside (L.mu0 ((j : ℕ) + 1)) L.Pg := by
  first | exact @GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet | exact GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet | (intros; apply GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramified

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add (f := _), map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add (f := _), map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add (f := _), map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramifiedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  first | exact @GlobalTheory.ConjTwist.isResAt_one_of_unram | exact GlobalTheory.ConjTwist.isResAt_one_of_unram | (intros; apply GlobalTheory.ConjTwist.isResAt_one_of_unram <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwist

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.BaseGood

theorem base_good : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j F hF de hde hpl
  have hL := hC.lev
  have hS : SplitSet Rl.Pg := by
    obtain ⟨P, h1, -, hP⟩ := hpl.split
    exact hP.mono h1
  have hr : Odd D.R.r := Formalism.L2.NTheta.odd_r D.R
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨Pa, hPa1, hPa2, hPa⟩ := hpl.split
  refine ⟨GlobalTheory.ConjTwist.liftWeight D j, fun PP => GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹,
    fun _ => rfl, fun _ => rfl, fun P => ?_⟩
  exact
    { even := rV ▸ hr.add_odd D.R.t_odd
      odd := rW ▸ hr
      frame := hF
      de := hde
      places := hpl
      wt := GlobalTheory.ConjTwist.liftWeight_good D j
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq D Rl.C Rl.eta hL.eta (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
      hecke := (hL.mu0 j).1
      real := GlobalTheory.GridWeil.triv_base (hL.mu0 j) (Rl.C.isMu0 j).triv
      unram := GlobalTheory.T.levelChoice_mu_unramified_outside_type_places D _ _ _ hL hS j
      tame := fun PP hPP x hx hi u hu => by
        have e1 := GlobalTheory.ConjTwist.eq_res_of_chrEq (hL.mu0 j) (hS.isIdemAt hPP) ((Rl.C.isMu0 j).tame PP) (hL.chi j PP hPP) x hx hi u hu
        have e2 := GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified D Circle de.chi de.Q Pa hde.unram hPa hPa2 PP (hPa1 hPP)
          (Finset.disjoint_left.1 hpl.disj hPP) x hx hi u hu
        show Rl.mu0 ((j : ℕ) + 1) x * de.chi x = GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹ u
        rw [e2, MonoidHom.one_apply, mul_one]
        exact Circle.ext e1
      inf := fun τ => by
        have e : ((GlobalTheory.ConjTwist.liftWeight D j).c τ : ℚ) - (((GlobalTheory.ConjTwist.liftWeight D j).p τ : ℚ) -
            (GlobalTheory.ConjTwist.liftWeight D j).q τ) / 2 + 1 / 2 = -(D.hc τ).e j := by
          have h := GlobalTheory.ConjTwist.liftC_cast D j τ
          simp only [GlobalTheory.ConjTwist.liftWeight]
          linarith
        rw [e]
        exact GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ }

end GlobalTheory.SeriesTie.BaseGood

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwistStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftBaseData_isGood_twist : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  first | exact @GlobalTheory.SeriesTie.BaseGood.base_good | exact GlobalTheory.SeriesTie.BaseGood.base_good | (intros; apply GlobalTheory.SeriesTie.BaseGood.base_good <;> assumption)
end
end
