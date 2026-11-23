module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBoxStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumpsStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeParametersWindowEndsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOrStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbitStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem good_conjugates_mem : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (s : ℕ),
    Loc.Good K s LL → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1 := by
  intro l _ K LL s h τ x
  unfold Loc.Good at h
  obtain ⟨-, -, hle, hall⟩ := h

  let σ := τ.liftNormal (Loc.Om l)
  have hσ : σ (algebraMap K.1 (Loc.Om l) x) = τ x := by
    rw [AlgHom.liftNormal_commutes]
    rfl
  have hx := hall ((σ : Loc.Om l →ₐ[ℚ_[l]] Loc.Om l).comp (Loc.Ks K s).val) ⟨x, hle x.2⟩
  rw [← hσ]
  exact hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWord

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_of_isSubOfSums : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hJ hRd T hT
  have hO := GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL
  have hW := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR
  have hjump : ∀ a τ, Over W τ a →
      JumpsInV (P.PD K) T.ρ τ {u | u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))} := fun a τ hτ =>
    GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) T.ρ Ms τ _ hT
      (fun x => hJ.jumps x τ (g a) (hRd τ a hτ))
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.CrysSub.isCrys_of_isSubOfSums (P.PD K) hF hO (GRep.ofLat T) Ms hJ.cont hT hJ.crys
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).1
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).2

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWordStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.fits_of_isSubOfSums | exact GlobalTheory.HTW.Rec.fits_of_isSubOfSums | (intros; apply GlobalTheory.HTW.Rec.fits_of_isSubOfSums <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertiaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), Br.DegW nbr i w hw := by
  first | exact @GlobalTheory.bridge_degW | exact GlobalTheory.bridge_degW | (intros; apply GlobalTheory.bridge_degW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageWordSEtaM

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_S_eta_m : ∀ {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), ((pageWord L j ε τ φ).S : ℝ) ≤ L.Sc ∧ ((pageWord L j ε τ φ).η : ℝ) ≤ L.etaSz + D.R.t + 2 ∧ (pageWord L j ε τ φ).m = D.R.m := by
  intro D L j ε τ φ
  refine ⟨?_, ?_, rfl⟩
  · exact Nat.floor_le L.Sc_pos.le
  · have h := Nat.floor_le L.etaSz_pos.le
    show ((⌊L.etaSz⌋₊ + D.R.t + 2 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordParams

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordNum : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨rfl, hg⟩ := hO
  generalize g 0 = τ at hg
  obtain rfl : g = letter τ ψ := funext hg
  have hsm := pageWord_S_eta_m L j ε τ ψ
  refine ⟨?_, ?_, ?_, hsm.1, hsm.2.1, rfl⟩
  · intro a
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a
    rcases GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ ψ hR a with h | h
    · exact Or.inl (hth.2 h)
    · refine Or.inr ?_
      have h' : (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) ≤ ((wHat D : ℕ) : ℤ) := by
        rw [hsz]; exact h
      exact_mod_cast h'
  · have h := bHat_add_etaHat_add_sHat_le_hPage L C hR
    exact h
  · exact (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).2

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordParametersNumbersStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wordNum_recWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordNum | exact GlobalTheory.HTW.Rec.recWord_wordNum | (intros; apply GlobalTheory.HTW.Rec.recWord_wordNum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbit

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia D.nbr i w hw, ?_, GlobalTheory.T.wordNum_recWord L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbitStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordBase_of_jumpIn | exact GlobalTheory.HTW.Rec.wordBase_of_jumpIn | (intros; apply GlobalTheory.HTW.Rec.wordBase_of_jumpIn <;> assumption)
end
end
