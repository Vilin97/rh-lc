module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersPageLargeScaleBoundsOfLargeScaleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeParametersWindowEndsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOrStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordInertDichotomyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjectionStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  first | exact @GlobalTheory.HTW.RecS.settingC_of_wordsAT | exact GlobalTheory.HTW.RecS.settingC_of_wordsAT | (intros; apply GlobalTheory.HTW.RecS.settingC_of_wordsAT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScaleStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ), L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  first | exact @GlobalTheory.InertPrimeEleven.eleven_le | exact GlobalTheory.InertPrimeEleven.eleven_le | (intros; apply GlobalTheory.InertPrimeEleven.eleven_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBounds

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem abs_szT_sub_floor_le {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) :
    |((szT P j s : ℤ) : ℝ) - ((⌊P.e j⌋ : ℤ) : ℝ)| ≤ ((R.t : ℝ) + 1) / 2 := by
  have h0 : (0 : ℤ) ≤ ((R.t : ℤ) + 1) / 2 := by omega
  have h1 : 2 * (((R.t : ℤ) + 1) / 2) ≤ (R.t : ℤ) + 1 := by omega
  have h0' : (0 : ℝ) ≤ ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : 2 * ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) ≤ (R.t : ℝ) + 1 := by exact_mod_cast h1
  unfold szT
  generalize ((R.t : ℤ) + 1) / 2 = q at h0' h1'
  cases s
  · simp only [Bool.false_eq_true, if_false, Int.cast_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [if_true, Int.cast_add]
    rw [abs_le]; constructor <;> linarith

theorem pageWord_not_thick_size : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  intro D L C j ε τ φ hR i hi
  have hnt : ¬ Thick D.host (letter τ φ i) := fun h => hi ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  have h1 := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C (letter τ φ i) j hR hnt
  have h2 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 (letter τ φ i) j hnt
  refine ⟨((⌊(hcAt D (letter τ φ i)).e j⌋ : ℤ) : ℝ), h1.1, ?_, h1.2, ?_⟩
  · exact_mod_cast h2
  · exact abs_szT_sub_floor_le _ j _

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBoundsStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  first | exact @GlobalTheory.HTW.pageWord_not_thick_size | exact GlobalTheory.HTW.pageWord_not_thick_size | (intros; apply GlobalTheory.HTW.pageWord_not_thick_size <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLeParametersPageHeightStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.sum_roundedSizes_le_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  first | exact @GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | exact GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | (intros; apply GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeight

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem WordData.Mi_add_hi_le_two_mul {n : ℕ} (W : WordData n) (hB : W.Box) (hT : W.ThickOr) (i : ZMod n) :
    W.Mi i + W.hi i ≤ 2 * (W.b + W.η + W.S) := by
  obtain ⟨-, -, hw, -, -, -⟩ := hB
  have hs : W.sz i ≤ (W.b : ℤ) + W.η := by
    rcases hT i with h | h
    · exact h.2
    · omega
  unfold WordData.Mi WordData.hi
  split_ifs <;> omega

theorem pageWord_Mi_add_hi_le {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG)
    (hR : Roomy L C) (i : ZMod (orderOf φ)) :
    (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  have h1 := WordData.Mi_add_hi_le_two_mul _ (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR) (GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ φ hR) i
  have h2 := GlobalTheory.T.sum_roundedSizes_le_height L C hR
  have h3 : (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ)
      ≤ ((2 * (bHat L + etaHat L + sHat L) : ℕ) : ℝ) := Nat.cast_le.mpr h1
  refine h3.trans ?_
  push_cast
  linarith

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  first | exact @GlobalTheory.HTW.pageWord_Mi_add_hi_le | exact GlobalTheory.HTW.pageWord_Mi_add_hi_le | (intros; apply GlobalTheory.HTW.pageWord_Mi_add_hi_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizes

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordBox : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := funext fun a => hg a
  rw [hgl]
  have hb := GlobalTheory.HTW.bHat_window L C hR
  refine ⟨?_, ?_, hb.1, hb.2⟩
  · intro a
    obtain ⟨-, hM, hh, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    rw [hM, hh]
    exact GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a
  · intro a hnt
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    obtain ⟨s, hs1, hs2, -, hs3⟩ := GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))
    refine ⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩
    have hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ) := by
      rw [← hsz]; push_cast; rfl
    rw [hc]; exact hs3

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizesStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_boxesAndSizes : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordBox | exact GlobalTheory.HTW.Rec.recWord_wordBox | (intros; apply GlobalTheory.HTW.Rec.recWord_wordBox <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointCD_of_large : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  intro eps ez A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW he hZ hA hx hadm hfont hja i hin r ρ π hpt w hw
  have hR : Roomy L 100 := h1 D L Pm he hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i := h2 D L _ hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  have hn2 := hin.ne_two
  have hj := hin.2.2.2
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L 100 HW i r ρ π w hw Cx hG hR hadm hfont hja hpt hin.1 hin.2.1 hin.2.2.1
  have hs := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D (D.nd.l i) hin.1 hin.2.1 hin.2.2.1).2
  have hm : (DV.frobG D (D.nd.l i)).1.2 = -1 := by
    refine (Int.units_eq_one_or _).resolve_left fun h => hj ?_
    rw [← hs, h]; rfl
  have hm' : ((DV.frobG D (D.nd.l i))⁻¹).1.2 = -1 := by
    change ((DV.frobG D (D.nd.l i)).1.2)⁻¹ = -1
    rw [hm]; rfl
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hn2 hB, h11,
    GlobalTheory.T.twistedDualSizeWord_boxesAndSizes L 100 _ ε g _ hR hg, ?_⟩
  rcases GlobalTheory.T.twistedDualSizeWord_inert_dichotomy L 100 _ ε g _ _ hR hg h11 hm' with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd, GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection L HW i r ρ π w hw Cx hG _ d h11 hB hd⟩

end GlobalTheory.HTW.RecS
end
end
