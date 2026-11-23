module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageLargeScaleBoundsOfLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditionsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwise

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem clusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  intro n th j hC t ht
  obtain ⟨F, sp, hF, huniq⟩ := hC
  obtain ⟨x, ⟨hxF, hxt⟩, -⟩ := huniq t ht
  obtain ⟨hthx, hspj, -, -, hbetween, hbefore⟩ := hF x hxF
  rcases hxt with rfl | rfl
  · exact Or.inl hbefore
  · by_cases hsp0 : sp x = 0
    · left
      rw [hsp0, Nat.cast_zero, add_zero]
      exact hbefore
    · right
      refine ⟨sp x, Nat.one_le_iff_ne_zero.2 hsp0, hspj, by simpa using hthx, fun k hk1 hk2 hkd => ?_⟩
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · have e : x + (sp x : ZMod n) - k = x + ((sp x - k : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [e]
        exact hbetween (sp x - k) (by omega) (by omega)
      · have e : x + (sp x : ZMod n) - k = x - ((k - sp x : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hgt.le]
          ring
        rw [e]
        exact hbefore (k - sp x) (by omega) (by omega)

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwiseStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWordMarkedClusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨ ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  first | exact @GlobalTheory.HTW.Rec.clusters_letterwise | exact GlobalTheory.HTW.Rec.clusters_letterwise | (intros; apply GlobalTheory.HTW.Rec.clusters_letterwise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | exact GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | (intros; apply GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointB_of_large : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  intro eps ez C₂ A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.HTW.roomy_of_large eps (max 100 (2 * C₂)) A heps (le_max_left _ _)
  obtain ⟨x2, h2⟩ := GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW hE hZ hA hx hadm hfont hJ i hin hrow r ρ π hPt w hw
  have hR : Roomy L (max 100 (2 * C₂)) := h1 D L Pm hE hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i :=
    h2 D L (D.nd.l i) hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L _ HW i r ρ π w hw Cx hG hR hadm hfont hJ hPt hin.1 hin.2.1 hin.2.2.1
  have hWB : WordsB L (D.nd.l i) C₂ (recWord L (liftIdx D i) ε g) := by
    refine GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime L Pm _ C₂ _ ε g _ (D.nd.l i) hR hg (le_max_right _ _) h11 hrow.1 ?_
    rw [Prod.snd_inv, orderOf_inv]
    exact hrow.lt_orderOf
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hin.ne_two hB, h11, hWB.j_lt, hWB.par, ?_⟩
  intro t ht
  exact GlobalTheory.T.cyclicWordMarkedClusters_letterwise _ _ hWB.clusters t ht

end GlobalTheory.HTW.RecS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScaleStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  first | exact @GlobalTheory.HTW.RecS.jointB_of_large | exact GlobalTheory.HTW.RecS.jointB_of_large | (intros; apply GlobalTheory.HTW.RecS.jointB_of_large <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScaleStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.inertPrimeWordConditions_of_large_scale : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  first | exact @GlobalTheory.HTW.RecS.jointCD_of_large | exact GlobalTheory.HTW.RecS.jointCD_of_large | (intros; apply GlobalTheory.HTW.RecS.jointCD_of_large <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJEpsPos

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem famJ_CLw_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by
  rw [← Fm.params_K x hx i]
  rfl

theorem famJ_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem famJ_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_ez 0 i]
  exact (Fm.L 0 i).sc.ez_pos

theorem fam_joints : ∀ {eps : ℝ} (Fm : FamP eps) (C₂ : ℝ), (∀ D : D7, LocalSituation.adm7 D) →
    (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) →
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (HW : HWOf (Fm.D x i).loc),
      LJ.ConclusionJa (Fm.D x i) → RecS.JointB (Fm.L x i) HW C₂ ∧ RecS.JointCD (Fm.L x i) HW := by
  intro eps Fm C₂ h7 hF
  obtain ⟨xB, hB⟩ := GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale eps Fm.ez C₂ (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  obtain ⟨xC, hC⟩ := GlobalTheory.T.inertPrimeWordConditions_of_large_scale eps Fm.ez (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  refine ⟨max xB xC, fun x hx h1 i HW hJ => ⟨?_, ?_⟩⟩
  · refine hB _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_left _ _).trans hx
  · refine hC _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_right _ _).trans hx

end GlobalTheory.HTW.RecS
end
end
