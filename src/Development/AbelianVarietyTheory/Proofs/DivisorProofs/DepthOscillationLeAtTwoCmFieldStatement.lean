module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColengthStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColengthBoundPrimeTwo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceChart
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem mean_bound_big_factors_at_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp F vd hTP T io y h2 hy
  classical
  obtain ⟨Ch, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p h2
  obtain ⟨xs, hAF, hprod⟩ := GlobalTheory.CharDepth.colength_bound_at_two p (GlobalTheory.ChF.colength_bound_split_place_chart p)
    E H Dw l Xo c T io y Ch X hy F vd hTP
  set v2 : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hv2
  set B : ℝ := (F : ℝ) * Dw.q * (1 + vd / 2) with hB

  have hv2pos : 0 < v2 := by
    rw [hv2, NNReal.coe_pos, pos_iff_ne_zero, Ne, map_eq_zero]
    exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv2lt : v2 < 1 := by
    have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
    have hle := X.ints.map_le_one ((p : ℕ) : X.O)
    have hne : X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ≠ 1 := fun h =>
      X.nonunit.out ((X.ints.isUnit_iff_valuation_eq_one).2 h)
    rw [h2C] at hle hne
    rw [hv2]
    exact_mod_cast lt_of_le_of_ne hle hne
  have hlogv : Real.log v2 < 0 := Real.log_neg hv2pos hv2lt

  have hpos : ∀ τ, InPsi H τ → 0 < (xs τ : ℝ) := by
    intro τ hτ
    have hP : 0 < ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hv2pos _) hprod
    rcases (NNReal.coe_nonneg (xs τ)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) h.symm
      linarith
  have hle1 : ∀ τ, InPsi H τ → (xs τ : ℝ) ≤ 1 := by
    intro τ hτ
    have hne : xs τ ≠ 0 := fun h => by have := hpos τ hτ; rw [h] at this; simp at this
    exact_mod_cast (GlobalTheory.CharDepth.exists_flag_characters X.C X.v X.O X.ints _ _ _ _ _ (hAF τ hτ) hne).1
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log v2 else 0
  have hlen_pow : ∀ τ, InPsi H τ → v2 ^ len τ = (xs τ : ℝ) := by
    intro τ hτ
    simp only [len, if_pos hτ]
    rw [Real.rpow_def_of_pos hv2pos, mul_div_cancel₀ _ hlogv.ne, Real.exp_log (hpos τ hτ)]
  refine ⟨len, ?_, ?_, ?_, ?_⟩
  · intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      exact div_nonneg_of_nonpos (Real.log_nonpos (NNReal.coe_nonneg _) (hle1 τ hτ)) hlogv.le
    · simp [len, if_neg hτ]
  · intro τ hτ
    simp [len, if_neg hτ]
  · have hsum : ∑ τ, len τ = (∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)) / Real.log v2 := by
      rw [Finset.sum_div, Finset.sum_filter]
    have hlogP : Real.log (∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) =
        ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) :=
      Real.log_prod fun τ hτ => (hpos τ (Finset.mem_filter.1 hτ).2).ne'
    have hlb : B * Real.log v2 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) := by
      rw [← hlogP, ← Real.log_rpow hv2pos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hv2pos _) hprod
    rw [hsum, div_le_iff_of_neg hlogv]
    exact hlb
  · intro f k hf
    have hr : (X.v ((p : ℕ) : X.C) : ℝ) ^ len f.1 ≤ xs f.1 := (hlen_pow f.1 hf).le
    exact (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X f (xs f.1) (len f.1) (hAF f.1 hf) hr).2 k

end GlobalTheory.RefSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.mean_bound_big_factors_at_two | exact GlobalTheory.RefSum.mean_bound_big_factors_at_two | (intros; apply GlobalTheory.RefSum.mean_bound_big_factors_at_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum

theorem extendedReal_coe_finset_sum_of_real {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem oscLe_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p hp vd hvd hT
  classical
  intro la
  refine ⟨0, fun T io e ho y => ?_⟩
  have hfall : ∀ f : Lt1 Dw, letI := H.starRing
      (((0 : ℝ) : EReal) ≤ nuFac p y f (cx f) ∧ (y.IsAlg → nuFac p y f (cx f) ≤ ((boundAll p (rk f) (cx f) : ℝ) : EReal))) :=
    fun f => ((GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y)
  have hnu : letI := H.starRing; nuP p y cx = ∑ f, nuFac p y f (cx f) := rfl
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Nat.cast_zero, EReal.coe_zero] at hfall ⊢
    rw [hnu]
    exact Finset.sum_nonneg fun f _ => (hfall f).1
  · obtain ⟨len, hlen0, -, hlenS, hlen⟩ :=
      GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo E H Dw l Xo c p F vd hT T io y (not_isUnit_of_overLa la ho) hy
    set b : Lt1 Dw → ℝ := fun f => if IsBig k f then (cx f : ℝ) * len f.1 else (rk f : ℝ) * cx f with hb
    have hfb : ∀ f, letI := H.starRing; nuFac p y f (cx f) ≤ ((b f : ℝ) : EReal) := by
      intro f
      by_cases hbig : IsBig k f
      · simp only [hb, if_pos hbig]
        simpa [mul_comm] using hlen f (cx f) hbig.1
      · simp only [hb, if_neg hbig]
        have := (hfall f).2 hy
        have hB : boundAll p (rk f) (cx f) ≤ (rk f : ℝ) * cx f := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
          unfold boundAll
          exact div_le_self (by positivity) (by linarith)
        exact this.trans (EReal.coe_le_coe_iff.2 hB)
    have hsum : letI := H.starRing; nuP p y cx ≤ ((∑ f, b f : ℝ) : EReal) := by
      rw [hnu, extendedReal_coe_finset_sum_of_real]
      exact Finset.sum_le_sum fun f _ => hfb f
    refine hsum.trans (EReal.coe_le_coe_iff.2 ?_)
    have hsplit : ∑ f, b f = (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) +
        ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f := by
      simp only [hb]; rw [Finset.sum_ite]
    have hsmall : (∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f) ≤ Sm := by
      refine le_trans (le_of_eq ?_) hE.2.2.1
      unfold sumSmallSpread
      push_cast
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext f; simp [not_isBig_iff]
    have hbig : (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) ≤ F * m * (1 + vd / 2) * Mb := by
      have hfib := Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)
        (fun f => (cx f : ℝ) * len f.1)
      rw [← hfib]
      have h1 : ∀ τ : E →+* ℂ, (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
          ≤ len τ * Mb := by
        intro τ
        have hτ := hE.2.1 τ
        have : (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
            = len τ * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), (cx f : ℝ) := by
          rw [Finset.filter_filter, Finset.mul_sum]
          refine Finset.sum_congr (by ext f; simp) fun f hf => ?_
          rw [(Finset.mem_filter.1 hf).2.2, mul_comm]
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (hlen0 τ)
        rw [Nat.cast_sum] at hτ
        refine le_trans (le_of_eq ?_) hτ
        exact Finset.sum_congr (by ext f; simp) fun _ _ => rfl
      have hq : (Dw.q : ℝ) ≤ m := by exact_mod_cast hS.2.1
      calc _ ≤ ∑ τ : E →+* ℂ, len τ * Mb := Finset.sum_le_sum fun τ _ => h1 τ
        _ = (∑ τ, len τ) * Mb := by rw [Finset.sum_mul]
        _ ≤ (F * Dw.q * (1 + vd / 2)) * Mb := mul_le_mul_of_nonneg_right hlenS hE.1
        _ ≤ F * m * (1 + vd / 2) * Mb := by
          apply mul_le_mul_of_nonneg_right _ hE.1
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    simp only [Nat.cast_zero, zero_add]
    rw [hsplit]
    linarith

end GlobalTheory.RefSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.depth_oscillation_le_at_two_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  first | exact @GlobalTheory.RefSum.oscLe_two | exact GlobalTheory.RefSum.oscLe_two | (intros; apply GlobalTheory.RefSum.oscLe_two <;> assumption)
end
end
