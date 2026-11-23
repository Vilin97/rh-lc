module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLcCutPointOfNotLcOtherStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallAmpleThroughOffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LcCutTwoClosedPointsOneCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtOfIsNkltCentre
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotLcAtAddOfIsNkltCentre

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_lcAt_add_of_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  intro X _ _ _ p n hp hn Γ A z x hN hA hoff hzx hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hlcz := ((GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Γ + A) x z hzx).2 hlc)
  obtain ⟨E, η, m, g, hη, hm, hlog, hC, hd⟩ := hN
  obtain ⟨m₀, D₀, hm₀, hEff, rfl⟩ := hA
  obtain ⟨m', f, hm', hreg, heq⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p (qWeil D₀ m₀) ⟨m₀, D₀, hm₀, hEff, rfl⟩ z
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ :=
    GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Γ (qWeil D₀ m₀) η z m m' g f 1 hm hm' hlog heq
  rw [one_smul] at hlog''
  have h1 := ((GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Γ + qWeil D₀ m₀) η z m'' g'' hη hm'' hlog'').1 hlcz) E hC.1
  rw [hdisc E, one_mul] at h1
  have hf0 : 0 ≤ E.ord f := (E.ord_nonneg_iff f).2 (hC.1 _ hreg)
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have hfle : (E.ord f : ℚ) / m' ≤ 0 := by linarith
  have hfle' : (E.ord f : ℚ) ≤ 0 := by
    rwa [div_le_iff₀ hm'q, zero_mul] at hfle
  have hord : E.ord f = 0 := by
    have : E.ord f ≤ 0 := by exact_mod_cast hfle'
    omega
  have hreg' := hC.2 f hreg hord
  apply hoff
  intro w hw
  by_cases hc : Order.coheight w = 1
  · obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
    rw [heq w hw F hF]
    have a : 0 ≤ F.ord f :=
      (F.ord_nonneg_iff f).2 ((hF _).2 (regAt_of_specializes hw hreg))
    have b : 0 ≤ F.ord f⁻¹ :=
      (F.ord_nonneg_iff _).2 ((hF _).2 (regAt_of_specializes hw hreg'))
    rw [F.ord_inv] at b
    have : F.ord f = 0 := by omega
    simp [this]
  · have : D₀.mult w = 0 := by
      by_contra h
      exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    simp [qWeil, this]

end GlobalTheory.PairStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotLcAtAddOfIsNkltCentreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.not_lcAt_add_of_isNkltCentre' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  first | exact @GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | exact GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | (intros; apply GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonical

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_closedPt_le_zero {X : Scheme.{0}} {x : X}
    (hx : IsClosed ({x} : Set X)) : topologicalKrullDim (closure ({x} : Set X)) ≤ 0 := by
  have hsing : ∀ a b : closure ({x} : Set X), a = b := by
    intro a b
    apply Subtype.ext
    have ha : (a : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset a.2)
    have hb : (b : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset b.2)
    rw [ha, hb]
  have hirr : ∀ s t : IrreducibleCloseds (closure ({x} : Set X)), s = t := by
    intro s t
    apply SetLike.ext
    intro a
    obtain ⟨b, hb⟩ := s.isIrreducible.nonempty
    obtain ⟨c, hc⟩ := t.isIrreducible.nonempty
    constructor
    · intro _
      rw [hsing a c]
      exact hc
    · intro _
      rw [hsing a b]
      exact hb
  unfold topologicalKrullDim
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro s t _
  rw [hirr t s]

theorem eq_of_closedPt_specializes {X : Scheme.{0}} {x y : X} (hx : IsClosed ({x} : Set X))
    (h : x ⤳ y) : y = x := by
  exact Set.mem_singleton_iff.mp (hx.closure_subset (specializes_iff_mem_closure.mp h))

private lemma two_mul_lt_pow_mul_of_le (a t t' c : ℚ) (k : ℕ) (ha : 0 ≤ a) (ht : 0 < t) (htt : t ≤ t')
    (h : 2 * a < t ^ k * c) : 2 * a < t' ^ k * c ∧ a < t' ^ k * c := by
  have htk : 0 < t ^ k := pow_pos ht k
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    have : t ^ k * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htk.le hc
    linarith
  have hpow : t ^ k ≤ t' ^ k := by
    first
    | exact pow_le_pow_left ht.le htt k
    | exact pow_le_pow_left₀ ht.le htt k
  have : t ^ k * c ≤ t' ^ k * c := mul_le_mul_of_nonneg_right hpow hc.le
  constructor <;> linarith

theorem twoPoint_step : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d ε : ℚ) (h : ℕ → ℚ) (x x' : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → x ≠ x' → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x ∨ z ⤳ x' → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → QNum p N d D → 0 ≤ d → LcCut p n (Δ + D) x j → ¬ KltAt p n (Δ + D) x' → LcCut p n (Δ + D) x 0 ∨ ∃ (i : ℕ) (D' : X → ℚ) (d' : ℚ), i < j ∧ 0 ≤ d' ∧ d' ≤ d + (h (i + 1) + ε) ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x i ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' i ∧ ¬ KltAt p n (Δ + D') x)) := by
  intro hP hNV hNef X _ _ _ p n hp hn Δ m G N D d ε h x x' j hΔ hklt hm hG hN hx hx' hxx' hpos hbig
    hε hD hd hcut hnk
  obtain ⟨hlcx, hnkx, hdim⟩ := hcut
  by_cases h0 : LcCut p n (Δ + D) x 0
  · exact Or.inl h0
  right

  have hex : ∃ z, z ⤳ x ∧ ¬ KltAt p n (Δ + D) z ∧
      ¬ topologicalKrullDim (closure ({z} : Set X)) ≤ 0 := by
    by_contra hne
    push_neg at hne
    apply h0
    unfold LcCut
    refine ⟨hlcx, hnkx, fun z hz hkz => ?_⟩
    have := hne z hz hkz
    simpa using this
  obtain ⟨z, hzx, hkz, hz0⟩ := hex
  have hzne : z ≠ x := by
    rintro rfl
    exact hz0 (topologicalKrullDim_closure_closedPt_le_zero hx)
  have hDq : IsQCart D := hD.isQCart

  obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hp hn Δ D z hDq (hklt z) hkz
  have hwx : w ⤳ x := hwz.trans hzx
  have hwne : w ≠ x := by
    rintro rfl
    exact hzne (eq_of_closedPt_specializes hx hwz)
  obtain ⟨e, -, hdw, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n w hn
  have he1' : 1 ≤ e := he1 x hwx hwne.symm
  have hkw : ¬ KltAt p n (Δ + D) w :=
    not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w w hw (specializes_refl w)
  have hej : e ≤ j := by
    have hle := hdim w hwx hkw
    rw [hdw] at hle
    exact_mod_cast hle
  obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
  have hwN := hbig w (i + 1) (Or.inl hwx) he1' hdw
  by_cases hlx' : LcAt p n (Δ + D) x'
  ·
    obtain ⟨w', hw'x', hw'⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hp hn Δ D x' hDq (hklt x') hnk
    by_cases hw'x : w' ⤳ x
    ·
      have hkw' : ¬ KltAt p n (Δ + D) w' :=
        not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w' w' hw' (specializes_refl w')
      obtain ⟨e', -, hdw', he1''⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n w' hn
      have h1e' : 1 ≤ e' := by
        by_cases hxw : x = w'
        · refine he1'' x' hw'x' ?_
          intro h2
          exact hxx' (hxw.trans h2.symm)
        · exact he1'' x hw'x hxw
      have he'j : e' ≤ j := by
        have hle := hdim w' hw'x hkw'
        rw [hdw'] at hle
        exact_mod_cast hle
      obtain ⟨i', rfl⟩ : ∃ i', e' = i' + 1 := ⟨e' - 1, by omega⟩
      have hw'N := hbig w' (i' + 1) (Or.inl hw'x) h1e' hdw'
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i' + 1)) (h (i' + 1) + ε) _ (i' + 1) (by positivity)
        (hpos _) (by linarith) hw'N
      obtain ⟨D', d', hd'0, hd'le, hD', hfin⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p n hp hn Δ m G N D d
        (h (i' + 1) + ε) x x' w' i' hΔ hklt hm hG hN hD hd hx hx' hlcx hlx' hw'x hw'x' (Or.inr hw')
        hdw' (by linarith [hpos (i' + 1)]) hnum.1
      exact ⟨i', D', d', by omega, hd'0, hd'le, hD', hfin⟩
    ·
      obtain ⟨b, A, hb0, hbε, hA, hAx, hAw'⟩ := GlobalTheory.T.exists_small_ample_through_off' X p hp N x w' ε hN hw'x hε
      have hAq : IsQCart A := hA.isQCart
      have hsum : Δ + D + (1 : ℚ) • A = Δ + (D + A) := by
        rw [one_smul, add_assoc]
      have hoff := off_add_smul X p n (Δ + D) A 1 x hAx
      rw [hsum] at hoff
      obtain ⟨hkltiff, hlciff, -, hoffz⟩ := hoff
      have hcut' : LcCut p n (Δ + (D + A)) x j := by
        unfold LcCut
        refine ⟨hlciff.mpr hlcx, fun hk => hnkx (hkltiff.mp hk), fun y hy hky => ?_⟩
        have h2 := (off_add_smul X p n (Δ + D) A 1 y (hoffz y hy)).1
        rw [hsum] at h2
        exact hdim y hy (fun hk => hky (h2.mpr hk))
      have hw2 : IsNkltCentre p n (Δ + (D + A)) w := by
        have h3 := (off_add_smul X p n (Δ + D) A 1 w (hoffz w hwx)).2.2.1
        rw [hsum] at h3
        exact h3.mpr hw
      have hnlc : ¬ LcAt p n (Δ + (D + A)) x' := by
        have h4 := GlobalTheory.T.not_lcAt_add_of_isNkltCentre' X p n hp hn (Δ + D) A w' x' hw' hAq hAw' hw'x'
        rw [add_assoc] at h4
        exact h4
      have hDA : QNum p N (d + b) (D + A) := qNum_add X p hp N d b D A hD hA
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε - b) _ (i + 1) (by positivity)
        (hpos _) (by linarith) hwN
      obtain ⟨hlcx2, -, -⟩ := hcut'
      obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
        N (D + A) (d + b) (h (i + 1) + ε - b) x x' w i hΔ hklt hm hG hN hDA (by linarith) hx hlcx2
        hnlc hwx hw2 hdw (by linarith [hpos (i + 1)]) hnum.2
      exact ⟨i, D', d', by omega, hd'0, by linarith, hD', Or.inl ⟨hcutD', hnkD'⟩⟩
  ·
    have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε) _ (i + 1) (by positivity)
      (hpos _) (by linarith) hwN
    obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
      N D d (h (i + 1) + ε) x x' w i hΔ hklt hm hG hN hD hd hx hlcx hlx' hwx hw hdw
      (by linarith [hpos (i + 1)]) hnum.2
    exact ⟨i, D', d', by omega, hd'0, hd'le, hD', Or.inl ⟨hcutD', hnkD'⟩⟩

end GlobalTheory.PairStep
end
end
