module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlacesStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BeSumStatementIffDefectSumBound
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraSide

section

@[expose] public section

namespace GlobalTheory.ClosingLemmaFourth

theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentAndSum

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      rw [Nat.padicValNat_def]
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceExponentPrimeBound

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum


namespace GlobalTheory.RefSum.WFree

theorem conj_eq_neg {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) z = -z ∧ z ≠ 0 :=
  _root_.GlobalTheory.ClosingLemmaFourth.main hd h

theorem two_mul_sum_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : 2 * ∑ τ : E →+* ℂ, Dw.mult τ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  have key : ∀ τ : E →+* ℂ, Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := fun τ => by
    have hs : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
      simpa using this
    obtain ⟨h1, h2⟩ := conj_eq_neg H.d_prime.pos hs
    have h3 : ComplexEmbedding.conjugate τ (H.rt : E) = -τ (H.rt : E) := h1
    unfold Datum.mult
    rw [h3]
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun e => h2 (by linear_combination (h - e) / 2)]
    · have : -τ (H.rt : E) = H.rt0 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans H.sqrt_neg_disc_sq.symm) with e | e
        · exact absurd e h
        · rw [e, neg_neg]
      rw [if_neg h, if_pos this, add_comm]
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := fun τ => star_star τ
  have e := Equiv.sum_comp hinv.toPerm Dw.mult
  rw [two_mul]
  nth_rewrite 2 [← e]
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun τ _ => key τ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Embeddings.card, smul_eq_mul]

theorem one_le_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q ≠ 0)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 1 ≤ vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K (q : 𝓞 K)) < 1 := (w.valuation_lt_one_iff_mem (K := K) _).2 h
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  have := WithZero.log_lt_log h0 one_ne_zero |>.2 h1
  rw [WithZero.log_one] at this
  unfold vAdd
  omega

theorem notMem_of_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := fun h' => by
  have hc : IsCoprime ((p : ℕ) : 𝓞 K) ((q : ℕ) : 𝓞 K) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨a, b, e⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h') (Ideal.mul_mem_left _ _ h)))

theorem different_vp_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {q : ℕ} (hq : q.Prime) (h : q ∉ badPrimes H l) : different_vp E q = 0 := by
  have : ¬ q ∣ (discr E).natAbs := fun hd => h (Nat.mem_primeFactors.2 ⟨hq, (hd.mul_left _).mul_right _,
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) (Int.natAbs_ne_zero.2 (discr_ne_zero E)))
      (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')⟩)
  rw [different_vp, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp

theorem refExp_vp_le_of_laws {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : GlobalTheory.FlatCore.Laws U x) (hN : UnramPts Xo c (badPrimes H l))
    (hF : FlatExists U x) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (cst : ℝ) {q : ℕ} (hq : q.Prime) {N : ℝ}
    (hs : ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) = N) :
    refExp_vp U cst (wtOf Dw u 0) q ≤ refExp_vp U cst (wtOf Dw (u + parWt Dw w₀) m) q +
      (((if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread E H Dw l Xo c r U hL.unf x hL.xi hL.geo hL.pos hL.good hN
  have hz : ∀ Z : Comp Xo c, ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m),
      IntOff (badPrimes H l) z.lo ∧ ∀ w, z.hi w - z.lo w ≤
        m * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := fun Z => by
    obtain ⟨t, ht1, ht2⟩ := ht Z
    obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
    exact GlobalTheory.CombTw.exists_twSec_comb E H Dw l Xo c r U hL.unf x _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  choose z hz1 hz2 using hz
  have key := GlobalTheory.T.baseLocusExponent_twistingSection_mul_le E H Dw l Xo c r U hL.unf x (wtOf Dw (u + parWt Dw w₀) m) _ (even_two_mul (m : ℤ)) cst
    (if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0) q hq z fun Z w hw => by
      have h1 := hz2 Z w
      simp only [fun τ => (GlobalTheory.DifferentGalois.ord_conjDifferent_and_sum E c.F (embF c τ) q w hq hw).1, ← Finset.sum_mul, hs] at h1
      split_ifs with hb
      · have h2 : (1 : ℝ) ≤ (vAdd w (q : c.F) : ℝ) := by exact_mod_cast one_le_vAdd w hq.ne_zero hw
        have h3 := Int.lt_floor_add_one ((z Z).lo w)
        linarith
      · obtain ⟨n, hn⟩ := hz1 Z w fun p hp =>
          notMem_of_ne w (Nat.prime_of_mem_primeFactors hp) hq (fun e => hb (e ▸ hp)) hw
        rw [different_vp_eq_zero l hq hb, hn] at h1
        rw [hn, Int.floor_intCast]
        simpa using h1
  rwa [add_sub_cancel] at key

end GlobalTheory.RefSum.WFree
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefExpPadicValLeShiftOfWeightFree

section

@[expose] public section

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.WFree
theorem refExp_padicVal_le_shift_of_weightFree : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  intro hP D T j Y e o hT hj hY _ _ hF u w₀ m cst q hq
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hL := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY
  have hp := hT.pins
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have h2 := two_mul_sum_mult (T.Q.Dw j)
  rw [StandardLattice.finrank_host D, hr, mul_assoc] at h2
  exact refExp_vp_le_of_laws hL (GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ _ _ _ hL.pos) hF u w₀ m cst hq
    (by exact_mod_cast Nat.eq_of_mul_eq_mul_left two_pos h2)
end GlobalTheory.RefSum.WFree
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.reference_exponent_valuation_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  first | exact @_root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree | exact _root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree | (intros; apply _root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree <;> assumption)
end
end
end
