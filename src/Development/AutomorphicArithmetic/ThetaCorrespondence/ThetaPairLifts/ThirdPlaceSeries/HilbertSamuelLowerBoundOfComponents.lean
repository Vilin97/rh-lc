module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegBoundOfClaimNumbers
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsAtDeepLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDegreeParametersBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelALogALe

section

@[expose] public section

namespace GlobalTheory

theorem hilbertSamuel_ALogA_le (T D : ℕ) (PP b z : ℝ) (hD1 : 1 ≤ D) (hDT : D ≤ T) (hPP : 1 ≤ PP)
    (hb : 1 ≤ b) (hlogb : Real.log b ≤ PP) (hTP : (T : ℝ) * PP ≤ Real.sqrt b) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (max (26 * (26 * (D : ℝ) ^ 2 + 2 * z * T)) 1)
      ≤ 6000 * b := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDT' : (D : ℝ) ≤ T := by exact_mod_cast hDT
  have hT1 : (1 : ℝ) ≤ T := le_trans hD1' hDT'
  set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 2 * z * T := by positivity
    nlinarith
  have hmax : max A 1 = A := max_eq_left hA1
  rw [hmax]
  have hApos : 0 < A := by linarith
  have hAle : A ≤ 702 * (T : ℝ) ^ 2 := by
    have h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith
    have h2 : 2 * z * (T : ℝ) ≤ T := by nlinarith
    have h3 : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (T : ℝ) ≤ Real.sqrt b := by nlinarith
  have hlogT : 2 * Real.log T ≤ PP := by
    have h1 : Real.log T ≤ Real.log (Real.sqrt b) := Real.log_le_log hT0 hTsq
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog702 : Real.log 702 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hlogA : Real.log A ≤ 8 * PP := by
    have h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2) := Real.log_le_log hApos hAle
    have h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP) :=
    mul_le_mul hAle hlogA hlogA0 (by positivity)
  have hsq : ((T : ℝ) * PP) ^ 2 ≤ b := by
    have h0 : 0 ≤ (T : ℝ) * PP := by positivity
    calc ((T : ℝ) * PP) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ h0 hTP 2
      _ = b := Real.sq_sqrt (by linarith)
  have hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2 := by
    have : PP ≤ PP ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNine

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

end GlobalTheory.TwistDeg
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedBundleDegreeLowerBound

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.TwistDeg
open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
theorem degree_twist_ge : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) → GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) → Y.degC la Z - Y.rkC la Z * (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2) ≤ Y.degC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z := by
  intro hP
  refine ⟨120, by norm_num, fun D T hT j hp hq _ hj Y e o hY Lb hL hM hE _ _ c₁ hc hc₁ la w Z hw hG => ?_⟩
  have hn : 1 ≤ D.R.n := D.R.toFrame.ord_pos
  have h1 := D.R.two_le_m
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hrk : (0 : ℝ) ≤ Y.rkC la Z := Nat.cast_nonneg _
  rcases isEmpty_or_nonempty (Psi T.Q.H) with h0 | ⟨⟨τ₀⟩⟩
  · rw [show la + parWt (T.Q.Dw j) w = la from funext fun τ => h0.elim τ]
    exact sub_le_self _ (by positivity)
  obtain ⟨hpq, -, -, -, -, g, ee, F, -⟩ := hY.unf Y.d.c₂.F.val.toRingHom rfl
  have hK := GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ Y.d.c₂.F.val.toRingHom rfl ee F (by omega) hY.geo
  obtain ⟨t, ht, -, hd⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) (badPrimes T.Q.H Y.d.l₂) hK hY.unf (by omega)
    (_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hT hj hY)).2 ⟨c₁, hc⟩ Z w (hc Z τ₀).1.some.hasPts
  have key := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ _ _ _ _ _ _ Y.U (xiR D) D (fun _ => D.sp.W j) Y.dict Z _ t _ (badPrimes T.Q.H Y.d.l₂) hY.unf
    (AllWt.even_wtOf la 0) badPrimes_prime ht hG
  rw [← wtOf_add'] at key
  refine le_trans ?_ key
  rw [sub_eq_add_neg, ← mul_neg]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans ?_ (sub_le_sub_right hd _)) hrk)
  have hdeg : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hd2 := abs_le.1 (GlobalTheory.abs_lrd_sub_log_d_le_lrd _ T.Q.H)
  have hcard : (Fintype.card (Psi T.Q.H) : ℝ) ≤ 2 * D.R.f := by
    have := Fintype.card_subtype_le fun τ : D.host.E →+* ℂ => τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0
    rw [Embeddings.card, hdeg] at this
    exact_mod_cast (Fintype.card_congr (Equiv.refl _)).le.trans this
  refine numeric hf hr hL (by exact_mod_cast (by omega : (T.Q.Dw j).q ≤ D.R.r)) (by linarith [hd2.1, hd2.2])
    (by rw [lrd_eq]; exact (log_rd_le_fieldSz _).trans hE) (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ ?_ ?_
  · refine (Finset.sum_le_card_nsmul _ _ (3 * (D.R.r : ℝ)) fun τ _ => by exact_mod_cast hw τ).trans ?_
    rw [nsmul_eq_mul, Finset.card_univ]
    nlinarith
  · simp only [hc.c1_eq ⟨Z⟩]
    rw [← Finset.sum_mul, abs_mul, mul_comm]
    exact mul_le_mul hc₁ (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by positivity)
  · refine (logSum_bad_le _ _).trans ?_
    have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.lev.2, Nat.lcm_one_right]
    have hD : Real.log |(discr D.host.E : ℝ)| = 2 * D.R.f * lrd D.host.E := by
      rw [lrd_eq, hdeg]; push_cast; field_simp
    rw [hM', hD]
    linarith [hd2.1]
end GlobalTheory.TwistDeg
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twisted_bundle_degree_lower_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) → GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) → Y.degC la Z - Y.rkC la Z * (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2) ≤ Y.degC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z := by
  first | exact @_root_.GlobalTheory.TwistDeg.degree_twist_ge | exact _root_.GlobalTheory.TwistDeg.degree_twist_ge | (intros; apply _root_.GlobalTheory.TwistDeg.degree_twist_ge <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.ShortRoad

theorem hilbertSamuel_of_component_estimates_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree →
    _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  intro hX h2 hGD hQd hSi hTo hSA hDG hS hF hDe hSh
  obtain ⟨Cp, hCp, htw⟩ := _root_.GlobalTheory.T.twisted_bundle_degree_lower_bound h2
  have hrk := _root_.GlobalTheory.T.twisted_flat_bundle_ranks h2
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (((((((_root_.GlobalTheory.T.exists_degree_parameters_bound_alt_alt hX h2 hGD hQd hSi hTo hSA hDG hS hF).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and hS).and hF).and
    hDe).and hSh) ?_
  intro eps Fm CH _ H
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _, hR⟩, _, _, hZ⟩, _, _, hQu⟩, CS, _, hSz⟩, _, _, hFl⟩, _, _, hDg⟩, _, _, hSr⟩ := H
  refine ⟨10000 + 2 * Cp, by positivity, ?_⟩
  obtain ⟨x0, H⟩ := ((((((hR.and hZ).and hQu).and hSz).and hFl).and hDg).and hSr)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hR, hZ⟩, hQu⟩, hSz⟩, hFl⟩, hDg⟩, hSr⟩ := H x hx hle ι p hp
  set PP := (Fm.parT x hx ι).PP
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ with hPdef
  obtain ⟨hp1, hq1, hfin, hqe, hanti, ⟨w, hw, huM⟩, -⟩ := hQu i hi
  obtain rfl := hqe u1 hu1
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, -, hZPP, hTPP, hzb, hz2, -, -⟩ := hZ i hi Y hY
  obtain ⟨hb1, hbU, -, -, -, hbPP, hSq⟩ := hSz i
  obtain ⟨hT, hρ, -, -⟩ := (hSq hi).2 _ hu1
  have hY1 := hY.1
  have hAG := hgood (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (P.wt (lenT p i PP))
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).1)
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).2)
  have hFZ := hFl i hi Y hY
  have hrkZ := (hrk (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 _ hFZ).1
  have htwZ := htw (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (Fm.L x ι).sc.L hL1 hM hfs hfr (le_of_eq (by rw [zBase]))
    _ hFZ (by rw [abs_neg]; exact hflat) (P.wt (lenT p i PP)) w
  have hDf : 1 ≤ CompHt.dimFlag (dat p i) := by
    rw [GlobalTheory.CovTop.WtShape.dim_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hz1 : 1 ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hPP1 : 1 ≤ PP := (one_le_pow₀ hz1).trans hZPP
  have hLz : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hz12 : zBase (Fm.L x ι) ≤ zBase (Fm.L x ι) ^ 12 := le_self_pow₀ hz1 (by norm_num)
  have hlb : Real.log (Fm.L x ι).sc.b ≤ PP := by
    rw [Formalism.BasicNotions.Scale.b, Real.log_exp]
    linarith
  have hT1 : (1 : ℝ) ≤ (lenT p i PP : ℝ) := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hsq : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (Fm.L x ι).sc.b by linarith)
    have := Real.one_le_sqrt.2 hb1
    nlinarith
  have hZb : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have a1 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
    have a2 : PP ≤ (lenT p i PP : ℝ) * PP := le_mul_of_one_le_left (by linarith) hT1
    exact a1.trans (hZPP.trans (a2.trans (hTPP.trans hsq)))
  have hkap : 0 ≤ kap p i := le_of_lt (pos_of_mul_pos_right (by linarith) (by linarith : (0 : ℝ) ≤ PP))
  have hz0 : 0 ≤ zed p i PP P.u₁ := by
    unfold zed
    exact mul_nonneg (by norm_num) (add_nonneg (by positivity) (mul_nonneg (by positivity) hρ))
  have hDf0 : (0 : ℝ) < CompHt.dimFlag (dat p i) := by exact_mod_cast hDf
  refine ⟨26 * (26 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 + 2 * zed p i PP P.u₁ * lenT p i PP),
    4000 * (Fm.L x ι).sc.b + 2 * (Cp * zBase (Fm.L x ι) ^ 2), by positivity, by positivity, ?_, fun Z => ?_⟩
  · have hA := GlobalTheory.hilbertSamuel_ALogA_le (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (Fm.L x ι).sc.b (zed p i PP P.u₁) hDf (by omega)
      hPP1 hb1 hlb hTPP hz0 hz2
    have e1 := mul_le_mul_of_nonneg_left hZb hCp
    have e2 := mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 10000 + 2 * Cp)
    nlinarith
  obtain ⟨n, Λ, β, ΛD, ΛT, J, hn, hΛ, hβ, hΛD, hΛT, hln, hlβ, hlδ, hlΛ, hlΛD, hlΛT, hJ, hcl⟩ := hR i hi Y hY Z
  obtain ⟨δ0, hδ0, hδ⟩ := hDg i hi Y hY _ hu1
  have hdg : 1 ≤ Y.dg P.u₁ Z := by
    have h0 : (0 : ℝ) < Y.dg P.u₁ Z := hδ0.trans_le (hδ Z).1
    simp only [Deep.dg] at h0 ⊢
    exact Nat.one_le_cast.2 (Nat.cast_pos.1 h0)
  have hsh := hSr i hi Y hY _ hu1 Z
  rw [huM, hrkZ] at hsh
  have hbin : (1 : ℝ) ≤ binT p i PP := by
    unfold binT
    exact Nat.one_le_cast.2 (Nat.choose_pos (by omega))
  have hd : 0 < Y.rkC (P.wt (lenT p i PP)) Z := by nlinarith [hsh.1]
  have htwz := htwZ Z hw (hAG.2 Z)
  rw [← huM] at htwz
  exact GlobalTheory.CovHSNum.deg_bound_of_claim_numbers (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (kap p i) (Fm.L x ι).sc.b (zed p i PP P.u₁)
    (CompHt.rhoB (dat p i) P.u₁) n Λ β ΛD ΛT J (Y.dg P.u₁ Z) (Y.ht P.u₁ Z) (Y.rkC (P.wt (lenT p i PP)) Z)
    (Y.degC (P.wt (lenT p i PP)) Z) (Y.degC (uM p i) Z) (Cp * zBase (Fm.L x ι) ^ 2) hDf hT hPP1 hb1 hlb hTPP rfl hρ hz2 hzb
    hkap hn hΛ hβ hΛD hΛT hdg hd hln hlβ hlδ hlΛ hlΛD hlΛT hJ hsh.2 hcl (by positivity) (by rw [zBase]; exact htwz)
end GlobalTheory.CovTop.ShortRoad
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverHeightSum := by
  first | exact @_root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | exact _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates_alt <;> assumption)
end
end
end
end
