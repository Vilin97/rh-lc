module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.MvPolynomial
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealTransferOfSyzygy
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoeffRenameProdCongrRight

-- Source module: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.DegPolynomialIsHomogeneous

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

def lieSign (bot b : Bool) (m : ℕ) : ℚ := if bot = b then (-1) ^ m else -1

theorem lieSign_cases (bot b : Bool) (m : ℕ) : lieSign bot b m = 1 ∨ lieSign bot b m = -1 := by
  unfold lieSign
  split_ifs
  · rcases neg_one_pow_eq_or ℚ m with h | h <;> simp [h]
  · right; rfl

theorem le_dimFl (f j k : ℕ) (hf : 1 ≤ f) : j + k ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 := by
  unfold IndefiniteRowSideFullHecke.RestTerms.dimFl
  have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
    rcases Nat.lt_or_ge (j + k) 2 with h | h
    · have : j + k - 1 = 0 := by omega
      simp [this]
    · rw [mul_comm (j + k)]; exact Nat.mul_le_mul_left _ h
  have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
  have h3 : (j + k) * (j + k - 1) / 2 ≤ f * ((j + k) * (j + k - 1) / 2) :=
    Nat.le_mul_of_pos_left _ hf
  omega

theorem lieClass_reduce (f j k : ℕ) (hf : 1 ≤ f) (bot : Bool)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : ∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 - m))
    (σ : Fin f × Bool) (τ : Fin f) (m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ j + k) :
    I (IndefiniteRowSideFullHecke.RestTerms.lieClass f j k (m - 1) σ * Q τ m) =
      (lieSign bot σ.2 (m - 1) : ℝ) *
        I (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) σ.1 * Q τ m) := by
  have hD := le_dimFl f j k hf
  have hkill := hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega)
    (by convert hQ τ m (by omega) hmN using 1; omega)
  have hsplit : IndefiniteRowSideFullHecke.RestTerms.psumAt f j k (m - 1) σ.1 =
      (∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ (m - 1)) +
        ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ (m - 1) := by
    unfold IndefiniteRowSideFullHecke.RestTerms.psumAt
    exact Fin.sum_univ_add _
  rw [hsplit, add_mul, map_add (f := _)] at hkill
  obtain ⟨τ', b⟩ := σ
  rcases Nat.even_or_odd (m - 1) with he | ho
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, he.neg_pow] <;> linarith
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, ho.neg_pow,
        Finset.sum_neg_distrib, neg_mul, map_neg] <;> linarith

theorem smallPowerSum_isHomogeneous (f r a : ℕ) (c : SmallBlock) (m : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c m τ).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h := (isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)).pow m
  rw [one_mul] at h
  exact h

theorem degPolynomial_isHomogeneous (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h1 := VandermondeOfHomogeneous.proof
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a))).mul hfib
  have hdeg : 1 * (f * (r * a)) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end RestBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StaircaseIsHomogeneous

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem CoinvAtTop.closed : CoinvAtTop.Statement :=
  CoinvAtTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof)

namespace FlagProportional

theorem staircase_isHomogeneous (f j k : ℕ) :
    (monomial (Coinv.staircase f (j + k)) (1 : ℝ)).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  show ∑ v, (Coinv.staircase f (j + k)) v = Coinv.coinvTop f (j + k)
  rw [← Coinv.sum_staircase_exponents]
  simp [Coinv.staircase]

theorem eval_top (f j k : ℕ) (L : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ)
    (hL : ∀ (m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), 1 ≤ m →
      m ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k → G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k - m) →
        L (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0)
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (hG : G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k)) (c : ℝ)
    (hc : G - C c * monomial (Coinv.staircase f (j + k)) 1 ∈ Coinv.psumIdeal ℝ f (j + k)) :
    L G = c * L (monomial (Coinv.staircase f (j + k)) 1) := by
  classical
  set D := IndefiniteRowSideFullHecke.RestTerms.dimFl f j k
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  obtain ⟨Q, hQ, hEq⟩ := CoinvIdealComponent.proof CoinvIdealRepresentation.proof
    HomogeneousComponentMul.proof ℝ f (j + k) _ hc D
  have hJ : (G - C c * s).IsHomogeneous D := hG.sub ((staircase_isHomogeneous f j k).C_mul c)
  have hcomp : homogeneousComponent D (G - C c * s) = G - C c * s := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hJ), if_pos rfl]
  have e1 := hcomp.symm.trans hEq
  have e2 : G - C c * s = homogeneousComponent D
      (∑ m ∈ Finset.Icc 1 (j + k), ∑ b : Fin f, Coinv.bps ℝ f (j + k) m b * Q m b) := by
    rw [← e1, hcomp]
  have hzero : L (G - C c * s) = 0 := by

    rw [e2, map_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_

    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hp : (Coinv.bps ℝ f (j + k) m b).IsHomogeneous m :=
      IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (hQ m b)))]
    split_ifs with h
    · exact hL m b (Q m b) hm1 (by omega) (hQ m b)
    · exact map_zero L
  calc L G = L (G - C c * s) + L (C c * s) := by rw [← map_add (f := _), sub_add_cancel]
    _ = c * L s := by rw [hzero, zero_add, C_mul', map_smul, smul_eq_mul]

end FlagProportional


open FlagProportional in
theorem FlagIntegralProportional.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.FlagIntegralProportional.Statement := by
  intro f j k _ _ _ I hI
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  have hdd : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      ∃ c : ℝ, I G = c * I s ∧ IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G = c * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s := by
    intro G hG
    obtain ⟨c, hc⟩ := CoinvAtTop.closed ℝ f (j + k) G hG
    exact ⟨c, eval_top f j k I hI.kills G hG c hc,
      eval_top f j k (IndefiniteRowSideFullHecke.RestTerms.ddConst f j k)
        (fun m τ G hm _ _ => FlagEq.ddConst_psumAt_mul f j k m τ G hm) G hG c hc⟩
  have hs0 : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s ≠ 0 := by
    obtain ⟨c, -, h⟩ := hdd (monomial (FlagEq.rho f (j + k)) 1)
      (isHomogeneous_monomial _ (by rw [FlagEq.rho_degree]; rfl))
    rw [FlagEq.ddConst_monomial_rho] at h
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h
  have hIs : I s ≠ 0 := by
    obtain ⟨G0, hG0, hne⟩ := hI.ne_zero
    obtain ⟨c, h, -⟩ := hdd G0 hG0
    intro h0
    rw [h0, mul_zero] at h
    exact hne h
  refine ⟨I s / IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s, div_ne_zero hIs hs0, fun G hG => ?_⟩
  obtain ⟨c, h1, h2⟩ := hdd G hG
  rw [h1, h2]
  field_simp

end

end GroundTheory.Heights₂.Heights.RestTerms
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.RestAt

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

theorem core (hA : RestBound.Statement)
    (f r a j k : ℕ) (c : SmallBlock) (bot : Bool) (h : r + a = j + k)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hsp : ∀ m τ, rootRingToReal f (r + a) j k h (smallPowerSum f r a c m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot m τ)
    (hF : rootRingToReal f (r + a) j k h (restPolynomial f r a c) = IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot)
    (hD : rootRingToReal f (r + a) j k h (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)
    (hn : f * (r * a) = IndefiniteRowSideFullHecke.RestTerms.nDim f j k)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (vol : ℝ) (hvol : 0 < vol) (P : Set ℕ) (B₀ : ℝ)
    (hB₀ : 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀)
    (σ : ℕ → ℕ → Fin f → Fin f × Bool) (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : IndefiniteRowSideFullHecke.RestTerms.IsPsumDecomp f j k (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) Q) :
    Summable (fun p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀ =>
        IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1) ∧
      |∑' p : IndefiniteRowSideFullHecke.RestTerms.primesOver P B₀, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1| ≤
        1.6 * ((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) * vol *
          |I (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot)| := by
  have hB₀' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ := by rw [h]; exact hB₀
  obtain ⟨⟨Q₀, hQ₀⟩, hall⟩ := hA f r a c B₀ hf hr ha hB₀'
  have hFh := RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.proof f r a c
  obtain ⟨hQh, -⟩ := isPowerSumDecomposition_homogeneousComponent f (r + a) _ Q₀ hFh hQ₀
  set Qh : ℕ → Fin f → RootRing f (r + a) :=
    fun m τ => homogeneousComponent (topDegree f (r + a) + 1 - m) (Q₀ m τ) with hQhdef
  obtain ⟨c₀, -, hIc⟩ := FlagIntegralProportional.intersectionNumber_baseChange f j k hf hj hk I hI
  set κ : ℝ := c₀ / FlagEq.stairConst f (j + k) with hκ
  have hIκ : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      I G = κ * flagIntegralReal f (j + k) G := by
    intro G hG
    rw [hIc G hG, flagIntegralReal_eq_mul_ddConst, hκ]
    field_simp [FlagEq.stairConst_pos.ne']
  have htop : topDegree f (r + a) = IndefiniteRowSideFullHecke.RestTerms.dimFl f j k := by
    rw [h]; rfl
  have hDle := le_dimFl f j k hf
  set s : ℕ → ℕ → Fin f → Fin f := fun p n τ => (σ p n τ).1 with hs
  set e : ℕ → ℕ → Fin f → ℕ → ℚ := fun p n τ m => lieSign bot (σ p n τ).2 (m - 1) with he
  obtain ⟨hsum, hbd⟩ := hall Qh hQh s e (fun _ _ _ _ => lieSign_cases _ _ _) P
  have hQ' : IndefiniteRowSideFullHecke.RestTerms.IsPsumDecomp f j k (rootRingToReal f (r + a) j k h (restPolynomial f r a c))
      Q := by rw [hF]; exact hQ
  have hterm : ∀ (p : ℕ) (τ : Fin f) (m : ℕ), m ∈ Icc 2 (j + k) → ∀ n : ℕ,
      IndefiniteRowSideFullHecke.RestTerms.restTerm f j k I σ Q p τ m n =
        κ * (((p : ℝ) ^ ((n + 1) * m))⁻¹ * ((e p (n + 1) τ m *
          restTerm f (r + a) Qh m τ (smallPowerSum f r a c (m - 1) (s p (n + 1) τ)) : ℚ) : ℝ)) := by
    intro p τ m hm n
    obtain ⟨hm2, hmN⟩ := Finset.mem_Icc.1 hm
    have hlie := lieClass_reduce f j k hf bot I hI Q hQ.1 (σ p (n + 1) τ) τ m hm2 hmN
    have hG := smallPowerSum_isHomogeneous f r a c (m - 1) (σ p (n + 1) τ).1
    have hhom : (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) (σ p (n + 1) τ).1 * Q τ m).IsHomogeneous
        (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
      rw [← hsp]
      have := ((rootRingToReal_isHomogeneous_iff f (r + a) j k h _ _).2 hG).mul
        (hQ.1 τ m (by omega) hmN)
      convert this using 1
      omega
    have hwd := flagIntegralReal_transfer_of_syzygy f (r + a) j k h _ Qh hQh Q hQ'.2 m τ _
      (fun S hS => syzygy_term_zero hA f r a c hf hr ha S hS τ (σ p (n + 1) τ).1 m hm2 (by omega))
    rw [IndefiniteRowSideFullHecke.RestTerms.restTerm, hlie, hIκ _ hhom, ← hsp, hwd]
    simp only [restTerm, he, hs]
    push_cast
    ring
  have hIcc : Finset.Icc 2 (r + a) = Finset.Icc 2 (j + k) := by rw [h]
  have hmodel : ∀ p : ℕ, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p =
      vol * κ * restPrimeModel f r a c Qh s e p := by
    intro p
    have hX : (∑ τ : Fin f, ∑ m ∈ Icc 2 (j + k), ∑' n : ℕ,
        IndefiniteRowSideFullHecke.RestTerms.restTerm f j k I σ Q p τ m n) =
        κ * ∑ τ : Fin f, ∑ m ∈ Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((e p (n + 1) τ m * restTerm f (r + a) Qh m τ
            (smallPowerSum f r a c (m - 1) (s p (n + 1) τ)) : ℚ) : ℝ) := by
      rw [hIcc, Finset.mul_sum]
      refine sum_congr rfl fun τ _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [← tsum_mul_left]
      exact tsum_congr fun n => hterm p τ m hm n
    rw [IndefiniteRowSideFullHecke.RestTerms.restAt, restPrimeModel, hX]
    ring
  have hs' : Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
      restPrimeModel f r a c Qh s e p) := summable_abs_iff.1 hsum
  have hJ : I (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot) = κ * (fibreDegree f r a c : ℝ) := by
    have hh : (IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
      rw [← hD, ← htop]
      exact (rootRingToReal_isHomogeneous_iff f (r + a) j k h _ _).2 (degPolynomial_isHomogeneous f r a c)
    rw [hIκ _ hh, ← hD, TermBoundEq.flagIntegralReal_rootRingToReal]
    rfl
  have hn' : ((f * (r * a) + 1 : ℕ) : ℝ) = (IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1 := by
    rw [hn]; push_cast; ring
  rw [hn'] at hbd
  refine ⟨?_, ?_⟩
  · show Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
      IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1)
    simp_rw [hmodel]
    exact hs'.mul_left _
  · show |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, IndefiniteRowSideFullHecke.RestTerms.restAt f j k I vol σ Q p.1| ≤ _
    simp_rw [hmodel]
    rw [tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hJ, abs_mul]
    have h0 : 0 ≤ vol * |κ| := by positivity
    calc vol * |κ| * |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Qh s e p|
        ≤ vol * |κ| * (1.6 * ((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) * |(fibreDegree f r a c : ℝ)|) :=
          mul_le_mul_of_nonneg_left hbd h0
      _ = _ := by ring

end RestBoundEq

theorem RestBound.imp : RestBound.Statement → IndefiniteRowSideFullHecke.RestTerms.RestBound.Statement := by
  intro hA f j k hf hj hk bot _hsmall I hI vol hvol P _hP B₀ hB₀ σ Q hQ
  cases bot with
  | false =>
    exact RestBoundEq.core hA f j k j k .first false rfl hf hj hk hj hk
      (rootRingToReal_smallPowerSum_first f j k) (rootRingToReal_restPolynomial_first f j k)
      (rootRingToReal_degreePolynomial_first f j k) (by unfold IndefiniteRowSideFullHecke.RestTerms.nDim; ring)
      I hI vol hvol P B₀ hB₀ σ Q hQ
  | true =>
    exact RestBoundEq.core hA f k j j k .last true (Nat.add_comm k j) hf hk hj hj hk
      (rootRingToReal_smallPowerSum_last f k j) (rootRingToReal_restPolynomial_last f k j)
      (rootRingToReal_degreePolynomial_last f k j) (by unfold IndefiniteRowSideFullHecke.RestTerms.nDim; ring)
      I hI vol hvol P B₀ hB₀ σ Q hQ

end

end GroundTheory.Heights₂.Heights.RestTerms
end
end
