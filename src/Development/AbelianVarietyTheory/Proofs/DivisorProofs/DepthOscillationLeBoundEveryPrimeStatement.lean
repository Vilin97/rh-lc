module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmFieldStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrimeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)


open Classical in
theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.OscSplit.oscLe_split | exact GlobalTheory.OscSplit.oscLe_split | (intros; apply GlobalTheory.OscSplit.oscLe_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)


open Classical in
theorem card_filter_inPsi_of_finrank {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {F : ℕ} (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
  have h := GlobalTheory.LamF.card_psiSet H
  rw [hF] at h
  have h2 : Nat.card (GlobalTheory.LamF.psiSet H) = (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  omega


open Classical in
theorem degree_le_of_exponentBound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} (hS : Shape Dw F k m) (hE : ExpBd Dw k cx Mb Sm M) :
    (∑ f : Lt1 Dw, (rk f : ℝ) * (cx f : ℝ)) ≤ F * (Dw.p + Dw.q : ℕ) * Mb + Sm := by
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hF : Module.finrank ℚ E = 2 * F := hS.2.2.2.2.2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (IsBig k)]
  refine add_le_add ?_ ?_
  · have hB : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) ≤ F * Mb := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)]
      calc ∑ τ : E →+* ℂ, ∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ)
          ≤ ∑ τ : E →+* ℂ, if InPsi H τ then Mb else 0 := by
            refine Finset.sum_le_sum fun τ _ => ?_
            split_ifs with hτ
            · have := hbig τ
              rw [Finset.filter_filter]
              push_cast at this
              convert this using 3
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
              exact absurd (hf.2 ▸ hf.1.1) hτ
        _ = F * Mb := by
            rw [← Finset.sum_filter, Finset.sum_const, card_filter_inPsi_of_finrank H hF, nsmul_eq_mul]
    have hN : ∀ f : Lt1 Dw, (rk f : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
      intro f
      have h1 := rk_le f
      have h2 : Dw.mult f.1 ≤ Dw.p + Dw.q := by
        unfold Datum.mult; split_ifs <;> omega
      exact_mod_cast h1.trans h2
    calc ∑ f ∈ Finset.univ.filter (IsBig k), (rk f : ℝ) * (cx f : ℝ)
        ≤ ∑ f ∈ Finset.univ.filter (IsBig k), ((Dw.p + Dw.q : ℕ) : ℝ) * (cx f : ℝ) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hN f) (Nat.cast_nonneg _)
      _ = ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) * (F * Mb) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = F * (Dw.p + Dw.q : ℕ) * Mb := by ring
  · have he : ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * (cx f : ℝ) = (sumSmallSpread k cx : ℝ) := by
      unfold sumSmallSpread
      push_cast
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext f
      simp [not_isBig_iff]
    rw [he]; exact hsm

theorem oscLe_zero_above_and_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  constructor
  · intro hMp la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun _ => 0)
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).2 (lt_of_le_of_lt (hE.2.2.2 f) hMp))).1
    simpa using h
  · intro la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun f => boundAll p (rk f) (cx f))
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1)).1
    have hsum : ∑ f, boundAll p (rk f) (cx f) ≤ (F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1) := by
      unfold boundAll
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (degree_le_of_exponentBound hS hE) (by linarith)
    intro T io e ho y
    obtain ⟨h1, h2⟩ := h T io e ho y
    refine ⟨by simpa using h1, fun ha => (h2 ha).trans ?_⟩
    simp only [Finset.sum_const_zero, Nat.cast_zero, zero_add]
    exact EReal.coe_le_coe_iff.2 hsum

end GlobalTheory.RefSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.depthOscillation_zero_above_and_degreeBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.RefSum.oscLe_zero_above_and_degree | exact GlobalTheory.RefSum.oscLe_zero_above_and_degree | (intros; apply GlobalTheory.RefSum.oscLe_zero_above_and_degree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem oscLe_eOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE vd S R hvd h2 h2S hdR hR p _
  have hram := GlobalTheory.T.depthOscillation_zero_above_and_degreeBound E H Dw l Xo c F k m M Mb Sm cx hS hE p
  have hMb : 0 ≤ Mb := hE.1
  have hp : p.Prime := Fact.out
  have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hF : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hFmMb : (0 : ℝ) ≤ F * m * Mb := by positivity
  unfold eOf
  split_ifs with h1 hS' h3 h4
  · exact hram.1 h1
  · exact GlobalTheory.T.depth_oscillation_le_at_two_cmField E H Dw l Xo c F k m M Mb Sm cx hS hE p (vd p) (hvd p) (h2 p hS')
  · exact hram.2
  all_goals
    have hpM : p ≤ M := Nat.le_of_not_lt h1
    have h2' : p ≠ 2 := fun h => hS' (h ▸ h2S)
    have hpd : ¬ (p : ℤ) ∣ discr E := hR p hp hS' h3
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := le_trans hp.one_lt.le hpM
      exact_mod_cast this
    have hlog : 0 ≤ Real.logb p M := Real.logb_nonneg (by exact_mod_cast hp.one_lt) hM1
    by_cases hsq : IsSquare (-(H.d : ZMod p))
    · have hd0 : (H.d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdv
        have : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 hdv
        exact h3 (this ▸ hdR)
      have hs := GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd ⟨hd0, hsq⟩
      refine OscLe.mono Xo hs ?_
      first
      | (unfold eSmall
         have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         have hB : (0 : ℝ) ≤ F * (m + 1) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) := by positivity
         linarith)
      | (have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         linarith)
    · first
      | exact GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd hsq (by exact_mod_cast hM1)
      | exact GlobalTheory.T.depthOscillation_large_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p hpd hsq (by omega)

end GlobalTheory.RefSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.depthOscillation_le_bound_every_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  first | exact @GlobalTheory.RefSum.oscLe_eOf | exact GlobalTheory.RefSum.oscLe_eOf | (intros; apply GlobalTheory.RefSum.oscLe_eOf <;> assumption)
end
end
