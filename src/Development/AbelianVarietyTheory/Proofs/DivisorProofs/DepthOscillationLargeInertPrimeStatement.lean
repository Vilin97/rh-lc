module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentLeDetDepthAdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
public import Mathlib.Data.Nat.PadicValNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanksStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
import Mathlib.Algebra.Order.Star.Int
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIK

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.DetPowContent

open GlobalTheory.DetPowShape

noncomputable def intCoeff (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) : ℤ :=
  (detZ i ^ k).coeff α * α.prod fun _ n => ((n.factorial : ℕ) : ℤ)

theorem cast_intCoeff (C : Type) [Field C] (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    ((intCoeff i k α : ℤ) : C) = (detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α := by
  rw [intCoeff, detPow_eq_map, MvPolynomial.coeff_map, Int.cast_mul, GlobalTheory.FGDepth.mfact]
  congr 1 <;> simp [Finsupp.prod]

theorem mem_support_iff' (C : Type) [Field C] [CharZero C] (i k : ℕ) (α) :
    α ∈ (detPow C i k).support ↔ α ∈ (detZ i ^ k).support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, detPow_eq_map,
    MvPolynomial.coeff_map]
  simp

theorem intCoeff_ne_zero (i k : ℕ) (α) (h : α ∈ (detZ i ^ k).support) : intCoeff i k α ≠ 0 := by
  rw [intCoeff]
  refine mul_ne_zero (MvPolynomial.mem_support_iff.1 h) ?_
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact_mod_cast Nat.factorial_ne_zero _

theorem v_intCast (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (m : C) = (((padicValNat p m.natAbs : ℕ) : ℝ) : WithTop ℝ) := by
  have h := GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv m.natAbs (Int.natAbs_ne_zero.2 hm)
  rcases Int.natAbs_eq m with h1 | h1
  · conv_lhs => rw [h1]
    simpa using h
  · conv_lhs => rw [h1, Int.cast_neg, v.map_neg]
    simpa using h

end GlobalTheory.DetPowContent

namespace GlobalTheory


open GlobalTheory.DetPowShape GlobalTheory.DetPowContent in
theorem detPow_content_const : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C]
    [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 →
      content v (detPow C i k) = (κ : EReal) := by
  intro p hp i k
  set S := (detZ i ^ k).support with hS
  have hne : S.Nonempty := by
    refine ⟨∑ a : Fin i, Finsupp.single ⟨a, a⟩ k, ?_⟩
    rw [← mem_support_iff' ℚ]
    rw [MvPolynomial.mem_support_iff, (detPow_shape ℚ i k).2.2.1]
    exact one_ne_zero
  let f : ((Σ _ : Fin i, Fin i) →₀ ℕ) → ℕ := fun α => padicValNat p (intCoeff i k α).natAbs
  obtain ⟨α0, hα0, hmin⟩ := S.exists_min_image f hne
  refine ⟨(f α0 : ℝ), fun C _ _ v hv => ?_⟩
  have hval : ∀ α ∈ S, GlobalTheory.FGDepth.toE (v ((detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α)) =
      ((f α : ℝ) : EReal) := by
    intro α hα
    rw [← cast_intCoeff, v_intCast C v p hp hv _ (intCoeff_ne_zero i k α hα)]
    rfl
  unfold GlobalTheory.FGDepth.content
  apply le_antisymm
  · refine iInf₂_le_of_le α0 ((mem_support_iff' C i k α0).2 hα0) ?_
    rw [hval α0 hα0]
  · refine le_iInf₂ fun α hα => ?_
    have hα' := (mem_support_iff' C i k α).1 hα
    rw [hval α hα']
    exact_mod_cast hmin α hα'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIKStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 → content v (detPow C i k) = (κ : EReal) := by
  first | exact @GlobalTheory.detPow_content_const | exact GlobalTheory.detPow_content_const | (intros; apply GlobalTheory.detPow_content_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hdisc hinert f k hpsi
  letI := H.starRing
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k p Fact.out (rk f) k
  have hFGT := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hbd : boundInert p Dw.q (rk f) k =
      2 * ((rk f : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * ((Dw.q : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) - 1) := rfl
  refine ⟨κ - boundInert p Dw.q (rk f) k, κ, fun T io e ho y => ⟨le_nuFac fun Ch X => ?_, fun _ => ?_⟩, by linarith⟩
  · obtain ⟨hfrob, htyp⟩ := hFGT T io X
    obtain ⟨h, hh, -, lab, hlab, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := htyp y Ch f.1
    have hf0 : f.1 = lab 0 := hlab.1.symm
    obtain ⟨hsat, hsupp, hnu⟩ := hfr 0 f hf0
    have hiff := (hfrob (lab 0) (lab (0 + 1)) (hlab.2.1 0)).2 hinert
    have hnot : ¬ InPsi H (lab (0 + 1)) := fun h1 =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H f.1 ⟨hpsi, by rw [hf0]; exact hiff.1 h1⟩
    have hc1 : (Finset.univ.filter fun a => ty a = (0 : ZMod h) + 1).card ≤ Dw.q := by
      have := hcard (0 + 1)
      rw [if_neg hnot, Fintype.card_subtype] at this
      exact this.le
    have hd2 := GlobalTheory.FGDepth.InertBound.content_le_detDepth_add X.C (vX_vp X) p Fact.out (vX_vp_p X) d' h hh ty G' mu
      0 Dw.q (rk f) k hc1 _ hsat hsupp
    rw [hκ X.C (vX_vp X) (vX_vp_p X), ← hbd] at hd2
    rw [hnu k, EReal.coe_sub]
    exact EReal.sub_le_of_le_add hd2
  · obtain ⟨Ch⟩ := hch T io y
    obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine (nuFac_le Ch X f k).trans ?_
    rw [← hκ X.C (vX_vp X) (vX_vp_p X)]
    exact h1.2.1

end GlobalTheory.RefSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.factorDepth_bounds_inert_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  first | exact @GlobalTheory.RefSum.facBetween_inert | exact GlobalTheory.RefSum.facBetween_inert | (intros; apply GlobalTheory.RefSum.facBetween_inert <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.InertOsc

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

theorem card_filter_inPsi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    [DecidablePred (fun τ : E →+* ℂ => InPsi H τ)] :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact GlobalTheory.LamF.card_psiSet H

theorem nuBetween_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c}
    {cx : Lt1 Dw → ℕ} {A B B' : ℝ} (h : NuBetween Xo la cx A B) (hB : B ≤ B') : NuBetween Xo la cx A B' :=
  fun T io e ho y => ⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩

theorem big_arith {i q k m p : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    2 * i + 2 * q * p ≤ 5 * m * p := by
  have h1 : 2 * m ≤ m * p := by nlinarith
  have h2 : q * p ≤ m * p := Nat.mul_le_mul_right _ hq
  nlinarith

theorem big_bound {i q k m p c : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    boundInert p q i c ≤ 5 * (m : ℝ) * c / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ) := by exact_mod_cast big_arith hi hk hq hp
  push_cast at hn
  unfold boundInert
  rw [div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have : (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1)
      = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  have : 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)

theorem rk_add_one_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (f : Lt1 Dw) : rk f + 1 ≤ Dw.p + Dw.q + 1 := by
  have h := rk_le f
  unfold Datum.mult at h
  split_ifs at h <;> omega

theorem oscLe_inert_large : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  classical
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp
  obtain ⟨hS1, hSq, hmk, hm1, hk2, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  intro la
  set w : Lt1 Dw → ℝ := fun f => if IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1)
    else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw
  have key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f := by
    intro f
    by_cases hb : IsBig k f
    · obtain ⟨A, B, hAB, hBA⟩ := GlobalTheory.T.factorDepth_bounds_inert_prime E H Dw l Xo c p la hdisc hin f (cx f) hb.1
      refine ⟨(A, B), hAB, ?_⟩
      simp only [hw, if_pos hb]
      exact hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)
    · refine ⟨(0, boundAll p (rk f) (cx f)), (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, ?_⟩
      simp only [hw, if_neg hb, boundAll, sub_zero, le_refl]
  choose g hg using key
  obtain ⟨n, hn⟩ := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2
  refine ⟨n, nuBetween_mono hn ?_⟩
  have hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => (hg f).2
  suffices hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith

  have hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi H, hF]; omega
  have hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ F * Mb := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => IsBig k f))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]
    calc _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), Mb := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have h := hbig τ
          push_cast at h
          rw [Finset.filter_filter]
          convert h using 2
      _ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ) := by
    unfold sumSmallSpread
    push_cast
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]
  simp only [hw]
  rw [Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]
  refine div_le_div_of_nonneg_right ?_ hp1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb := by
    have : (0 : ℝ) ≤ F * m * Mb := by positivity
    nlinarith
  linarith

end GlobalTheory.RefSum.InertOsc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.depthOscillation_large_inertPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  first | exact @GlobalTheory.RefSum.InertOsc.oscLe_inert_large | exact GlobalTheory.RefSum.InertOsc.oscLe_inert_large | (intros; apply GlobalTheory.RefSum.InertOsc.oscLe_inert_large <;> assumption)
end
end
