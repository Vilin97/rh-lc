module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

open Formalism.IrreducibleCountingLemmas.TW

section Dense

variable (l : ℕ) [Fact l.Prime]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem exists_norm_btwn (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : ∃ a : ℂ_[l], x < ‖a‖ ∧ ‖a‖ < y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := lt_trans one_pos hl1
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  set x' := max x (y / 2) with hx'
  have hx'0 : 0 < x' := lt_of_lt_of_le (half_pos hy) (le_max_right _ _)
  have hx'y : x' < y := max_lt hxy (half_lt_self hy)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((Real.logb_lt_logb_iff hl1 hx'0 hy).2 hx'y)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (l : ℂ_[l]) q.den_pos
  have hcn : ‖c‖ ^ q.den = (l : ℝ)⁻¹ := by rw [← norm_pow, hc, norm_l]
  have hc' : ‖c‖ = ((l : ℝ)⁻¹) ^ ((q.den : ℝ)⁻¹) := by
    rw [← hcn, Real.pow_rpow_inv_natCast (norm_nonneg _) q.den_ne_zero]
  have hval : ‖c ^ (-q.num)‖ = (l : ℝ) ^ (q : ℝ) := by
    rw [norm_zpow, ← Real.rpow_intCast, hc', ← Real.rpow_mul (inv_nonneg.2 hl0.le),
      Real.inv_rpow hl0.le, ← Real.rpow_neg hl0.le]
    congr 1
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hq]
    push_cast
    field_simp
  refine ⟨c ^ (-q.num), ?_, ?_⟩
  · rw [hval]
    refine lt_of_le_of_lt (le_max_left x (y / 2)) ?_
    rw [← hx']
    calc x' = (l : ℝ) ^ Real.logb l x' := (Real.rpow_logb hl0 hl1.ne' hx'0).symm
      _ < (l : ℝ) ^ (q : ℝ) := (Real.rpow_lt_rpow_left_iff hl1).2 hq1
  · rw [hval]
    calc (l : ℝ) ^ (q : ℝ) < (l : ℝ) ^ Real.logb l y := (Real.rpow_lt_rpow_left_iff hl1).2 hq2
      _ = y := Real.rpow_logb hl0 hl1.ne' hy

@[reducible] def denseC : DenselyNormedField ℂ_[l] where
  __ := (inferInstance : NormedField ℂ_[l])
  lt_norm_lt := exists_norm_btwn l

attribute [local instance] denseC

variable {l}

end Dense

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

variable {X} {k : ℕ} {ρ : ℝ}

end PtGeo

variable {D : Formalism.BasicNotions.D7}

section Places

section

variable {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]

end

end Places

section Gal

variable (X : Geo D)

end Gal

section U4

theorem norm_unif {K O : Type} [NormedField K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range) {ϖ : O} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap O K ϖ‖ ∧ ‖algebraMap O K ϖ‖ < 1 := by
  have h0 : algebraMap O K ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hϖ.ne_zero
  refine ⟨norm_pos_iff.2 h0, lt_of_le_of_ne ((hball _).2 ⟨ϖ, rfl⟩) ?_⟩
  intro h1
  have h2 : ‖(algebraMap O K ϖ)⁻¹‖ ≤ 1 := by rw [norm_inv, h1, inv_one]
  obtain ⟨a, ha⟩ := (hball _).1 h2
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one a ?_
  apply IsFractionRing.injective O K
  rw [map_mul, ha, map_one, mul_inv_cancel₀ h0]

theorem complete_of_adic {K O : Type} [NormedField K] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal O) O) : CompleteSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hr0, hr1⟩ := norm_unif hball hϖ
  set r := ‖algebraMap O K ϖ‖ with hr
  have hπ0 : algebraMap O K ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hmem : ∀ (a : O) (n : ℕ), ‖algebraMap O K a‖ ≤ r ^ n → a ∈ IsLocalRing.maximalIdeal O ^ n := by
    intro a n h
    have h1 : ‖algebraMap O K a / (algebraMap O K ϖ) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (pow_pos hr0 n)]; exact h
    obtain ⟨c, hc'⟩ := (hball _).1 h1
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, map_pow, hc', mul_div_cancel₀ _ (pow_ne_zero n hπ0)]
  have hnorm : ∀ (a : O) (n : ℕ), a ∈ IsLocalRing.maximalIdeal O ^ n → ‖algebraMap O K a‖ ≤ r ^ n := by
    intro a n h
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨c, rfl⟩ := h
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg hr0.le n) ((hball _).2 ⟨c, rfl⟩)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => r ^ n) (fun n => pow_pos hr0 n) ?_
  intro u hu
  have h1 : ∀ n, ∃ a : O, algebraMap O K a = u n - u 0 := by
    intro n
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [pow_zero, dist_eq_norm] at this
    exact (hball _).1 this.le
  choose a ha using h1
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := a) (by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply hmem
    rw [map_sub, ha, ha, sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact (hu m m n le_rfl hmn).le)
  refine ⟨u 0 + algebraMap O K L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h2
  have h3 := hnorm _ n h2
  rw [map_sub, ha] at h3
  rwa [← sub_sub]

end U4

section U4rec

variable {D : Formalism.BasicNotions.D7}

end U4rec

section ConjPlaces

end ConjPlaces

namespace SplitL

variable {R : Ranks} (H : Host R)

end SplitL

section PartC

variable {i : D.ntw.Tw} {j : ℕ} {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}

variable {δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)}
  {Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i} {φ : D.nth.Lt i j → KK i}

variable (X : Geo D)

end PartC

section U5

end U5

end Formalism.MainNotions.ExistsIdealDenominator

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]


variable (V K) in
def absOfVal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) : AbsoluteValue K ℝ where
  toFun x := if x = 0 then 0 else c ^ (vV V x)
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, vV_mul hx hy, zpow_add₀ hc0.ne']
  nonneg' x := by
    show 0 ≤ (if x = 0 then 0 else c ^ (vV V x))
    split_ifs
    · exact le_rfl
    · positivity
  eq_zero' x := by
    show (if x = 0 then 0 else c ^ (vV V x)) = 0 ↔ x = 0
    split_ifs with h
    · simp [h]
    · simp [h, zpow_ne_zero _ hc0.ne']
  add_le' x y := by
    show (if x + y = 0 then 0 else c ^ (vV V (x + y))) ≤
      (if x = 0 then 0 else c ^ (vV V x)) + (if y = 0 then 0 else c ^ (vV V y))
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    have px := zpow_pos hc0 (vV V x)
    have py := zpow_pos hc0 (vV V y)
    by_cases hxy : x + y = 0
    · simp only [hxy, hx, hy, if_true, if_false]; positivity
    simp only [hxy, hx, hy, if_false]
    rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith

theorem absOfVal_of_ne (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) {x : K} (hx : x ≠ 0) :
    absOfVal V K c hc0 hc1 x = c ^ (vV V x) := by
  show (if x = 0 then 0 else c ^ (vV V x)) = _
  simp [hx]

end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

theorem isReading_ext : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr),
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  intro p _ F _ _ φ T io k hk T' i hi j hj
  have hji : ∀ y, j (i y) = k y := fun y => by rw [← hj]; rfl
  refine ⟨fun a => by rw [RingHom.comp_apply, hji]; exact hk.comp a, fun x => ?_⟩
  obtain ⟨hfin, r, hr, hv⟩ := hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by simpa using hπ.ne_zero
  set ρ := ‖k (algebraMap T.V T.Fr π)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 ((map_ne_zero k).2 hπ0)
  have hρ1 : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv'⟩ := (hk.int _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv', map_one, mul_inv_cancel₀ hπ0]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ρ ^ ((1 : ℝ) / r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hρ0 _
  have hc1 : c < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hcr : c ^ r = ρ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  letI NF : NontriviallyNormedField T.Fr :=
    { NormedField.induced T.Fr ℂ_[p] k k.injective with
      non_trivial := ⟨(algebraMap T.V T.Fr π)⁻¹, by
        show 1 < ‖k (algebraMap T.V T.Fr π)⁻¹‖
        rw [map_inv₀, norm_inv]
        exact (one_lt_inv₀ hρ0).2 hρ1⟩ }
  have hnk : ∀ y : T.Fr, ‖y‖ = ‖k y‖ := fun y => rfl
  haveI : IsUltrametricDist T.Fr :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnk, hnk, hnk, map_add (f := _)]
      exact IsUltrametricDist.norm_add_le_max _ _
  haveI : CompleteSpace T.Fr := Formalism.MainNotions.ExistsIdealDenominator.complete_of_adic (O := T.V) (K := T.Fr) (fun y => hk.int y) inferInstance
  letI := i.toAlgebra
  haveI : FiniteDimensional T.Fr T'.Fr := hfin
  have e1 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective) (fun y => by
      show ‖j (i y)‖ = ‖y‖
      rw [hji, hnk]) x
  have e2 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := absOfVal T'.V T'.Fr c hc0 hc1.le) (fun y => by
      show absOfVal T'.V T'.Fr c hc0 hc1.le (i y) = ‖y‖
      by_cases hy : y = 0
      · subst hy; simp
      rw [absOfVal_of_ne _ _ _ ((map_ne_zero i).2 hy), hv, zpow_mul, zpow_natCast, hcr, hnk,
        norm_eq_zpow T k hk.int hπ y hy]) x
  have hx : ‖j x‖ = absOfVal T'.V T'.Fr c hc0 hc1.le x := e1.trans e2.symm
  rw [hx]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [map_zero, zero_le_one, true_iff]
    exact ⟨0, map_zero _⟩
  rw [absOfVal_of_ne _ _ _ hx0]
  change _ ↔ ∃ a : T'.V, algebraMap T'.V T'.Fr a = x
  rw [GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := one_lt_zpow_of_neg₀ hc0 hc1 hn
    linarith
  · intro h
    exact zpow_le_one₀ hc0 hc1.le h

end GlobalTheory.GeoTie.ReadExt
end
end
end
