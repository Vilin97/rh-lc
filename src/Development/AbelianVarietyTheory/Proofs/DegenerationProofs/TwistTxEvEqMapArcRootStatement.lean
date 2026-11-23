module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum

section

@[expose] public section

open Module

namespace GlobalTheory

theorem hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by
  intro O K Z _ _ _ _ φ h1 hX deg hfin a
  classical
  set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF
  have key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) →
      ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖
        ≤ ‖φ PowerSeries.X‖ ^ n := by
    intro n s hs
    have hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣
        (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm

      rw [map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]
      have : (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z := by
        rw [← finsum_mem_coe_finset]
        refine finsum_congr fun z => ?_
        refine finsum_congr_Prop ?_ (fun _ => rfl)
        apply propext
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : deg z = m
      · simp [h]
      · simp [h, Ne.symm h]
    obtain ⟨g, hg⟩ := hdvd
    have h2 := congrArg φ hg

    simp only [map_sub, map_sum, map_mul, map_pow] at h2
    rw [h2, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (h1 g)
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hX
  have hfn : {z | deg z < n}.Finite := by
    refine ((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    exact ⟨deg z, hz, rfl⟩
  simp only [SummationFilter.unconditional_filter]
  filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs
  rw [dist_eq_norm]
  exact (key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.twist_terms_alt : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) := by
  first | exact @GlobalTheory.Ex.twist_terms | exact GlobalTheory.Ex.twist_terms | (intros; apply GlobalTheory.Ex.twist_terms <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArc

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem hasSum_zpow_of_form_le {O C X : Type} [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (φ : PowerSeries O →+* C) (h1 : ∀ f, ‖φ f‖ ≤ 1) (hX : ‖φ PowerSeries.X‖ < 1) (u : Cˣ)
    (hu : (u : C) = φ PowerSeries.X) (B : LinearMap.BilinForm ℤ X) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (y : X) {m : ℕ} (hm : m ≠ 0) {D : ℤ} (hD : 0 < D) (E : X → ℤ)
    (hE : ∀ χ, B (y + m • χ) (y + m • χ) ≤ D * E χ) (a : X → O) :
    HasSum (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ)))
      (φ (PowerSeries.mk fun n => ∑ᶠ (χ : X) (_ : E χ = n), a χ)) := by
  classical
  have hB0 : ∀ x, 0 ≤ B x x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  have hE0 : ∀ χ, 0 ≤ E χ := by
    intro χ
    have h := hE χ
    have h' := hB0 (y + m • χ)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hinj : Function.Injective (fun χ : X => y + m • χ) := by
    intro a b h
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (Int.natCast_ne_zero.mpr hm) h'
  have hQ := GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef hs hp
  have hfin : ∀ n : ℕ, {χ | (E χ).toNat = n}.Finite := by
    intro n
    refine (Set.Finite.preimage (fun _ _ _ _ h => hinj h)
      (GlobalTheory.ClassMin.finite_sublevel hQ ((D * n : ℤ) : ℝ))).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq] at hχ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
    have h := hE χ
    have h0 := hE0 χ
    have h2 := hB0 (y + m • χ)
    have hEn : E χ = n := by omega
    rw [hEn] at h
    have h3 : (B (y + m • χ) (y + m • χ) : ℝ) ≤ ((D * n : ℤ) : ℝ) := by exact_mod_cast h
    have h4 : (0 : ℝ) ≤ B (y + m • χ) (y + m • χ) := by exact_mod_cast h2
    linarith
  have h := GlobalTheory.hasSum_map_powerSeries_mk_finsum O C X φ h1 hX (fun χ => (E χ).toNat) hfin a
  have hf : (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ))) =
      fun χ => φ (PowerSeries.C (a χ)) * φ PowerSeries.X ^ (E χ).toNat := by
    funext χ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (hE0 χ)
    rw [hk]
    simp [hu, mul_comm]
  have hg : (fun n : ℕ => ∑ᶠ (χ : X) (_ : E χ = n), a χ) =
      fun n : ℕ => ∑ᶠ (χ : X) (_ : (E χ).toNat = n), a χ := by
    funext n
    refine finsum_congr fun χ => ?_
    have h0 := hE0 χ
    have hiff : (E χ = n) = ((E χ).toNat = n) := propext (by omega)
    rw [hiff]
  rw [hf, hg]
  exact h

theorem form_le_exponent {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by
  have hB0 : ∀ y, 0 ≤ β.be y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (β.pos y hy).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hk : k = 0 := by simpa using hm
    have h0 : β.be x x = 0 := by
      have h := β.dvd x x
      simpa [hk] using h
    simp [h0]
  · have hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ) := mul_dvd_mul_left 2 (by exact_mod_cast hm)
    have hjk : (j : ℤ) ∣ 2 * (k : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hj) 2
    obtain ⟨q, hq⟩ := dvd_trans hmk (β.dvd x x)
    obtain ⟨c, hc⟩ := dvd_trans hjk (β.dvd z x)
    have hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hq' : β.be x x / (2 * m ^ 2) = q := by
      rw [hq]
      exact Int.mul_ediv_cancel_left q hm2.ne'
    have hc' : β.be z x / j = c := by
      rw [hc]
      exact Int.mul_ediv_cancel_left c (by omega)
    rw [hq', hc']
    have hexp := hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp
    rw [β.symm x z, hc] at hexp
    have ha := hB0 z
    have hs0 : 0 ≤ s := le_trans (mul_nonneg (by positivity) ha) hs
    have hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1 := by nlinarith
    have h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z)) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))
    have key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s) := by
      nlinarith [hexp, h5]
    have hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg
      linarith
    nlinarith [hX, hq]

theorem twist_tx_ev_eq_map_arc : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2
  have hm0 : m ≠ 0 := hmo.pos.ne'
  have hT := (GlobalTheory.T.hom_transport_alt O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2
  have hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀) := by
    intro χ₀
    rw [hp1, map_add (f := _), map_nsmul]
  have hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y := fun x y =>
    dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)
  have hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  constructor
  · have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2))
      (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)
    have key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) =
        (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) :
          Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]
      ring
    show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr
      (hsum.mul_left (I.lam : C))
  · intro j hj q₀ q hj0 hq1 hq2 s hs
    have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0
      (D := 4 * (m : ℤ) ^ 2) (by positivity)
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s)
      (fun χ => form_le_exponent β₀ hm hj hj0 _ _ (s : ℤ) hs) (fun χ => N₀.evT m p₀ q₀.1.2 χ)
    have key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) =
        ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
          (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) +
            β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C) *
            φ (PowerSeries.C (N₀.evT m p₀ q₀.1.2 χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ,
        (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]
      simp only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _
    rw [← tsum_mul_left]
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
      φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr
      (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))

end GlobalTheory.Ex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  first | exact @GlobalTheory.Ex.twist_tx_ev_eq_map_arc | exact GlobalTheory.Ex.twist_tx_ev_eq_map_arc | (intros; apply GlobalTheory.Ex.twist_tx_ev_eq_map_arc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcRoot

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RootSum

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) : N.Form n where
  be := (n : ℤ) • β.be
  symm y z := congrArg ((n : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hn) (β.pos y hy)
  dvd y z := by
    obtain ⟨a, ha⟩ := β.dvd y z
    exact ⟨k * a, by change (n : ℤ) * β.be y z = _; rw [ha]; ring⟩

def pullForm {O O' : Type} [CommRing O] [CommRing O'] {N₀ : NumD O} {N : NumD O'} {k : ℕ} (β : N.Form k)
    (e : N₀.X ≃+ N.X) (be₀ : LinearMap.BilinForm ℤ N₀.X) (h : ∀ y z, β.be (e y) (e z) = be₀ y z) : N₀.Form k where
  be := be₀
  symm y z := by rw [← h, ← h, β.symm]
  pos y hy := by rw [← h]; exact β.pos _ (fun h0 => hy (e.map_eq_zero_iff.1 h0))
  dvd y z := h y z ▸ β.dvd _ _

def idHom {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u : Oˣ)
    (h : t ^ n = u) : NumD.Hom (RingHom.id O) (N.twist (scaleForm β n hn) t) (N.twist β u) where
  φ := MonoidHom.id _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp only [mul_one]; rfl
  σ_eq _ := by simp only [mul_one]; rfl
  lam := 1
  th_eq _ := by simp only [mul_one, Units.val_one, one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq (χ : N.X) := by
    rw [mul_one]
    change N.ψ χ * u ^ (β.be χ χ / 2) = N.ψ χ * t ^ ((n : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, h]

theorem idHom_rel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u r : Oˣ)
    (h : t ^ n = u) {i : ℕ} (a : ℕ) (hi : i * a = n) (hd : i ∣ n) (hr : t ^ a = r) (p₁ : N.QT i)
    (p : (N.twist β u).QT i) (hp : TwRel β u r p₁ p) :
    p.1.1.toAdd = (idHom β n hn t u h).e (N.twQ (scaleForm β n hn) t hd p₁).1.1.toAdd ∧
      (idHom β n hn t u h).Rel (N.twQ (scaleForm β n hn) t hd p₁).1.2 p.1.2 := by
  refine ⟨congrArg Multiplicative.toAdd hp.1, hp.2.1, fun (χ : N.X) => ?_⟩
  change p.1.2.s χ * 1 = p₁.1.2.s χ * t ^ ((n : ℤ) * β.be p₁.1.1.toAdd χ / i) * 1 * 1
  have hi0 : (i : ℤ) ≠ 0 := by
    rintro h0
    rw [Int.natCast_eq_zero.1 h0, zero_mul] at hi
    omega
  rw [hp.2.2, ← hi, Nat.cast_mul, mul_assoc (i : ℤ), Int.mul_ediv_cancel_left _ hi0, zpow_mul, zpow_natCast, hr,
    mul_one, mul_one]

theorem twist_tx_ev_eq_map_arc_root : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 h2 t u rm rj m j hm hj ht hrm hrj hu N₀ N I k be₀ β hβ p₀ p₁ p hp1 hp2 hp
  have hn : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  have htu : t ^ (m ^ 2 * j) = u := by rw [mul_comm, pow_mul, hrm, hu]
  have hd : m ^ 2 ∣ m ^ 2 * j := Dvd.intro _ rfl
  have key := GlobalTheory.T.twist_tx_ev_eq_map_arc_alt O C φ h1 h2 t ht N₀ N I (m ^ 2 * j) (scaleForm (pullForm β I.e be₀ hβ) _ hn)
    (scaleForm β _ hn) (fun y z => congrArg (((m ^ 2 * j : ℕ) : ℤ) * ·) (hβ y z)) m hd hm p₀ p₁ hp1 hp2
  have hr := idHom_rel β _ hn t u rm htu j rfl hd hrm p₁ p hp
  have tr := (NumD.hom_transport C C _ _ _ (idHom β _ hn t u htu)).2.2.2.2 m hm _ p hr.1 hr.2
  refine ⟨Eq.trans (tsum_congr fun χ => ?_) key.1, fun q₀ q₁ q hq1 hq2 hq s hs => ?_⟩
  · exact (tr χ).1.trans (one_mul _)
  · have hd' : j ∣ m ^ 2 * j := Dvd.intro_left _ rfl
    have hr' := idHom_rel β _ hn t u rj htu (m ^ 2) (mul_comm _ _) hd' hrj q₁ q hq
    refine Eq.trans (congrArg _ (tsum_congr fun χ => ?_)) (key.2 j hd' q₀ q₁ hj.ne' hq1 hq2 s hs)
    refine ((tr χ).2 _ _ hr'.2).trans ?_
    change ((1 * 1 ^ (m ^ 2) : Cˣ) : C) * _ = _
    rw [one_pow, mul_one, Units.val_one, one_mul]
    rfl

end GlobalTheory.Ex.RootSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcRootStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  first | exact @GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root | exact GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root | (intros; apply GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root <;> assumption)
end
end
