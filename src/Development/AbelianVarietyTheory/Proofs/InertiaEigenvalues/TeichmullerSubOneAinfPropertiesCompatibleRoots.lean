module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishingStatement
public import Mathlib.RingTheory.WittVector.Basic
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
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorDvdOfSaturatedIdeal

section

@[expose] public section

namespace GlobalTheory

open WittVector

theorem wittVector_coeff_pow_mul_eq_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by
  intro m
  induction m with
  | zero => intro t j hj; omega
  | succ m ih =>
    intro t j hj
    have h : (l : WittVector l R) ^ (m + 1) * t
        = verschiebung (frobenius ((l : WittVector l R) ^ m * t)) := by
      rw [verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact verschiebung_coeff_zero _
    | succ j =>
      rw [verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]
      exact zero_pow hl.out.ne_zero

theorem wittVector_coeff_add_pow_mul {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] (x t : WittVector l R) (m j : ℕ) (hj : j < m) :
    (x + (l : WittVector l R) ^ m * t).coeff j = x.coeff j := by
  have h0 : truncate m ((l : WittVector l R) ^ m * t) = 0 := by
    ext i
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact wittVector_coeff_pow_mul_eq_zero m t i i.2
  have h1 : truncate m (x + (l : WittVector l R) ^ m * t) = truncate m x := by
    rw [map_add (f := _), h0, add_zero]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨j, hj⟩ y) h1
  simpa only [WittVector.coeff_truncate] using this

theorem wittVector_dvd_of_coeff_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] [PerfectRing R l] (x : WittVector l R) (hx : x.coeff 0 = 0) :
    ∃ y, x = (l : WittVector l R) * y := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := exists_eq_pow_p_mul x h
  cases m with
  | zero => rw [pow_zero, one_mul] at hxb; exact absurd (hxb ▸ hx) hb
  | succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩

theorem wittVector_dvd_of_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by
  intro l _ R _ _ _ J μ hμ hsat hdiv a ha

  have step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J,
      (d : WittVector l R) = μ * c + (l : WittVector l R) * d' := by
    intro d
    obtain ⟨c₀, hc₀⟩ := hdiv d d.2
    set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef
    have hx0 : x.coeff 0 = 0 := by
      have e : (d : WittVector l R) = x + μ * teichmuller l c₀ := by rw [hxdef]; ring
      have h2 := congrArg (fun y : WittVector l R => y.coeff 0) e
      simp only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2
      rw [hc₀] at h2
      linear_combination -h2
    obtain ⟨y, hy⟩ := wittVector_dvd_of_coeff_zero x hx0
    have hyJ : y ∈ J := by
      apply hsat
      rw [← hy, hxdef]
      exact J.sub_mem d.2 (J.mul_mem_right _ hμ)
    refine ⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩
    rw [← hy, hxdef]; ring
  choose cf df hcd using step
  let seq : ℕ → J := fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n
  let s : ℕ → WittVector l R := fun n =>
    ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)
  have hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n) := by
    intro n; simp only [s, Finset.sum_range_succ]
  have hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : (seq (n + 1)).1 = (df (seq n)).1 := rfl
      rw [hs_succ, e]
      have := hcd (seq n)
      rw [ih, this]; ring
  have hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨0, by ring⟩
    | succ m hnm ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩
      rw [hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]; ring
  let c : WittVector l R := WittVector.mk l (fun k => (s (k + 1)).coeff k)
  refine ⟨c, ?_⟩
  ext k

  have htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1)) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    obtain ⟨t, ht⟩ := hstab ((i : ℕ) + 1) (k + 1) (by omega)
    show (s ((i : ℕ) + 1)).coeff i = _
    rw [ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]
  have hta : truncate (k + 1) a = truncate (k + 1) (μ * c) := by
    have e := hmain (k + 1)
    have h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1)
        = 0 := by
      ext i
      rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      exact wittVector_coeff_pow_mul_eq_zero _ _ i i.2
    conv_lhs => rw [e]
    rw [map_add (f := _), h0, add_zero, map_mul, map_mul, htc]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta
  simpa only [WittVector.coeff_truncate] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorDvdOfSaturatedIdealStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J → (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) → ∀ a ∈ J, μ ∣ a := by
  first | exact @GlobalTheory.wittVector_dvd_of_saturated_ideal | exact GlobalTheory.wittVector_dvd_of_saturated_ideal | (intros; apply GlobalTheory.wittVector_dvd_of_saturated_ideal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_eq {ε δ : OCb l} (h : δ ^ l = ε) : δ = (frobeniusEquiv (OCb l) l).symm ε := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, ← h]
  rfl

theorem coeff_zero_muOf (x : OCb l) : (muOf x).coeff 0 = x - 1 := by
  change WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem frob_iterate_muOf (x : OCb l) (n : ℕ) :
    WittVector.frobenius^[n] (muOf x) = muOf (x ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]

theorem theta_muOf (x : OCb l) : Per.θ l (muOf x) = x.untilt - 1 := by
  rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]


variable (l) in
def kerAll : Ideal (Ainf l) := ⨅ n : ℕ, RingHom.ker ((Per.θ l).comp (WittVector.frobenius ^ n))

theorem mem_kerAll (a : Ainf l) : a ∈ kerAll l ↔ ∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0 := by
  simp only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]

theorem muOf_mem_kerAll {x : OCb l} (hx : x.untilt = 1) : muOf x ∈ kerAll l := by
  rw [mem_kerAll]
  intro n
  rw [frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]

theorem kerAll_sat (a : Ainf l) (h : (l : Ainf l) * a ∈ kerAll l) : a ∈ kerAll l := by
  rw [mem_kerAll] at h ⊢
  intro n
  have h1 := h n
  rw [← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)

theorem isEps_mem {ε : OCb l} (hε : IsEps ε) :
    GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hδ1⟩ := hε
  exact ⟨h1, by rw [← root_eq hδ]; exact hδ1⟩

theorem ne_one {ε : OCb l} (hε : IsEps ε) : ε ≠ 1 := by
  obtain ⟨-, δ, hδ, hδ1⟩ := hε
  rintro rfl
  have : δ = 1 := by rw [root_eq hδ, map_one]
  exact hδ1 (by rw [this, map_one])

theorem muOf_dvd {ε : OCb l} (hε : IsEps ε) {x : OCb l} (hx : x.untilt = 1) : muOf ε ∣ muOf x :=
  GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat
    (fun a ha => by rw [coeff_zero_muOf]; exact GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAll hx)

theorem muOf_ne_zero {ε : OCb l} (hε : IsEps ε) : muOf ε ≠ 0 := fun h => by
  have := congrArg (fun y : Ainf l => y.coeff 0) h
  simp only [coeff_zero_muOf, WittVector.zero_coeff] at this
  exact ne_one hε (sub_eq_zero.1 this)

theorem σA_muOf (g : GQ l) (x : OCb l) : Per.σA g (muOf x) = muOf (Per.σF g x) := by
  rw [muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]

theorem untilt_σF_eq {x : OCb l} (hx : x.untilt = 1) (g : GQ l) : (Per.σF g x).untilt = 1 := by
  rw [GlobalTheory.RingBasics.untilt_σF, hx, map_one]

end GlobalTheory.MuOfEps

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  exact ⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩

theorem units_σA {ε : OCb l} (hε : IsEps ε) (g : GQ l) :
    ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε := by
  obtain ⟨a, ha⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g)
  obtain ⟨b, hb⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)
  rw [← σA_muOf] at ha hb
  have h : muOf ε = Per.σA g b * a * muOf ε := by
    have := congrArg (Per.σA g) hb
    rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha] at this
    linear_combination this
  have h1 : Per.σA g b * a = 1 := by
    have h2 : (Per.σA g b * a - 1) * muOf ε = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))
  refine ⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩
  rw [ha, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  intro l _
  refine ⟨exists_isEps l, fun ε δ hε hδ => ?_⟩
  have hr := root_eq hδ
  have hE := isEps_mem hε
  refine ⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε,
    fun x hx => muOf_dvd hε hx⟩
  · rw [GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]
  · rw [muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, hδ]
  · rw [theta_muOf, sub_ne_zero]
    obtain ⟨-, δ', hδ', hδ'1⟩ := hε
    rwa [root_eq hδ', ← hr] at hδ'1
  · exact GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)
  · refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
    have h0 : (muOf ε).coeff 0 = 0 :=
      IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
    rw [coeff_zero_muOf] at h0
    exact ne_one hε (sub_eq_zero.1 h0)

end GlobalTheory.MuOfEps

end
end
end
