module

public import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNormsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsPowPrincipal
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProdNormEmbeddingsEqAbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminantStatement
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelicStatement
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
import Mathlib.Tactic.Linter.Style
import Mathlib.Data.Num.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.AdelicProofs.NormEqOneOfValuationEqOne

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Place

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

noncomputable def placeOf (κ : F →+* ℂ_[p]) : HeightOneSpectrum (𝓞 F) where
  asIdeal := GlobalTheory.DatumJets.Place.smallIdeal κ
  isPrime := GlobalTheory.DatumJets.Place.smallIdeal_isPrime κ
  ne_bot := by
    intro hbot
    have hp : ((p : ℕ) : 𝓞 F) ∈ GlobalTheory.DatumJets.Place.smallIdeal κ := by
      rw [GlobalTheory.DatumJets.Place.mem_smallIdeal]
      simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)
    rw [hbot, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem mem_placeOf (κ : F →+* ℂ_[p]) (y : 𝓞 F) :
    y ∈ (placeOf κ).asIdeal ↔ ‖κ (y : F)‖ < 1 := Iff.rfl

theorem valuation_placeOf_le_one_iff (κ : F →+* ℂ_[p]) (a : F) :
    (placeOf κ).valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  ⟨fun h => GlobalTheory.MomPlace.norm_le_one_of_valuation F p κ (placeOf κ) (mem_placeOf κ) a h,
    fun h => GlobalTheory.DatumJets.Place.valuation_le_one_of_norm κ (placeOf κ) (mem_placeOf κ) a h⟩

theorem norm_eq_one_of_valuation_eq_one (κ : F →+* ℂ_[p]) {u : F}
    (hu : (placeOf κ).valuation F u = 1) : ‖κ u‖ = 1 := by
  have h1 : ‖κ u‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u).1 hu.le
  have h2 : ‖κ u⁻¹‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u⁻¹).1 (by simp [hu])
  rw [map_inv₀, norm_inv] at h2
  have h0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h3 : 0 < ‖κ u‖ := by simp [h0]
  exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)

theorem log_norm_eq_of_valuation (κ : F →+* ℂ_[p]) {π α : F} {n : ℤ}
    (hπ : (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ))
    (hα : (placeOf κ).valuation F α = WithZero.exp (-n)) (hα0 : α ≠ 0) :
    Real.log ‖κ α‖ = n * Real.log ‖κ π‖ := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hu : (placeOf κ).valuation F (α * π ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, hα, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h := norm_eq_one_of_valuation_eq_one κ hu
  rw [map_mul, map_zpow₀, norm_mul, norm_zpow] at h
  have hκπ : ‖κ π‖ ≠ 0 := by simp [hπ0]
  have hκα : ‖κ α‖ ≠ 0 := by simp [hα0]
  have h2 := congrArg Real.log h
  rw [Real.log_mul hκα (zpow_ne_zero _ hκπ), Real.log_zpow, Real.log_one] at h2
  push_cast at h2
  linarith

theorem dvd_absNorm_placeOf (κ : F →+* ℂ_[p]) :
    p ∣ Ideal.absNorm (placeOf κ).asIdeal := by
  refine GlobalTheory.DatumJets.Place.dvd_of_natCast_mem (placeOf κ).asIdeal (placeOf κ).isPrime.ne_top
    Fact.out ?_ (Ideal.absNorm_mem _)
  rw [mem_placeOf]
  simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)

end Place

theorem deg_eq_places : ∀ (F : Type) [Field F] [NumberField F] (N : LogNorms F) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]) (v : HeightOneSpectrum (𝓞 F)) (π : F), (∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → v.valuation F π = WithZero.exp (-1 : ℤ) → N.fin p κ = (r v : ℝ) * Real.log ‖κ π‖) → N.IsAdelic ∧ N.deg = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, N.inf σ) / (Module.finrank ℚ F : ℝ) := by
  intro F _ _ N r h
  obtain ⟨M, α, hM, hα, hn⟩ := exists_pow_principal F r
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hfin : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), ∃ π : F,
      N.fin p κ = (r (placeOf κ) : ℝ) * Real.log ‖κ π‖ ∧
        (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ) := by
    intro p κ
    obtain ⟨π, hπ⟩ := (placeOf κ).valuation_exists_uniformizer F
    exact ⟨π, h p κ _ π (valuation_placeOf_le_one_iff κ) hπ, hπ⟩
  have key : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), (M : ℝ) * N.fin p κ = Real.log ‖κ α‖ := by
    intro p κ
    obtain ⟨π, h1, hπ⟩ := hfin p κ
    obtain ⟨m, hm, hv⟩ := hn (placeOf κ)
    rw [log_norm_eq_of_valuation κ hπ hv hα, h1]
    have hm' : (m : ℝ) = M * (r (placeOf κ) : ℝ) := by exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hm
    rw [hm']
    ring
  have hadel : N.IsAdelic := by
    have hS : ((r.support.biUnion fun v => (Ideal.absNorm v.asIdeal).primeFactors : Finset ℕ) : Set ℕ).Finite :=
      Finset.finite_toSet _
    refine (hS.preimage (f := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn).subset ?_
    rintro p ⟨κ, hκ⟩
    obtain ⟨π, h1, -⟩ := hfin p κ
    have hr : r (placeOf κ) ≠ 0 := by
      intro h0
      exact hκ (by rw [h1, h0]; simp)
    simp only [Set.mem_preimage, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Nat.mem_primeFactors]
    refine ⟨placeOf κ, Finsupp.mem_support_iff.2 hr, p.2, dvd_absNorm_placeOf κ, ?_⟩
    have := NumberField.HeightOneSpectrum.one_lt_absNorm (placeOf κ)
    omega
  refine ⟨hadel, ?_⟩
  let n : HeightOneSpectrum (𝓞 F) →₀ ℤ := r.mapRange (fun q => ⌊(M : ℚ) * q⌋) (by simp)
  have hnv : ∀ v, ((n v : ℤ) : ℚ) = M * r v := by
    intro v
    obtain ⟨m, hm, -⟩ := hn v
    simp [n, ← hm]
  have hn' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v)) := by
    intro v
    obtain ⟨m, hm, hv⟩ := hn v
    have : n v = m := by
      have := hnv v
      rw [← hm] at this
      exact_mod_cast this
    rw [this]
    exact hv
  have h1 := sum_log_embeddings_eq F n α hα hn'
  have h2 := (GlobalTheory.T.product_formula_log_norms F α hα).2
  have h3 : ∀ p, (LogNorms.ofElt α).finSum p = M * N.finSum p := by
    intro p
    simp only [LogNorms.finSum, LogNorms.ofElt, Finset.mul_sum, key]
  have hsupp : (Function.support N.finSum).Finite := by
    refine Set.Finite.subset hadel ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
    exact hp (by simp [LogNorms.finSum, hc])
  have h4 : ∑ᶠ p, (LogNorms.ofElt α).finSum p = M * ∑ᶠ p, N.finSum p := by
    simp_rw [h3]
    rw [mul_finsum]
  have h5 : (n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) =
      M * r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h6 : ((⌊(M : ℚ) * r v⌋ : ℤ) : ℝ) = M * (r v : ℝ) := by
      have h7 := hnv v
      have h8 : n v = ⌊(M : ℚ) * r v⌋ := by simp [n]
      rw [h8] at h7
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) h7
    rw [h6]
    ring
  have h6 : ∑ᶠ p, N.finSum p = -(r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) := by
    apply mul_left_cancel₀ hMR
    rw [← h4, mul_neg, ← h5, ← h1]
    linarith
  rw [LogNorms.deg, h6]
  congr 1
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.LogIdealNonpos

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Num

theorem value_bound (p q : ℕ) (l L : ℝ) (h7 : Real.log 7 / 2 ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := OnHodge.const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a1], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a2]⟩
  push_cast
  nlinarith

theorem near_of (n : ℕ) (bad : Finset ℕ) (h2 : 2 ∈ bad) (rd L h₀ : ℝ) (d v : ℕ → ℝ)
    (hb : |h₀| + (n : ℝ) * Real.log 2 ≤ (n : ℝ) * (3 / 2 * Real.log rd + |L| / 2))
    (hd : ∀ r ∈ bad, 0 ≤ v r ∧ |d r| ≤ ((n : ℝ) * cP r + (n : ℝ) * v r) * Real.log r)
    (hv : ∑ r ∈ bad, v r * Real.log r ≤ Real.log rd) : NearRecord n bad rd L (h₀ + ∑ r ∈ bad, d r) := by
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 ≤ N * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le
  obtain ⟨hv2, hd2⟩ := hd 2 h2
  have hv2' := mul_nonneg hN0 hv2
  simp only [cP, if_true, Nat.cast_ofNat] at hd2
  obtain ⟨e, he, he'⟩ : ∃ e : ℝ, |e| ≤ N * Real.log 2 ∧ |d 2 - e| ≤ (N + N * v 2) * Real.log 2 := by
    rw [abs_le] at hd2
    rcases le_total 0 (d 2) with h | h
    · exact ⟨N * Real.log 2, (abs_of_nonneg hN0).le, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
    · exact ⟨-(N * Real.log 2), by rw [abs_neg, abs_of_nonneg hN0], abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  refine ⟨_ + e, fun r => d r - if r = 2 then e else 0, v, (abs_add_le _ _).trans ((add_le_add le_rfl he).trans hb), ?_,
    fun r hr => ⟨(hd r hr).1, ?_⟩, hv⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' bad 2, if_pos h2]; ring
  · by_cases h : r = 2
    · subst h
      have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
      simp only [if_true, this, div_one]
      exact_mod_cast he'
    · have := (hd r hr).2
      simp only [cP, if_neg h] at this ⊢
      rwa [sub_zero, div_eq_mul_one_div]

def extP (g : Nat.Primes → ℝ) (n : ℕ) : ℝ := if h : n.Prime then g ⟨n, h⟩ else 0

theorem extendFromPrimes_coe (g : Nat.Primes → ℝ) (ℓ : Nat.Primes) : extP g ℓ = g ℓ := dif_pos ℓ.2

theorem exists_primes (bad : Finset ℕ) (hb : ∀ ℓ ∈ bad, ℓ.Prime) :
    ∃ B : Finset Nat.Primes, (∀ ℓ, ℓ ∈ B ↔ (ℓ : ℕ) ∈ bad) ∧ ∀ G : ℕ → ℝ, ∑ ℓ ∈ bad, G ℓ = ∑ ℓ ∈ B, G ℓ := by
  refine ⟨bad.preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) Subtype.val_injective.injOn, fun ℓ => Finset.mem_preimage,
    fun G => ?_⟩
  exact (Finset.sum_preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) bad Subtype.val_injective.injOn G
    fun x hx hn => absurd ⟨⟨x, hb x hx⟩, rfl⟩ hn).symm

theorem place_eq {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (κ : F →+* ℂ_[p])
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) : v = placeOf κ := by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [h, valuation_placeOf_le_one_iff]

theorem logIdeal_nonpos {E : Type} [Field E] [NumberField E] (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≤ 0 := by
  obtain ⟨a, -, -, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    (j.injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
  rw [e]
  refine Real.log_nonpos (norm_nonneg _) ?_
  exact (valuation_placeOf_le_one_iff j (a : E)).1 ((placeOf j).valuation_le_one a)

end Num

open Num in
theorem numerics : Numerics := by
  intro E _ _ _ H p q F F' _ _ _ _ ι σ N r bad hσ h2 hbp hAd hdeg hloc
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  let N' : LogNorms F' := ⟨fun s => N.inf (s.comp ι), fun ℓ κ' => (r (placeOf κ') : ℝ) * Real.log ‖κ' (π (placeOf κ'))‖⟩
  obtain ⟨hAd', hdeg'⟩ := deg_eq_places F' N' r (by
    intro ℓ κ' v π' hv hπ'
    obtain rfl := place_eq κ' v hv
    have h0 : π' ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have := log_norm_eq_of_valuation κ' (n := 1) (hπ _) hπ' h0
    show _ * _ = _
    rw [this]
    simp)
  have hgoal : ((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
      (Module.finrank ℚ F' : ℝ) = N'.deg := hdeg'.symm
  rw [hgoal]
  obtain ⟨hext, hextA⟩ := GlobalTheory.T.logNorms_ext_degree_adelic F F' ι N
  have hAdx : (N.ext ι).IsAdelic := hextA.2 hAd
  have hl := fun (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) =>
    hloc ℓ κ' (placeOf κ') (π _) (valuation_placeOf_le_one_iff κ') (hπ _)
  have hn' : (0 : ℝ) < Module.finrank ℚ F' := by exact_mod_cast Module.finrank_pos
  have hnE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  obtain ⟨B, hB, hBs⟩ := exists_primes bad hbp
  let f : E →+* F' := IsFractionRing.lift (A := 𝓞 E) (g := ι.comp σ) (ι.injective.comp hσ)
  have hf : ∀ a : 𝓞 E, f (algebraMap (𝓞 E) E a) = ι (σ a) := fun a => IsFractionRing.lift_algebraMap _ a
  let g : Nat.Primes → ℝ := fun ℓ => -(N'.finSum ℓ - (N.ext ι).finSum ℓ) / Module.finrank ℚ F'
  let w : Nat.Primes → ℝ := fun ℓ =>
    -∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => neg_nonneg.2 (Finset.sum_nonpos fun j _ => logIdeal_nonpos ℓ j)
  have hlog : ∀ ℓ : Nat.Primes, 0 < Real.log (ℓ : ℕ) := fun ℓ => Real.log_pos (by exact_mod_cast ℓ.2.one_lt)
  have hsupp : ∀ M : LogNorms F', M.IsAdelic → (Function.support M.finSum).Finite := fun M hM =>
    Set.Finite.subset hM fun ℓ hℓ => by
      by_contra hc
      simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
      exact hℓ (by simp [LogNorms.finSum, hc])
  have hsplit : N'.deg = N.deg + ∑ ℓ ∈ bad, extP g ℓ := by
    rw [hBs, ← hext]
    simp only [extendFromPrimes_coe, g]
    have e1 : ∑ᶠ ℓ, (N'.finSum ℓ - (N.ext ι).finSum ℓ) = ∑ ℓ ∈ B, (N'.finSum ℓ - (N.ext ι).finSum ℓ) := by
      refine finsum_eq_sum_of_support_subset _ fun ℓ hℓ => ?_
      by_contra hc
      refine hℓ (sub_eq_zero.2 (Finset.sum_congr rfl fun κ' _ => ?_))
      exact (hl ℓ κ').1 fun h => hc ((hB ℓ).2 h)
    rw [finsum_sub_distrib (hsupp _ hAd') (hsupp _ hAdx)] at e1
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← e1]
    have e2 : ∑ s, N'.inf s = ∑ s, (N.ext ι).inf s := rfl
    simp only [LogNorms.deg]
    rw [e2]
    ring
  rw [hsplit]
  have hrd : hostRd E = rootDiscr E := OnHodge.hostRd_eq E
  refine near_of (p + q) bad h2 _ _ _ _ (extP fun ℓ => w ℓ / Module.finrank ℚ E / Real.log (ℓ : ℕ)) ?_ ?_ ?_
  · rw [hdeg]
    refine value_bound p q _ _ ?_
    have h7 : (7 : ℝ) ≤ H.d := by
      have := H.d_mod
      have : 7 ≤ H.d := by omega
      exact_mod_cast this
    have h1 := (GlobalTheory.T.sqrt_discriminant_bounds_cm_field E H).2
    rw [hrd, ← Real.log_sqrt (by norm_num)]
    exact Real.log_le_log (Real.sqrt_pos.2 (by norm_num)) ((Real.sqrt_le_sqrt h7).trans h1)
  · intro n hn
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Nat.Primes, (ℓ : ℕ) = n := ⟨⟨n, hbp n hn⟩, rfl⟩
    rw [extendFromPrimes_coe, extendFromPrimes_coe]
    refine ⟨div_nonneg (div_nonneg (hw0 ℓ) hnE.le) (hlog ℓ).le, ?_⟩
    have hk : ∀ κ' : F' →+* ℂ_[ℓ], |N'.fin ℓ κ' - (N.ext ι).fin ℓ κ'| ≤ ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) -
        logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := fun κ' => by
      obtain ⟨a, ha, ha0, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
        ((κ'.comp f).injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
      rw [e, RingHom.comp_apply, RingHom.comp_apply, hf]
      exact (hl ℓ κ').2 hn a ha ha0
    have hfib := GlobalTheory.T.sum_embeddings_base_change E F' ℂ_[ℓ] f
      fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    have hs : |N'.finSum ℓ - (N.ext ι).finSum ℓ| ≤ ((p + q : ℕ) : ℝ) * (Module.finrank ℚ F' * (cP ℓ * Real.log (ℓ : ℕ)) -
        ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
      simp only [LogNorms.finSum]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun κ' _ => hk κ').trans (le_of_eq ?_))
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
    have hS : ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        -(Module.finrank ℚ F' * (w ℓ / Module.finrank ℚ E)) := by
      apply mul_left_cancel₀ hnE.ne'
      rw [hfib]
      simp only [w]
      field_simp
    rw [hS] at hs
    simp only [g]
    rw [abs_div, abs_neg, abs_of_pos hn', div_le_iff₀ hn']
    refine hs.trans (le_of_eq ?_)
    have := (hlog ℓ).ne'
    field_simp
    ring
  · rw [hBs]
    simp only [extendFromPrimes_coe]
    obtain ⟨hfin, hsum⟩ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hwf : (Function.support w).Finite := hfin.subset fun ℓ hℓ => fun h => hℓ (by simp only [w]; rw [h, neg_zero])
    have hws : ∑ᶠ ℓ, w ℓ = Module.finrank ℚ E * Real.log (rootDiscr E) := by
      simp only [w]
      rw [finsum_neg_distrib, hsum]
      ring
    have hle : ∑ ℓ ∈ B, w ℓ ≤ ∑ᶠ ℓ, w ℓ := by
      rw [finsum_eq_sum_of_support_subset w (s := B ∪ hwf.toFinset) (fun ℓ hℓ => by simp [hℓ])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun ℓ _ _ => hw0 ℓ
    rw [Finset.sum_congr rfl fun ℓ _ => div_mul_cancel₀ _ (hlog ℓ).ne', ← Finset.sum_div, div_le_iff₀ hnE, hrd]
    linarith

end RootFieldNumerics.RF
end
end
end
