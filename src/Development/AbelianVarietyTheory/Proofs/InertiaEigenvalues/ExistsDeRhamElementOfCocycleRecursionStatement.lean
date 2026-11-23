module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
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
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfCocycleRecursionOfFrobeniusTwistStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowMulInvPowMemAinfFilLatticeStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTowerStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvIoPi

section

@[expose] public section

namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.MemLoc GlobalTheory.ThetaTie
open scoped Formalism.Per

theorem exists_inv_io_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  intro l _ P AI T
  obtain ⟨-, -, hun, hth, -⟩ := thetaD_props l
  have hθ : Per.θ l AI.π₁ ≠ 0 := by
    have h : Per.θ l AI.π₁ = PreTilt.untilt AI.ε1 - 1 := by
      rw [LocAinf.π₁, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
    rw [h]
    exact sub_ne_zero.2 (isEps AI).2
  have hne : Per.θD l (aDp l AI.π₁) ≠ 0 := by
    rw [hth]
    exact fun h0 => hθ (Subtype.ext h0)
  obtain ⟨v, hv⟩ := (hun _ hne).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v),
    (fil_zero T _).2 ⟨v, (T.eD.apply_symm_apply _).symm⟩, T.eD.injective ?_⟩
  rw [map_mul, io_apply, eD_ιA, T.eD.apply_symm_apply, ← map_mul, hv, map_one, map_one]

end GlobalTheory.ExpImage
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvIoPiStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_inv_io_pi_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  first | exact @GlobalTheory.ExpImage.exists_inv_io_pi | exact GlobalTheory.ExpImage.exists_inv_io_pi | (intros; apply GlobalTheory.ExpImage.exists_inv_io_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLat

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_Ainf_series_limit (l : ℕ) [Fact l.Prime] (a : ℕ → Ainf l) :
    ∃ x : Ainf l, ∀ n : ℕ, ∃ y : Ainf l,
      x - ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i = ((l : ℕ) : Ainf l) ^ n * y := by
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : Ainf l)}) (Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  have key : ∀ (n : ℕ) (u v : Ainf l),
      u ≡ v [SMOD ((Ideal.span {((l : ℕ) : Ainf l)}) ^ n • ⊤ : Submodule (Ainf l) (Ainf l))] ↔
        ((l : ℕ) : Ainf l) ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨x, hx⟩ := hc.toIsPrecomplete.prec
    (f := fun n => ∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi =>
        Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.mp hi).1) _)
  refine ⟨x, fun n => ?_⟩
  have := hx n
  rw [key, ← dvd_neg, neg_sub] at this
  exact this

theorem exists_series_limit_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ)
    (c : ℕ → P.R.BdR) (h0 : ∀ k, c k ∈ FilB P 0)
    (hc : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) :
    ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀,
      b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  choose k hk using hc
  let K : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (n + 1), k i
  have hK1 : ∀ n, k n ≤ K n := fun n => by
    simp only [K, Finset.sum_range_succ]
    omega
  have hK2 : ∀ n, K n ≤ K (n + 1) := fun n => by
    simp only [K, Finset.sum_range_succ k (n + 1)]
    omega
  have hblock : ∀ n R, K n ≤ R →
      ∑ j ∈ Finset.range R, c j - ∑ j ∈ Finset.range (K n), c j ∈ Lat AI M n := by
    intro n R hR
    rw [← Finset.sum_Ico_eq_sub _ hR]
    exact AddSubgroup.sum_mem _ fun j hj => hk n j ((hK1 n).trans (Finset.mem_Ico.mp hj).1)
  choose a ha using fun n => (mem_Lat AI).mp (hblock n (K (n + 1)) (hK2 n))
  have htel : ∀ n, ∑ j ∈ Finset.range (K n), c j - ∑ j ∈ Finset.range (K 0), c j -
      io AI (∑ i ∈ Finset.range n, ((l : ℕ) : Ainf l) ^ i * a i) ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (ha n)
      rw [Finset.sum_range_succ (fun i => ((l : ℕ) : Ainf l) ^ i * a i), map_add (f := _)]
      convert this using 1
      ring
  obtain ⟨x, hx⟩ := exists_Ainf_series_limit l a
  refine ⟨∑ j ∈ Finset.range (K 0), c j + io AI x,
    add_mem (Submodule.sum_mem _ fun j _ => h0 j) (io_mem AI x), fun n => ⟨K n, fun R hR => ?_⟩⟩
  obtain ⟨y, hy⟩ := hx n
  have h1 := io_mem_Lat AI M n y
  rw [← hy, map_sub] at h1
  have := sub_mem (sub_mem h1 (FilB_le_Lat AI (n := n) (htel n))) (hblock n R hR)
  convert this using 1
  ring

end GlobalTheory.ExpImage
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLatStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_series_limit_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ) (c : ℕ → P.R.BdR), (∀ k, c k ∈ FilB P 0) → (∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) → ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.exists_series_limit_Lat | exact GlobalTheory.ExpImage.exists_series_limit_Lat | (intros; apply GlobalTheory.ExpImage.exists_series_limit_Lat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursion

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller]
  congr 2
  exact (frobeniusEquiv (OCb l) l).apply_symm_apply AI.ε

theorem act_μ {K : FinExt l} {h : GQ l} (hh : h ∈ Hinf K) : AI.actW h AI.μ = AI.μ := by
  have h1 : P.χQ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
  have h2 := GlobalTheory.T.cyclotomic_action_on_root_tower l P AI h 1 (by rw [h1]; simp) 0
  have h3 : AI.actT h AI.ε = AI.ε := by simpa [LocAinf.εroot] using h2
  rw [LocAinf.μ, map_sub, map_one, LocAinf.actW, WittVector.map_teichmuller]
  congr 2

theorem step_dR (T : LocTied l P AI) {g : GQ l} {U : ℤ_[l]} {k : ℕ} {β r : Ainf l} {u : P.R.BdR}
    (hu : io AI AI.π₁ * u = 1) (h : Step AI g U AI.π₁ k β r) :
    qB P (U : ℚ_[l]) * P.actQdR g (io AI β * u ^ k) - io AI β * u ^ k = io AI r * u ^ k := by
  have e := congrArg (io AI) h
  simp only [map_sub, map_mul, map_pow, io_act, io_zl AI T] at e
  have h1 : io AI AI.π₁ ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  have h2 : P.actQdR g (io AI AI.π₁) ^ k * P.actQdR g u ^ k = 1 := by
    rw [← mul_pow, ← map_mul, hu, map_one, one_pow]
  rw [map_mul, map_pow]
  linear_combination (u ^ k * P.actQdR g u ^ k) * e
    - (qB P (U : ℚ_[l]) * P.actQdR g (io AI β) * P.actQdR g u ^ k) * h1
    + (io AI β * u ^ k + io AI r * u ^ k) * h2

theorem limit (T : LocTied l P AI) {M : ℕ} (hM : 1 ≤ M) (g : GQ l) (U : ℤ_[l]) (b v : P.R.BdR)
    (S E : ℕ → P.R.BdR)
    (hb : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - S R ∈ Lat AI M n)
    (hE : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, E R ∈ Lat AI M n)
    (hS : ∀ R, ∃ z : ℤ_[l], v + (qB P (U : ℚ_[l]) * P.actQdR g (S R) - S R) = qB P (z : ℚ_[l]) - E R) :
    NearZ P M (v + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l P AI T M hM _ fun n => ?_
  obtain ⟨R₀, h₀⟩ := hb n
  obtain ⟨R₁, h₁⟩ := hE n
  obtain ⟨z, hz⟩ := hS (max R₀ R₁)
  have a := h₀ _ (le_max_left R₀ R₁)
  have a' := h₁ _ (le_max_right R₀ R₁)
  refine ⟨z, ?_⟩
  have := add_mem (sub_mem a (qB_mul_mem_Lat AI T U (act_mem_Lat AI g a))) a'
  convert this using 1
  rw [map_sub]
  linear_combination -hz

theorem telescope (g : GQ l) (U : ℤ_[l]) (s : ℕ) (B H : ℕ → P.R.BdR)
    (h : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (B k) - B k =
      H k - (l : P.R.BdR) ^ s * H (k + 1) + qB P (z : ℚ_[l])) (R : ℕ) :
    ∃ z : ℤ_[l], -H 0 + (qB P (U : ℚ_[l]) *
        P.actQdR g (∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) -
        ∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) =
      qB P (z : ℚ_[l]) - (l : P.R.BdR) ^ (s * R) * H R := by
  induction R with
  | zero => exact ⟨0, by simp⟩
  | succ R ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := h R
    refine ⟨z + (l : ℤ_[l]) ^ (s * R) * w, ?_⟩
    rw [Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      map_add, map_mul, map_pow, map_natCast, mul_add s R 1, pow_add, mul_one]
    linear_combination hz + (l : P.R.BdR) ^ (s * R) * hw

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (g : GQ l) (U : ℤ_[l]) (M : ℕ), 1 ≤ M → ∀ y : Ainf l, Solv AI K s g U (y - WittVector.frobenius y) → ∃ b ∈ FilB P 0, (∀ h ∈ Hinf K, NearZ P M (P.actQdR h b - b)) ∧ NearZ P M (io AI y + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  intro l _ P AI T K s hs g U M hM y ⟨p, q, hq0, hp, hstep⟩
  have asw := (GlobalTheory.ArtinSchreierWitt.main l).2.2
  choose β hβ using fun k : ℕ => asw (AI.ξ ^ (k + 1)) (p k)
  have hη' : ∀ k : ℕ, ∃ η : Ainf l, WittVector.frobenius η - AI.ξ ^ k * η = q k ∧ (k = 0 → η = -y) := by
    intro k
    rcases k with _ | k
    · exact ⟨-y, by rw [hq0, map_neg]; ring, fun _ => rfl⟩
    · obtain ⟨η, h⟩ := asw (AI.ξ ^ (k + 1)) (q (k + 1))
      exact ⟨η, h, fun h => absurd h (Nat.succ_ne_zero k)⟩
  choose η hη hη0 using hη'
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_inv_io_pi_alt l P AI T
  have small := GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice l P AI s hs u hu0 hu M
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_series_limit_Lat_alt l P AI M
    (fun k => (l : P.R.BdR) ^ (s * k) * (io AI (β k) * u ^ (k + 1)))
    (fun k => by
      have h1 : (l : P.R.BdR) ^ (s * k) * io AI (β k) ∈ FilB P 0 := by
        simpa using io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * β k)
      have h2 : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu0 (k + 1)
      rw [← mul_assoc]
      exact FilB_zero_mul h1 h2)
    (fun n => by
      obtain ⟨k₀, h⟩ := small n
      exact ⟨k₀, fun k hk => by rw [← mul_assoc]; exact h k hk _⟩)
  have h1 : ∀ k, io AI AI.π₁ ^ k * u ^ k = 1 := fun k => by rw [← mul_pow, hu, one_pow]
  refine ⟨b, hb0, fun h hh => ?_, ?_⟩
  · have key : ∀ k, ∃ z : ℤ_[l], qB P ((1 : ℤ_[l]) : ℚ_[l]) * P.actQdR h (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = (0 : P.R.BdR) - (l : P.R.BdR) ^ s * 0 + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI h 1 (k + 1) (β k) 0 (by
        rw [hβ]
        unfold Step
        rw [hp k h hh, act_μ AI hh]
        simp [mul_comm])
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz, zero_add, map_mul, map_pow, io_zl AI T, mul_assoc, h1]
      ring
    have := limit AI T hM h 1 b 0 _ (fun _ => 0) hb (fun n => ⟨0, fun _ _ => zero_mem _⟩)
      (fun R => by
        simpa using telescope h 1 s (fun k => io AI (β k) * u ^ (k + 1)) (fun _ => 0) key R)
    simpa using this
  · have key : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = io AI (η k) * u ^ k -
          (l : P.R.BdR) ^ s * (io AI (η (k + 1)) * u ^ (k + 1)) + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI g U (k + 1) (β k)
        (AI.π₁ * η k - ((l : ℕ) : Ainf l) ^ s * η (k + 1)) (by
        rw [hβ]
        convert hstep k using 1
        rw [← hη k, ← hη (k + 1), map_sub, map_mul, map_mul, map_pow, map_natCast, frob_π₁, AI.μ_eq]
        ring)
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz]
      simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, io_zl AI T]
      linear_combination (io AI (η k) * u ^ k) * hu + qB P (z : ℚ_[l]) * h1 (k + 1)
    refine limit AI T hM g U b _ _ (fun R => (l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) hb
      (fun n => ?_) (fun R => ?_)
    · obtain ⟨k₀, h⟩ := small n
      refine ⟨k₀, fun R hR => ?_⟩
      convert h R hR (η R * AI.π₁) using 1
      rw [map_mul]
      linear_combination (-(l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) * hu
    · have := telescope g U s (fun k => io AI (β k) * u ^ (k + 1)) (fun k => io AI (η k) * u ^ k) key R
      simpa only [hη0 0 rfl, map_neg, pow_zero, mul_one, neg_neg] using this

end GlobalTheory.ExpImage.Sum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursionStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_deRham_element_of_cocycleRecursion : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (g : GQ l) (U : ℤ_[l]) (M : ℕ), 1 ≤ M → ∀ y : Ainf l, Solv AI K s g U (y - WittVector.frobenius y) → ∃ b ∈ FilB P 0, (∀ h ∈ Hinf K, NearZ P M (P.actQdR h b - b)) ∧ NearZ P M (io AI y + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  first | exact @GlobalTheory.ExpImage.Sum.main | exact GlobalTheory.ExpImage.Sum.main | (intros; apply GlobalTheory.ExpImage.Sum.main <;> assumption)
end
end
