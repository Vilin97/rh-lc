module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvdBound
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvdBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnityStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.BKLim.BetaDiv.isBeta_div : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  intro l _ K bk N d ρ F m k n β γ hβ hm hnk hd
  have hT := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk
  have strip : ∀ (r n : ℕ) (a : Ainf l), bk.ev bk.E ^ r ∣ (l : Ainf l) ^ n * a → bk.ev bk.E ^ r ∣ a := by
    intro r n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      refine ih a ((hT r).1 _ ?_)
      rw [pow_succ', mul_assoc] at h
      exact h
  have hk : (l : bk.S) ^ k = (l : bk.S) ^ n * (l : bk.S) ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnk]
  refine ⟨fun i j => ?_, fun g i j => ?_⟩
  · have h1 := hβ.1 i j
    have h2 : bk.E ∣ (β - (l : bk.S) ^ n • γ) i j := (dvd_pow_self _ (by omega : m ≠ 0)).trans (hd i j)
    have h3 : bk.E ∣ (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j := by
      have : (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (β - (l : bk.S) ^ n • γ) i j := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hk]
        ring
      rw [this]
      exact dvd_sub h1 h2
    obtain ⟨c, hc⟩ := h3
    have h4 : bk.ev bk.E ^ 1 ∣ (l : Ainf l) ^ n * bk.ev ((γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) :=
      ⟨bk.ev c, by rw [pow_one, ← map_mul, ← hc, map_mul, map_pow, map_natCast]⟩
    simpa using (hT 1).2.1 _ (strip 1 n _ h4)
  · set Φ := (F.ε g).map WittVector.frobenius with hΦ
    set σ := Per.σA (g : GQ l) with hσ
    set δ := β - (l : bk.S) ^ n • γ with hδ
    have hev : ∀ p q, bk.ev bk.E ^ m ∣ (δ.map bk.ev) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      exact ⟨bk.ev c, by rw [Matrix.map_apply, hc, map_mul, map_pow]⟩
    have hσE : bk.ev bk.E ∣ σ (bk.ev bk.E) := by
      have := GlobalTheory.BKLim.BetaBd.dvd_σA_ev_sub bk g bk.E
      simpa using dvd_add this (dvd_refl (bk.ev bk.E))
    have hevσ : ∀ p q, bk.ev bk.E ^ m ∣ ((δ.map bk.ev).map σ) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      rw [Matrix.map_apply, Matrix.map_apply, hc, map_mul, map_mul, map_pow, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hσE m) _
    have hβeq : β = (l : bk.S) ^ n • γ + δ := by rw [hδ]; abel
    have hmap : (β.map bk.ev) = (l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev := by
      rw [hβeq]; ext p q; simp
    have hmapσ : (β.map bk.ev).map σ = (l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ := by
      rw [hmap]; ext p q; simp
    have hD := hβ.2 g i j
    rw [hmapσ, hmap] at hD
    have hsplit : (Φ * ((l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ) -
        ((l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev)) i j =
        (l : Ainf l) ^ n * (Φ * (γ.map bk.ev).map σ - γ.map bk.ev) i j +
          ((Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsplit] at hD
    have hrest : bk.ev bk.E ^ m ∣ (Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j := by
      refine dvd_sub ?_ (hev i j)
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hevσ k j) _
    exact strip m n _ ((dvd_add_left hrest).1 hD)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  first | (exact @GlobalTheory.BKLim.BetaDiv.isBeta_div) | (exact GlobalTheory.BKLim.BetaDiv.isBeta_div) | (intros; apply GlobalTheory.BKLim.BetaDiv.isBeta_div  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfTheta

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfThetaStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_primePow_dvd_mod_eisenstein_of_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  first | exact @GlobalTheory.LiftDiv.dvd_mod_E | exact GlobalTheory.LiftDiv.dvd_mod_E | (intros; apply GlobalTheory.LiftDiv.dvd_mod_E; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominators

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

theorem isBeta_scale {bk : BK K} (F : Frame bk N d ρ) {m k : ℕ} {β : Matrix (Fin d) (Fin d) bk.S}
    (hβ : F.IsBeta m k β) (j : ℕ) : F.IsBeta m (k + j) ((l : bk.S) ^ j • β) := by
  refine ⟨fun p q => ?_, fun g p q => ?_⟩
  · have : ((l : bk.S) ^ j • β - (l : bk.S) ^ (k + j) • (1 : Matrix (Fin d) (Fin d) bk.S)) p q =
        (l : bk.S) ^ j * (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) p q := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, pow_add]; ring
    rw [this]; exact dvd_mul_of_dvd_right (hβ.1 p q) _
  · have h2 : ((l : bk.S) ^ j • β).map bk.ev = (l : Ainf l) ^ j • β.map bk.ev := by
      ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    have h1 : (((l : bk.S) ^ j • β).map bk.ev).map (Per.σA (g : GQ l)) =
        (l : Ainf l) ^ j • (β.map bk.ev).map (Per.σA (g : GQ l)) := by
      rw [h2]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [h1, h2, Matrix.mul_smul, ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hβ.2 g p q) _

end GlobalTheory.BKLim.BetaBd


open GlobalTheory.BKLim.BetaBd in
theorem GlobalTheory.BKLim.beta_bdd_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  intro l _ K bk m
  obtain ⟨g, z, ⟨w, hw, hzw⟩, hz⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hu : ∀ i, 1 ≤ i → Per.θ l w ^ i - 1 ≠ 0 := by
    intro i hi h
    apply hz i hi
    have h1 : ((Per.θ l w : OC l) : ℂ_[l]) ^ i = 1 := by
      have := congrArg (fun t : OC l => (t : ℂ_[l])) (sub_eq_zero.1 h)
      simpa using this
    rw [(thetaD_props l).2.2.2.1 w] at hzw
    calc z ^ i = z ^ i * ((Per.θ l w : ℂ_[l]) ^ i) := by rw [h1, mul_one]
      _ = (z * (Per.θ l w : ℂ_[l])) ^ i := (mul_pow _ _ _).symm
      _ = 1 := by rw [hzw, one_pow]
  choose a ha using fun i : {i : ℕ // 1 ≤ i} => exists_dvd_bound _ (hu i.1 i.2)
  let A : ℕ → ℕ := fun i => if h : 1 ≤ i then a ⟨i, h⟩ else 0
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, A j
  have hSs : ∀ i, S (i + 1) = S i + A i := fun i => Finset.sum_range_succ _ _
  have hSm : ∀ i j, i ≤ j → S i ≤ S j := fun i j h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  refine ⟨S m, fun N d ρ F k β hβ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨(l : bk.S) ^ S 0 • 1, fun p q => by simp, fun g p q => by simp⟩
  by_cases hk : k < S m
  · refine ⟨(l : bk.S) ^ (S m - k) • β, ?_⟩
    have := isBeta_scale F hβ (S m - k)
    rwa [Nat.add_sub_cancel' hk.le] at this
  push_neg at hk
  have key : ∀ i, 1 ≤ i → i ≤ m → ∃ γ : Matrix (Fin d) (Fin d) bk.S,
      ∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ (k - S i) • γ) p q := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ him
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨(l : bk.S) ^ S 1 • 1, fun p q => ?_⟩
        have hS : S 1 ≤ k := le_trans (hSm 1 m him) hk
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hS, pow_one]
        exact hβ.1 p q
      · obtain ⟨γ, hγ⟩ := ih hi0 (by omega)
        obtain ⟨δ, hδ1, hδ2⟩ := GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem l K bk N d ρ F g w hw m k β hβ i (k - S i) him γ hγ
        have hAi : A i = a ⟨i, hi0⟩ := dif_pos hi0
        have hS1 : S (i + 1) ≤ k := le_trans (hSm _ _ him) hk
        have hle : a ⟨i, hi0⟩ ≤ k - S i := by rw [hSs] at hS1; omega
        have hexp : k - S i - a ⟨i, hi0⟩ = k - S (i + 1) := by rw [hSs, hAi]; omega
        have hlift : ∀ p q, ∃ s' t : bk.S, δ p q = (l : bk.S) ^ (k - S (i + 1)) * s' + bk.E * t := by
          intro p q
          obtain ⟨y, hy⟩ := hδ2 p q
          obtain ⟨y', hy'⟩ := ha ⟨i, hi0⟩ _ y _ hy hle
          rw [hexp] at hy'
          exact GlobalTheory.T.exists_primePow_dvd_mod_eisenstein_of_theta l K bk _ _ y' hy'
        choose δ' t ht using hlift
        refine ⟨(l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ', fun p q => ?_⟩
        have hpow : (l : bk.S) ^ (k - S (i + 1)) * (l : bk.S) ^ A i = (l : bk.S) ^ (k - S i) := by
          rw [← pow_add]; congr 1; rw [hSs] at hS1 ⊢; omega
        have e : (β - (l : bk.S) ^ (k - S (i + 1)) • ((l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ')) p q =
            (β - (l : bk.S) ^ (k - S i) • γ - bk.E ^ i • δ) p q + bk.E ^ (i + 1) * t p q := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
          linear_combination (bk.E ^ i) * ht p q - γ p q * hpow
        rw [e]
        exact dvd_add (hδ1 p q) (dvd_mul_right _ _)
  obtain ⟨γ, hγ⟩ := key m hm le_rfl
  refine ⟨γ, ?_⟩
  have := GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul l K bk N d ρ F m k (k - S m) β γ hβ hm (Nat.sub_le k (S m)) hγ
  rwa [Nat.sub_sub_self hk] at this

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominatorsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_beta_bounded_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  first | (exact @GlobalTheory.BKLim.beta_bdd_denominators) | (exact GlobalTheory.BKLim.beta_bdd_denominators) | (intros; apply GlobalTheory.BKLim.beta_bdd_denominators  <;> assumption)
end
end
