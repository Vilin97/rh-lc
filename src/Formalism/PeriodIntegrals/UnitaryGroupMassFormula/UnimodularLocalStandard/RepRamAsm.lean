module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RamDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.IsKTheta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.FieldTheory.Finite.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.HNsmulNsmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat
import Mathlib.Analysis.CStarAlgebra.Classes
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.DescentStep

section

@[expose] public section

noncomputable section
open scoped ComplexConjugate
open Polynomial

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma pigeon {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (A B E : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hB : ¬ (p : ℤ) ∣ B) : ∃ s t : ℤ, (p : ℤ) ∣ s ^ 2 * A + t ^ 2 * B - E := by
  have := Fact.mk hp
  have hA' : (A : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB' : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']
    rfl
  have hg : (C (B : ZMod p) * X ^ 2).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB']
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  linear_combination hxy

variable {a : ℕ} {b c : ℤ} {d : ℕ}

lemma descent_step (hok : CmOK a b c d) {P Q r p q : ℤ} (hr : (d : ℤ) ∣ r) (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hM : r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q) :
    (d : ℤ) ∣ P ∧ (d : ℤ) ∣ Q := by
  obtain ⟨h4, -, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef
  have hcop : IsCoprime ((d : ℤ) ^ 2) q :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)
  have hdN : (d : ℤ) ^ 2 ∣ N := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hM]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _
  have hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2 := by
    rw [hNdef]
    linear_combination Q ^ 2 * h4
  have hX : (d : ℤ) ∣ 2 * P + b * Q := by
    apply hD.dvd_of_dvd_pow (n := 2)
    have : (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2 := by rw [hid]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)
  have hQ2 : (d : ℤ) ∣ Q ^ 2 := by
    have h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2 := by
      have : (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2 := by rw [hid]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_left hD0).mp h1
  have hQ : (d : ℤ) ∣ Q := hD.dvd_of_dvd_pow hQ2
  have h2P : (d : ℤ) ∣ 2 * P := by
    have : 2 * P = (2 * P + b * Q) - b * Q := by ring
    rw [this]
    exact dvd_sub hX (Dvd.dvd.mul_left hQ _)
  refine ⟨?_, hQ⟩
  rcases hD.dvd_or_dvd h2P with h | h
  · exact absurd h hD2
  · exact h

lemma norm_square (hok : CmOK a b c d) {γ : ℂ} (hγ : IsK b d γ) {p q : ℤ} (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hN : γ * conj γ = (p : ℂ) / q) : ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
  obtain ⟨h4, ha, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero _)
  have hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
    have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    have h4' : (4 * a * c : ℂ) = b ^ 2 + d := by exact_mod_cast h4
    unfold cmTheta
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs +
      (-1 / 4 : ℂ) * h4'

  have rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
    intro P Q r hr
    have h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q) := by
      rw [map_mul, map_intCast, ← hN]
      ring
    have h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c) := by
      rw [hr, map_add (f := _), map_mul, map_intCast, map_intCast, theta_conj]
      linear_combination (Q : ℂ) ^ 2 * hθ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
      rw [← h2, h1]
      field_simp
    exact_mod_cast hC

  have main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q r hn hr0 hM
      by_cases hdr : (d : ℤ) ∣ r
      · obtain ⟨hP, hQ⟩ := descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM
        obtain ⟨P', rfl⟩ := hP
        obtain ⟨Q', rfl⟩ := hQ
        obtain ⟨r', rfl⟩ := hdr
        have hr' : r' ≠ 0 := by
          rintro rfl
          simp at hr0
        have hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q := by
          have hd2 : ((d : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hD0
          apply mul_left_cancel₀ hd2
          linear_combination hM
        refine ih r'.natAbs ?_ P' Q' r' rfl hr' hM'
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (d : ℤ).natAbs := by
          have := hdp.two_le
          simp only [Int.natAbs_natCast]
          omega
        have h2 : 0 < r'.natAbs := Int.natAbs_pos.mpr hr'
        nlinarith
      · have := Fact.mk hdp
        have hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q) := by
          linear_combination 4 * hM + q * Q ^ 2 * h4
        have h2r : ((2 * r : ℤ) : ZMod d) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro h
          rcases hD.dvd_or_dvd h with h | h
          · exact hD2 h
          · exact hdr h
        refine ⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hk := congrArg (Int.cast : ℤ → ZMod d) hkey
        push_cast at hk h2r ⊢
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at *
        have hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h2r, one_pow]
        linear_combination (-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv
  obtain ⟨P, Q, r, hr0, hr⟩ := hγ
  exact main r.natAbs P Q r rfl hr0 (rel P Q r hr)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamAsm

section

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyStartRam_of_unit (hU : UnitVecRam) : KeyStartRam := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK hld
  subst l
  have hK0 := hK
  obtain ⟨hOK, hsd, hθ, -, h2, hdp, hQ, hi₀, -⟩ := hK0
  set L := cmL a b d ha hd lam hlam with hL
  set κ := repKappa a b d ha hd lam hlam with hκdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  set f := fvec a b d lam x y i₀ with hf
  have hκ : κ ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hκc : conj κ = κ := kappa_real a b d ha hd lam hlam
  have hHf : stdH L m f f = κ * (Q : ℂ) := rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀
  have hQ0 : (Q : ℂ) ≠ 0 := by
    have : Q ≠ 0 := fun h => hQ (h ▸ dvd_zero _)
    exact_mod_cast this
  have hfT : ∀ j ∈ T, f j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := fun h => hi₀ (h ▸ hj)
    simp [hf, fvec, hne]
  have hfmem : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  set M := relIdx Λ (stdLat L m) with hMdef
  have hMf : M • f ∈ Λ := by
    have h := AddSubgroup.nsmul_index_mem (Λ.addSubgroupOf (stdLat L m)) ⟨f, hfmem⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    simpa [hMdef, relIdx, AddSubgroup.relIndex] using h
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast h2
  have hgf : M • f = (M : ℂ) • f := (Nat.cast_smul_eq_nsmul ℂ M f).symm
  set g := M • f with hg
  have hHs : ∀ (α β : ℂ) (u v : m → ℂ), stdH L m (α • u) (β • v) = α * conj β * stdH L m u v := by
    intro α β u v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    ring
  have hgT : ∀ j ∈ T, g j = 0 := by
    intro j hj
    simp [hgf, hfT j hj]
  have hg0 : g ≠ 0 := by
    intro h
    have h' : stdH L m g g = 0 := by rw [h]; simp
    rw [hgf, hHs, hHf] at h'
    have : (M : ℂ) * conj (M : ℂ) * (κ * Q) ≠ 0 := by
      simp only [map_natCast]
      exact mul_ne_zero (mul_ne_zero hMc hMc) (mul_ne_zero hκ hQ0)
    exact this h'
  have hgS : SatMem d Λ g := rep_sat_of_mem d Λ hMf hdp
  have hd1 : ¬ (d : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact hdp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨y1, hy1S, hy1T, -, p1, q1, hp1, hq1, hy1H⟩ :=
    hU a b c d ha hd lam hlam m Λ x y T i₀ hK 0 (rep_sat_zero d Λ hdp) (by simp) (Or.inl rfl)
      g hgS hgT (by simp) hg0
  have hp1c : (p1 : ℂ) ≠ 0 := by
    have : p1 ≠ 0 := fun h => hp1 (h ▸ dvd_zero _)
    exact_mod_cast this
  have hq1c : (q1 : ℂ) ≠ 0 := by
    have : q1 ≠ 0 := fun h => hq1 (h ▸ dvd_zero _)
    exact_mod_cast this
  obtain ⟨n', c₂, s', hs', hpair⟩ := sat_pair hOK hsd hθ hdp hgS hy1S
  rw [← hL, ← hκdef] at hy1H hpair
  have hs'c : (s' : ℂ) ≠ 0 := by
    have : s' ≠ 0 := fun h => hs' (h ▸ dvd_zero _)
    exact_mod_cast this
  have hθc : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
    have := rep_theta_add_conj b d
    linear_combination this
  set γ0 : ℂ := (q1 : ℂ) * ((n' : ℂ) - c₂ * conj (cmTheta b d)) with hγ0
  set z : m → ℂ := (((p1 * s' : ℤ) : ℂ)) • g - γ0 • y1 with hz
  have hzS : SatMem d Λ z := by
    have h1 := rep_sat_zsmul d Λ hgS (p1 * s')
    have h2 := rep_sat_elt d Λ hdp hθ hy1S (q1 * n') (q1 * c₂) 1 hd1
    have h3 : ((((q1 * n' : ℤ) : ℂ) - ((q1 * c₂ : ℤ) : ℂ) * conj (cmTheta b d)) / ((1 : ℤ) : ℂ)) = γ0 := by
      rw [hγ0]; push_cast; ring
    rw [h3] at h2
    exact rep_sat_sub d Λ hdp h1 h2
  have hzT : ∀ j ∈ T, z j = 0 := by
    intro j hj
    simp [hz, hgT j hj, hy1T j hj]
  have hzy : stdH L m z y1 = 0 := by
    have e1 : stdH L m z y1 = ((p1 * s' : ℤ) : ℂ) * stdH L m g y1 - γ0 * stdH L m y1 y1 := by
      simp only [hz, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e1, hpair, hy1H, hγ0]
    push_cast
    field_simp
    ring
  by_cases hz0 : z = 0
  · set r : ℂ := ((p1 * s' : ℤ) : ℂ) * M with hr
    have hr0 : r ≠ 0 := by
      rw [hr]; push_cast
      exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
    have hrc : conj r = r := by rw [hr]; simp
    have hrf : r • f = γ0 • y1 := by
      have : ((p1 * s' : ℤ) : ℂ) • g = γ0 • y1 := sub_eq_zero.mp (by rw [← hz]; exact hz0)
      rw [hgf, smul_smul] at this
      simpa [hr] using this
    set β : ℂ := γ0 / r with hβ
    have hβN : β * conj β = ((Q * q1 : ℤ) : ℂ) / ((p1 : ℤ) : ℂ) := by
      have e := congrArg (fun v => stdH L m v v) hrf
      simp only [hHs, hHf, hy1H, hrc] at e
      field_simp at e
      rw [hβ, map_div₀, hrc, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hr0 hr0) hp1c]
      push_cast
      linear_combination -e
    have hβK : IsK b d β := by
      refine ⟨q1 * (n' - c₂ * b), q1 * c₂, p1 * s' * M, ?_, ?_⟩
      · have : ((p1 * s' * M : ℤ) : ℂ) ≠ 0 := by
          push_cast; exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
        exact_mod_cast this
      · rw [hβ, hγ0, hθc]
        have : ((p1 * s' * (M : ℤ) : ℤ) : ℂ) = r := by rw [hr]; push_cast; ring
        rw [this]
        field_simp
        push_cast
        ring
    have hQq : ¬ (d : ℤ) ∣ Q * q1 := not_dvd_mul' hdp hQ hq1
    obtain ⟨s, hs⟩ := norm_square hOK hβK hQq hp1 hβN
    obtain ⟨k, hk⟩ := hs
    refine ⟨(s : ℂ) • y1, ⟨rep_sat_zsmul d Λ hy1S s, ?_, k, Q * q1, hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj]
    · rw [hHs, hy1H, hHf]
      have hk' : (s : ℂ) ^ 2 * p1 = Q * q1 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      simp only [map_intCast]
      push_cast
      field_simp
      linear_combination hk'
  · obtain ⟨y2, hy2S, hy2T, hy21, p2, q2, hp2, hq2, hy2H⟩ :=
      hU a b c d ha hd lam hlam m Λ x y T i₀ hK y1 hy1S hy1T (Or.inr ⟨p1, q1, hp1, hq1, by
        rw [hy1H]⟩) z hzS hzT hzy hz0
    rw [← hL, ← hκdef] at hy2H
    rw [← hL] at hy21
    have hp2c : (p2 : ℂ) ≠ 0 := by
      have : p2 ≠ 0 := fun h => hp2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hq2c : (q2 : ℂ) ≠ 0 := by
      have : q2 ≠ 0 := fun h => hq2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hy12 : stdH L m y1 y2 = 0 := by
      have := rep_H_conj (L := L) (m := m) y2 y1
      rw [hy21, map_zero] at this
      exact this.symm
    have hodd : d % 2 = 1 := by
      have := hOK.2.2.1
      omega
    obtain ⟨s, t, hst⟩ := pigeon hdp hodd (p1 * q2) (p2 * q1) (Q * q1 * q2)
      (not_dvd_mul' hdp hp1 hq2) (not_dvd_mul' hdp hp2 hq1)
    obtain ⟨k, hk⟩ := hst
    have hQq : ¬ (d : ℤ) ∣ Q * (q1 * q2) := not_dvd_mul' hdp hQ (not_dvd_mul' hdp hq1 hq2)
    refine ⟨(s : ℂ) • y1 + (t : ℂ) • y2,
      ⟨rep_sat_add d Λ hdp (rep_sat_zsmul d Λ hy1S s) (rep_sat_zsmul d Λ hy2S t), ?_, k, Q * (q1 * q2), hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj, hy2T j hj]
    · have e : stdH L m ((s : ℂ) • y1 + (t : ℂ) • y2) ((s : ℂ) • y1 + (t : ℂ) • y2) =
          (s : ℂ) ^ 2 * stdH L m y1 y1 + (t : ℂ) ^ 2 * stdH L m y2 y2 := by
        simp only [map_add (f := _), LinearMap.add_apply, hHs, hy12, hy21, map_intCast]
        ring
      rw [e, hy1H, hy2H, hHf]
      have hk' : (s : ℂ) ^ 2 * (p1 * q2) + (t : ℂ) ^ 2 * (p2 * q1) = Q * q1 * q2 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      push_cast
      field_simp
      linear_combination hk'

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
end
