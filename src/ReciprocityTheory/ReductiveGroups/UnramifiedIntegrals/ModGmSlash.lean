module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSlash

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem denom_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  first
  | rfl
  | simp [UpperHalfPlane.denom]
  | (simp [UpperHalfPlane.denom]; norm_cast)

theorem smul_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]

theorem pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by
  have hm : ∀ i j, (Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') i j := fun i j => by rw [h]
  have z00 : (t.1 : ℤ) * γ 0 0 + (t.2.1 : ℤ) * γ 1 0 = γ' 0 0 * (t'.1 : ℤ) := by
    have hh := hm 0 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z01 : (t.1 : ℤ) * γ 0 1 + (t.2.1 : ℤ) * γ 1 1 = γ' 0 0 * (t'.2.1 : ℤ) + γ' 0 1 * (t'.2.2 : ℤ) := by
    have hh := hm 0 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z10 : (t.2.2 : ℤ) * γ 1 0 = γ' 1 0 * (t'.1 : ℤ) := by
    have hh := hm 1 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z11 : (t.2.2 : ℤ) * γ 1 1 = γ' 1 0 * (t'.2.1 : ℤ) + γ' 1 1 * (t'.2.2 : ℤ) := by
    have hh := hm 1 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have c00 : (t.1 : ℂ) * ((γ 0 0 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z00
  have c01 : (t.1 : ℂ) * ((γ 0 1 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 0 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z01
  have c10 : (t.2.2 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z10
  have c11 : (t.2.2 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 1 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z11
  have he : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have he' : (t'.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hD' : ((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hZ : ((γ • τ : ℍ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) := by
    rw [smul_SL_coe γ τ]; exact div_mul_cancel₀ _ hD
  have hW : ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) * (t'.2.2 : ℂ) = (t'.1 : ℂ) * (τ : ℂ) + (t'.2.1 : ℂ) := by
    rw [pt_coe ht'.1 ht'.2]; exact div_mul_cancel₀ _ he'
  have c2 : (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    linear_combination ((γ' 1 0 : ℤ) : ℂ) * hW - (τ : ℂ) * c10 - c11
  refine ⟨UpperHalfPlane.ext ?_, ?_⟩
  · rw [pt_coe ht.1 ht.2, smul_SL_coe γ' (pt t'.1 t'.2.1 t'.2.2 τ), div_eq_div_iff he hD']
    have key : ((t'.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) *
        (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) - (((γ' 0 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 0 1 : ℤ) : ℂ)) * (t.2.2 : ℂ)) = 0 := by
      linear_combination (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * c2 +
        ((t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * ((t.1 : ℂ) * hZ - ((γ' 0 0 : ℤ) : ℂ) * hW + (τ : ℂ) * c00 + c01)
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 (mul_ne_zero he' hD)
    · exact sub_eq_zero.mp h0
  · rw [denom_SL_coe, denom_SL_coe]
    exact c2

theorem fac_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rw [div_mul_eq_mul_div, eq_div_iff he']
    exact h2
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModHnf

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ (x y z w : ℤ) (a b e : ℕ), x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
    · exact h0
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]; conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]; ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod0 : 0 ≤ b0 % E := Int.emod_nonneg _ hE0.ne'
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  have hdiv : b0 % E + E * (b0 / E) = b0 := Int.emod_add_mul_ediv b0 E
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hmod0
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast; rw [hEn]; exact hgE
    exact_mod_cast this
  · omega
  · rw [hx]; ring
  · rw [hEn, hBn]
    have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-q) * h1
  · rw [hz]; ring
  · rw [hEn, hBn]
    have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-s) * h1

theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [Matrix.det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    · exact h0
    · omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    · exact h0
    · omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    · have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
    · have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPerm

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem perm_Tmat_det {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : (Tmat t).det = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  simp only [Tmat, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact_mod_cast Nat.mul_div_cancel' hdvd

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmSlash

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A : SL(2, ℤ),
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ (Tm m) := by
    intro t1 h1 t2 h2 he
    have e1 := hg t1 h1
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]; simp only [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hσ t ht
    · rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ := hprod (fun t => fac t τ)
  have hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ) := hprod (fun t => (t.2.2 : ℂ))
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  have hstep : ∏ t ∈ Tm m, fac t (γ • τ) =
      ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ) :=
    Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)
  unfold Gm
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac,
    Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
end
end
end
