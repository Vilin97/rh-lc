module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.HermBvecFvec
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConvAlg

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.UtSubOneLast

section

@[expose] public section

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem ut_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (j : Fin (r + 1)) :
    u (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  split_ifs with h
  · subst h; exact hu.2 _
  · exact hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

theorem ut_det {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) : u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

theorem ut_sub_one_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (x : Fin (r + 1) → ℂ) : ((u - 1) *ᵥ x) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, ut_last hu, Matrix.one_apply]
  by_cases h : j = Fin.last r
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ut_conj_fix {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp only [ha, if_false, star_zero, zero_mul]
      exact (hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm
  · intro b _ hb
    rw [hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]
  · simp

theorem cancel_of_pair {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by
  have hA : IsUnit (uᴴ * Z).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]; exact hZ
  have h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]
  calc (u' - 1) *ᵥ c = ((uᴴ * Z)⁻¹ * (uᴴ * Z)) *ᵥ ((u' - 1) *ᵥ c) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem ut_adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hu : u ∈ UTset (r + 1)) : uᴴ * Adiag k r z * u = Adiag k r z := by
  ext a b
  rw [Adiag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu a, ut_last hu b, Matrix.diagonal_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
    · subst ha; subst hb; simp
    · subst ha; simp [hb, Ne.symm hb]
    · subst hb; simp [ha]
    · simp [ha, hb]
  · intro c _ hc; simp [hc]
  · simp

end PI.StabPairs.Conv
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStepOf

section

@[expose] public section

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  all_goals simp

theorem converseStep_of (hG : GramInv) : ConverseStep := by
  intro k r z z' γ hS hP p hp
  obtain ⟨u, u'⟩ := p
  obtain ⟨hu, hu', hZp⟩ := hp
  simp only at hu hu' hZp
  have hGi := hG k r z z' γ hS hP
  have hγ : γ ∈ B.GV k r := hP.1
  have hγu : IsUnit γ.det := isUnit_det_of_mem_GV hγ
  have hZ : IsUnit (Zhat k r z z' γ).det := isUnit_iff_ne_zero.mpr (det_Zhat_ne z z' hS γ hP)
  have hZh : IsUnit (Zhat k r z z' γ)ᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hZ.star
  have hZp' : u'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' γ)ᴴ := by
    have := congrArg Matrix.conjTranspose hZp
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  have hGi' : IsUnit ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ).det := by rwa [← gramM_eq]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = PI.StabPairsW.rhoOf k r z z' γ u u' := ⟨_, rfl⟩
  rw [← hρ]

  have hρF : ρ * Fm k r z z' γ = Fm k r z z' γ * Wm u u' := by
    rw [hρ, rho_eq]; exact PI.StabPairs.ConvAlg.rhoOf_mul _ _ _ hGi'
  have hcols := hρF
  rw [Fm_eq, Matrix.mul_fromCols, Wm, Matrix.fromCols_mul_fromBlocks] at hcols
  simp only [Matrix.mul_zero, add_zero, zero_add] at hcols
  obtain ⟨hA, hB⟩ := (Matrix.fromCols_ext_iff _ _ _ _).mp hcols
  have hs' : γ⁻¹ * ρ * γ * Ff k r z' = Ff k r z' * u' := by
    calc γ⁻¹ * ρ * γ * Ff k r z' = γ⁻¹ * (ρ * (γ * Ff k r z')) := by simp only [Matrix.mul_assoc]
      _ = γ⁻¹ * (γ * Ff k r z' * u') := by rw [hB]
      _ = Ff k r z' * u' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mul]

  have hWG : (Wm u u')ᴴ * ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ) * Wm u u' =
      (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    rw [← gramM_eq, gramM_blocks z z' hS.2.1.1 hS.2.2.1 γ hγ, Wm, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [ut_adiag k r z hu, ut_adiag k r z' hu', hZp, hZp']
  have hUH : ρ ∈ B.GV k r := by
    rw [mem_GV_iff, hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_unitary _ _ _ hpk_conjTranspose hGi' hWG
  have hexp : ∀ v, ρ *ᵥ v = v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
      (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
    intro v; rw [hρ]; exact rho_mulVec k r z z' γ u u' v

  have hN : ρ ∈ Nset k r := by
    refine ⟨hUH, fun a i hi => N2gen k r z ρ hu hA a i hi, fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z ρ i j hi ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ bvec j) ∘ Sum.inl)) (ut_sub_one_last hu _) ?_
    have hc := cancel_of_pair hu hZ hZp _
      (Z_cR k r z z' γ hS hP hGi (bvec j) (fun a ha => herm_bvec_fvec k r z j hj1 hj2 a ha))
    rw [hexp, hc, Matrix.mulVec_zero, add_zero]

  have hN' : γ⁻¹ * ρ * γ ∈ Nset k r := by
    refine ⟨mul_mem_GV (mul_mem_GV (inv_mem_GV hγ) hUH) hγ, fun a i hi => N2gen k r z' _ hu' hs' a i hi,
      fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z' _ i j hi ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ (γ *ᵥ bvec j)) ∘ Sum.inr))
      (ut_sub_one_last hu' _) ?_
    have hc := cancel_of_pair hu' hZh hZp' _
      (Z_cL k r z z' γ hS hP hGi (γ *ᵥ bvec j) (fun b hb => by
        rw [herm_GV hγ]; exact herm_bvec_fvec k r z' j hj1 hj2 b hb))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hexp, hc, Matrix.mulVec_zero, add_zero,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec, Matrix.one_mul]
  refine ⟨⟨⟨⟨1, one_mem_UW k r z, ρ, hN, (Matrix.one_mul ρ).symm⟩,
    γ⁻¹ * ρ * γ, ⟨1, one_mem_UW k r z', _, hN', (Matrix.one_mul _).symm⟩, ?_⟩, ?_⟩, ?_⟩
  · calc ρ = (γ * γ⁻¹) * ρ * (γ * γ⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul, Matrix.mul_one]
      _ = γ * (γ⁻¹ * ρ * γ) * γ⁻¹ := by simp only [Matrix.mul_assoc]
  · intro v hv
    rw [mem_Uperp_iff] at hv
    rw [hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker _ _ _ v hv
  · show (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ)) = (u, u')
    rw [uMap_eq z hS.2.1 ρ u hA, uMap_eq z' hS.2.2 _ u' hs']

end PI.StabPairs.Conv
end
end
end
