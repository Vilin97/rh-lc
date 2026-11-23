module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DPsiMonomialIwh

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem rowA_of_iwh {K : Type} [CommRing K] {k n : ℕ} {f : MvPolynomial (Fin k × Fin n) K} {μ : Fin k → ℕ}
    (h : IsWeightedHomogeneous (rowW k n) f μ) (a : Fin k) : RowA a f (μ a) := by
  intro u hu
  rw [← ldrow_weight_rowW, h hu]

theorem qt_cnt (m : ℕ) (i a' : Fin (m + 1)) :
    (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ)) a' = if a' = i then 0 else 1 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · subst h
    exact Finset.sum_eq_zero fun p _ => if_neg (Fin.succAbove_ne a' p).symm
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro p _ hp
      exact if_neg fun e => hp (Fin.succAbove_right_injective e).symm
    · intro hq
      exact absurd (Finset.mem_univ q) hq

theorem qt_covY_iwh (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (covY K m i) (∑ p : Fin m, Pi.single (i.succAbove p) 1) := by
  have e : covY K m i = ((-1 : ℤ) ^ (i : ℕ)) • initMinor K (n := m + 1) i.succAbove (Nat.le_succ m) := by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  rw [e, ← mem_weightedHomogeneousSubmodule]
  exact zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_initMinor_rowHom K i.succAbove (Nat.le_succ m))) _

theorem dPsi_monomial (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    deltaB K m (PsiXY K m (monomial v c)) =
      C c * ((∏ i : Fin (m + 1), X (i, (0 : Fin (m + 1))) ^ v (Sum.inl i)) * ∏ i : Fin (m + 1), covY K m i ^ v (Sum.inr i)) := by
  have hx : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inr i))) = covY K m i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
    rw [this, rename_id_apply]
  have hC : deltaB K m (PsiXY K m (C c)) = C c := by
    simp only [← algebraMap_eq, AlgHom.commutes]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, hC]

def qtW (m : ℕ) (v : XY (m + 1) →₀ ℕ) : Fin (m + 1) → ℕ :=
  0 + ((∑ i : Fin (m + 1), v (Sum.inl i) • (Pi.single i 1 : Fin (m + 1) → ℕ)) +
    ∑ i : Fin (m + 1), v (Sum.inr i) • ∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ))

theorem dPsi_monomial_iwh (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (deltaB K m (PsiXY K m (monomial v c))) (qtW m v) := by
  rw [dPsi_monomial]
  refine (isWeightedHomogeneous_C _ c).mul (IsWeightedHomogeneous.mul ?_ ?_)
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (isWeightedHomogeneous_X K (rowW (m + 1) (m + 1)) (i, 0)).pow _
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (qt_covY_iwh K m i).pow _

theorem qtW_apply (m : ℕ) (v : XY (m + 1) →₀ ℕ) (a' : Fin (m + 1)) :
    qtW m v a' + v (Sum.inr a') = v (Sum.inl a') + yDeg v := by
  classical
  unfold qtW yDeg
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∑ i : Fin (m + 1), v (Sum.inl i) * (Pi.single i 1 : Fin (m + 1) → ℕ) a' = v (Sum.inl a') := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∀ i : Fin (m + 1), (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ) a') = if a' = i then 0 else 1 := by
    intro i
    rw [← Finset.sum_apply]
    exact qt_cnt m i a'
  have h3 : v (Sum.inr a') = ∑ i : Fin (m + 1), v (Sum.inr i) * (if a' = i then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, add_assoc]
  congr 1
  simp only [h2]
  conv_lhs => rw [h3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TopLinePOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def vStar (m a b : ℕ) : XY (m + 1) →₀ ℕ :=
  Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr (Fin.last m)) b

theorem qt_comb (m a b : ℕ) (v : XY (m + 1) →₀ ℕ) (hx : xDeg v = a) (hy : yDeg v = b)
    (h0 : qtW m v 0 = a + b) (hl : qtW m v (Fin.last m) = 0) : v = vStar m a b := by
  classical
  have e0 := qtW_apply m v 0
  have el := qtW_apply m v (Fin.last m)
  have l0 : v (Sum.inl 0) ≤ xDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  have ll : v (Sum.inr (Fin.last m)) ≤ yDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inr i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have a1 : v (Sum.inl 0) = a := by omega
  have a2 : v (Sum.inr (Fin.last m)) = b := by omega
  have z1 : ∀ i : Fin (m + 1), i ≠ 0 → v (Sum.inl i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inl i)) (Finset.mem_univ 0)
    have h' : ∑ x ∈ Finset.univ.erase (0 : Fin (m + 1)), v (Sum.inl x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inl x) = a := hx
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  have z2 : ∀ i : Fin (m + 1), i ≠ Fin.last m → v (Sum.inr i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inr i)) (Finset.mem_univ (Fin.last m))
    have h' : ∑ x ∈ Finset.univ.erase (Fin.last m), v (Sum.inr x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inr x) = b := hy
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  ext w
  unfold vStar
  rw [Finsupp.add_apply]
  rcases w with i | i
  · by_cases hi : i = 0
    · subst hi; simp [a1]
    · have : (Sum.inl 0 : XY (m + 1)) ≠ Sum.inl i := fun h => hi (Sum.inl.inj h).symm
      simp [this, z1 i hi]
  · by_cases hi : i = Fin.last m
    · subst hi; simp [a2]
    · have : (Sum.inr (Fin.last m) : XY (m + 1)) ≠ Sum.inr i := fun h => hi (Sum.inr.inj h).symm
      simp [this, z2 i hi]

theorem qtW_vStar (m a b : ℕ) (hm : 1 ≤ m) : qtW m (vStar m a b) 0 = a + b ∧ qtW m (vStar m a b) (Fin.last m) = 0 := by
  classical
  have hne : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have e0 := qtW_apply m (vStar m a b) 0
  have el := qtW_apply m (vStar m a b) (Fin.last m)
  have y : yDeg (vStar m a b) = b := by
    unfold yDeg vStar
    simp [Finsupp.single_apply]
  have v1 : vStar m a b (Sum.inr 0) = 0 := by
    unfold vStar
    simp [hne]
  have v2 : vStar m a b (Sum.inl 0) = a := by
    unfold vStar
    simp
  have v3 : vStar m a b (Sum.inr (Fin.last m)) = b := by
    unfold vStar
    simp
  have v4 : vStar m a b (Sum.inl (Fin.last m)) = 0 := by
    unfold vStar
    simp [hne.symm]
  constructor <;> omega

theorem topCore (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ)
    (Ψ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (hΨ : Ψ ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)))
    (h0 : RowA 0 Ψ (a + b)) (hl : RowA (Fin.last m) Ψ 0) :
    ∃ c : R.Kf, Ψ = c • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) := by
  classical
  rw [← tie3 h2 h5 hCO R m hm a b] at hΨ
  obtain ⟨f, hf, rfl⟩ := hΨ
  refine ⟨AddMonoidAlgebra.coeff f (vStar m a b), ?_⟩
  have hT : AddMonoidAlgebra.coeff f (vStar m a b) • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) =
      deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (AddMonoidAlgebra.coeff f (vStar m a b)))) := by
    rw [← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [hT]
  have hsum : dPsi R.Kf m f = ∑ v ∈ f.support, deltaB R.Kf m (PsiXY R.Kf m (monomial v (AddMonoidAlgebra.coeff f v))) := by
    conv_lhs => rw [dPsi_apply, f.as_sum]

    simp only [map_sum]
  obtain ⟨s0, sl⟩ := qtW_vStar m a b hm
  ext u
  by_cases hu : rowDeg u 0 = a + b ∧ rowDeg u (Fin.last m) = 0
  · rw [hsum, coeff_sum, Finset.sum_eq_single (vStar m a b)]
    · intro v hv hne
      by_contra hc
      apply hne
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (AddMonoidAlgebra.coeff f v)) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (AddMonoidAlgebra.coeff f v)) (Fin.last m) u hc
      exact qt_comb m a b v (hf v hv).1 (hf v hv).2 (by rw [← w0, hu.1]) (by rw [← wl, hu.2])
    · intro hv
      rw [notMem_support_iff.1 hv, monomial_zero, map_zero, map_zero, AddMonoidAlgebra.coeff_zero]
      rfl
  · have c1 : AddMonoidAlgebra.coeff (dPsi R.Kf m f) u = 0 := by
      by_contra hc
      exact hu ⟨h0 u hc, hl u hc⟩
    have c2 : AddMonoidAlgebra.coeff (deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (AddMonoidAlgebra.coeff f (vStar m a b))))) u = 0 := by
      by_contra hc
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) (Fin.last m) u hc
      exact hu ⟨by rw [w0, s0], by rw [wl, sl]⟩
    rw [c1, c2]

theorem topLineP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : TopLineP := by
  intro p n' R r hr a b Ψ hΨ h0 hl
  have hA : Antitone (nuOf (wtPQ (r + 1) a b)) := nuOf_anti _ (wtPQ_anti (r + 1) a b (by omega))
  obtain ⟨c, hc⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b Ψ hΨ h0 hl
  obtain ⟨c', hc'⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b (hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b)))
    (hwMem R.Kf _ _ le_rfl _ hA)
    (by have h := rowA_hw R.Kf _ _ hA 0; rwa [nuOf_wt_zero] at h)
    (by have h := rowA_hw R.Kf _ _ hA (Fin.last (r + 1)); rwa [nuOf_last] at h)
  have he := (hwMulP R.Kf _ _ _ hA hA).2
  set Z := deltaB R.Kf (r + 1) (PsiXY R.Kf (r + 1) (monomial (vStar (r + 1) a b) 1)) with hZ
  rw [hc', smul_eq_C_mul, map_mul, eval_C] at he
  rw [hc', hc, smul_eq_C_mul, smul_eq_C_mul, map_mul, eval_C, ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_assoc, mul_comm _ c', he, mul_one]

end Formalism.MainNotions.flipOneThree.Pf

end
end
end
