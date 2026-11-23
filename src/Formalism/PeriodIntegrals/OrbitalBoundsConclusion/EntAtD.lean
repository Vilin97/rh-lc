module

public import Formalism.PeriodIntegrals.EntAtD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.ExpCoeff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapComm

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem pderiv_pderiv_comm {σ R : Type} [CommRing R] (v w : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w f) = MvPolynomial.pderiv w (MvPolynomial.pderiv v f) := by
  have hX : ∀ i j k : σ, MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
    intro i j k
    by_cases h : k = j
    · subst h; simp
    · simp [MvPolynomial.pderiv_X_of_ne h]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hX, mul_zero, zero_add, hp]
    ring

theorem pd_comm {H : Type} {N0 N1 : ℕ} (v w : XZ (Bool × H) N0 N1) :
    Commute (pd (H := H) (N0 := N0) (N1 := N1) v) (pd w) := by
  refine LinearMap.ext fun f => ?_
  exact pderiv_pderiv_comm (R := ℤ) v w f

theorem pLapComm : PLapComm := by
  intro H N0 N1 t t'
  unfold lapT
  refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
  refine Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact ((pd_comm _ _).mul_right (pd_comm _ _)).mul_left ((pd_comm _ _).mul_right (pd_comm _ _))

end PI.EntAtD.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.MinorAff

section

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

open PI.EntAtD

section DerDet

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem minorAff_derProd {ι : Type} [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.erase_insert_of_ne (by rintro rfl; exact hi hk),
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)), mul_assoc]

theorem minorAff_derDet (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    D M.det = ∑ i, (M.updateCol i (fun r => D (M r i))).det := by
  classical

  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, minorAff_derProd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∏ j, (M.updateCol i (fun r => D (M r i))) (σ j) j =
      D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  rw [Units.smul_def, h1, mul_comm]

theorem minorAff_sumApply {ι : Type} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

end DerDet

theorem pMinorAff : PMinorAff := by
  intro H N0 N1 t k I b b'
  classical
  let y : Fin k → PolyXZ H N0 N1 := fun i => ∑ a : Fin N0,
    (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
      MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a))
  have hD : ∀ (bb : Fin N1) (f : PolyXZ H N0 N1), dRow (N0 := N0) t 0 bb f =
      ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
        MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, bb)) f := by
    intro bb f
    simp only [dRow]
    rw [minorAff_sumApply]
    simp only [Derivation.smul_apply, smul_eq_mul]
  have hE : ∀ (bb c : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb
      (∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
        MvPolynomial.X (Sum.inr ((true, t), a, c))) = if c = bb then y i else 0 := by
    intro bb c i
    rw [hD]
    by_cases hc : c = bb
    · subst hc

      simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]

    · simp [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hc]
  have hy : ∀ (bb : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb (y i) = 0 := by
    intro bb i
    rw [hD]

    simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [minorXZ]

  rw [minorAff_derDet, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : I c = b'
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = y := by
      funext r
      rw [Matrix.of_apply, hE, if_pos hc]
    rw [hcol, minorAff_derDet]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = c
    · subst hl
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro r
      simp only [Matrix.updateCol_self, hy]
    · by_cases hIl : I l = b
      · apply Matrix.det_zero_of_column_eq hl
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.updateCol_ne (Ne.symm hl),
          Matrix.of_apply, hE, if_pos hIl]
      · apply Matrix.det_eq_zero_of_column_eq_zero l
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.of_apply, hE, if_neg hIl]
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = fun _ => 0 := by
      funext r
      rw [Matrix.of_apply, hE, if_neg hc]
    rw [hcol]
    convert map_zero (dRow (N0 := N0) t 0 b)
    exact Matrix.det_eq_zero_of_column_eq_zero c fun r => Matrix.updateCol_self

end PI.EntAtD.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.SDegMul

section

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

section SDeg

variable {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)

theorem sdegMul_zero : ∀ k : ℕ, SDegD d k (0 : A)
  | 0 => fun j => by simp
  | k + 1 => fun j => by simpa using sdegMul_zero k

theorem sdegMul_add : ∀ (k : ℕ) (a b : A), SDegD d k a → SDegD d k b → SDegD d k (a + b)
  | 0, a, b, ha, hb => fun j => by simp [map_add (f := _), ha j, hb j]
  | k + 1, a, b, ha, hb => fun j => by
    rw [map_add (f := _)]
    exact sdegMul_add k _ _ (ha j) (hb j)

theorem symbol_degree_mul : ∀ (n k l : ℕ) (f g : A), k + l = n → SDegD d k f → SDegD d l g → SDegD d n (f * g) := by
  intro n
  induction n with
  | zero =>
    intro k l f g hn hf hg
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := ⟨by omega, by omega⟩
    intro j
    simp only [Derivation.leibniz, hf j, hg j, smul_zero, add_zero]
  | succ n ih =>
    intro k l f g hn hf hg j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    apply sdegMul_add
    · cases l with
      | zero => rw [show d j g = 0 from hg j, mul_zero]; exact sdegMul_zero d n
      | succ l => exact ih k l f (d j g) (by omega) hf (hg j)
    · cases k with
      | zero => rw [show d j f = 0 from hf j, mul_zero]; exact sdegMul_zero d n
      | succ k => exact ih l k g (d j f) (by omega) hg (hf j)

end SDeg

theorem pSDegMul : PSDegMul := by
  intro A _ ι d f g k l hf hg
  exact symbol_degree_mul d (k + l) k l f g rfl hf hg

end PI.EntAtD.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD

section

@[expose] public section

theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
end
end
