module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
public import Formalism.PeriodIntegrals.WwInjective
public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.GramVanish

section

@[expose] public section

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial

theorem gram_vanish {σ ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (f : ι → MvPolynomial σ ℤ) (ph : MvPolynomial σ K →ₗ[K] K)
    (h : ∑ i, ph (map (Int.castRingHom K) (f i)) • map (Int.castRingHom K) (f i) = 0)
    (i : ι) : ph (map (Int.castRingHom K) (f i)) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ι → MvPolynomial σ K, ∀ j, g j = map (Int.castRingHom K) (f j) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hg] at h ⊢
  have key : ∀ l : Module.Dual ℚ K, ∀ j, l (ph (g j)) = 0 := by
    intro l
    have lin : ∀ (x : K) (n : ℤ), algebraMap ℚ K (l x) * (n : K) = algebraMap ℚ K (l (x * n)) := by
      intro x n
      rw [show x * (n : K) = n • x by rw [zsmul_eq_mul, mul_comm], map_zsmul, zsmul_eq_mul,
        map_mul, map_intCast, mul_comm]
    have hrel : ∑ j, algebraMap ℚ K (l (ph (g j))) • g j = 0 := by
      ext s
      have hs := congrArg (fun p => l (AddMonoidAlgebra.coeff p s)) h

      simp only [coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_sum, map_zero] at hs
      have e : ∀ j, AddMonoidAlgebra.coeff (g j) s = ((AddMonoidAlgebra.coeff (f j) s : ℤ) : K) := fun j => by
        rw [hg, coeff_map, eq_intCast]
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul]
      calc ∑ j, algebraMap ℚ K (l (ph (g j))) * AddMonoidAlgebra.coeff (g j) s
          = ∑ j, algebraMap ℚ K (l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [e j, lin]
        _ = algebraMap ℚ K (∑ j, l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by rw [map_sum]
        _ = 0 := by rw [hs, map_zero]
    have hsum : ∑ j, l (ph (g j)) ^ 2 = 0 := by
      have h1 : l (ph (∑ j, algebraMap ℚ K (l (ph (g j))) • g j)) = 0 := by
        rw [hrel, map_zero, map_zero]

      rw [map_sum, map_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul, sq]
    intro j
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ l (ph (g k)) ^ 2 := fun k _ => sq_nonneg _
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ j)
    exact (pow_eq_zero_iff two_ne_zero).mp hj
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (ph (g i))).mp (fun l => key l i)

end PI.WwInjectiveWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice

section

@[expose] public section

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial PI.WwInjective PI.WwInjective.KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)

noncomputable instance instFintypeColChoice : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

theorem eval_map_nablaX {K : Type} [CommRing K] (J : ColChoice N nu)
    (pt : Lt × ℕ × Fin N → K) :
    eval pt (map (Int.castRingHom K) (nablaX N nu J)) = minY N nu J (fun s a i => pt (s, i, a)) := by
  unfold nablaX minY
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem deX_eq_sum (hCB : PI.WwCauchyBinet.WwCauchyBinet) {K : Type} [CommRing K]
    (y : Lt → Fin N → ℕ → K) :
    DeX N nu y = ∑ J : ColChoice N nu, C (minY N nu J y) *
      map (Int.castRingHom K) (nablaX N nu J) := by
  have h := hCB Lt K N nu y
  have h' : (∑ᶠ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J)) =
      ∑ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J) :=
    finsum_eq_sum_of_fintype _
  rw [← h']
  exact h

theorem sum_smul_eq_zero (hCB : PI.WwCauchyBinet.WwCauchyBinet) (l : ℕ) [Fact l.Prime]
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l]))
    (hph : ∀ y, ph (DeX N nu y) = 0) :
    ∑ J : ColChoice N nu, ph (map (Int.castRingHom ℂ_[l]) (nablaX N nu J)) •
      map (Int.castRingHom ℂ_[l]) (nablaX N nu J) = 0 := by
  haveI : Infinite ℂ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  have hx := hph (fun s a i => x (s, i, a))

  rw [deX_eq_sum N nu hCB, map_sum] at hx
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul] at hx

  simp only [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
  eval_map_nablaX, map_zero]
  refine Eq.trans ?_ hx
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

theorem wwInjective_of (hCB : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by
  unfold PI.WwInjective.WwInjective
  intro Lt _ _ l _ N nu ph hph J
  exact gram_vanish (fun J => nablaX N nu J) ph (sum_smul_eq_zero N nu hCB l ph hph) J

end PI.WwInjectiveWork
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective

section

@[expose] public section

theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold

section

@[expose] public section

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns
end
end
