module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Mathlib.NumberTheory.Padics.Complex
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
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Tactic.Lemma

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormDetLeAlt

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh59.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh59.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh59.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) M.det‖ ≤ R ^ n := by
  intro l inst ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR

  rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : UpperTheory.Reformulated.B.Qh59.Qbar l)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  have h2 : ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ R ^ n := by
    calc ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
      _ = R ^ n := by simp
  calc _ ≤ 1 * R ^ n :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = R ^ n := one_mul _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetBound

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private lemma norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh59.norm_det_le ι M R hR h

theorem UpperTheory.Gal.Gen.detBound_pf :
    UpperTheory.Gal.Gen.DetBound := by
  intro l _ ι T _ n lam A R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [pow_mul]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k
end
end
