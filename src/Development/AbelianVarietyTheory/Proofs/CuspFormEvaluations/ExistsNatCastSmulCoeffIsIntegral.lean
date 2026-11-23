module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatSmulCoeffIsIntegral

section

@[expose] public section

namespace GlobalTheory.NatMultipleIntegralCoefficients

theorem exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (AddMonoidAlgebra.coeff ((N : K) • P) m) := by
  classical
  have halg : ∀ x : K, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
    intro x
    obtain ⟨y, hy, h⟩ := (halg x).exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · rw [e] at h
      simpa using h
    · rw [e] at h
      have h2 := h.neg
      simpa using h2
  choose n hn hi using hx
  refine ⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]
    refine IsIntegral.mul ?_ (hi _)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K)
      (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))
  · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.NatMultipleIntegralCoefficients
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_natCast_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, IsIntegral ℤ (((N : K) • P).coeff m) := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | (apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral ..)

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (t : k) (hP : P ∈ HHa r n k cc isX a) :
    t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1,
    fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_natCast_smul_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ N : ℕ, 0 < N ∧ (N : c.F) • P ∈ harmA c a n ∧ ((N : c.F) • P).support = P.support := by
  intro E _ _ _ H Dw l c a n P hP
  haveI := c.fin
  obtain ⟨N, hN, h⟩ := exists_natCast_smul_coeff_isIntegral (K := c.F) P
  refine ⟨N, hN, ⟨smul_mem_HHa _ hP, fun m => h m⟩, ?_⟩
  have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, hN']

end GlobalTheory
end
end
