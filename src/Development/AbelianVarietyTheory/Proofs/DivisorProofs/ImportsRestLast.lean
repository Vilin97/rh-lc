module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IntLatMul

theorem main : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  intro d Λ hd hΛ
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast, hw2]
    ring
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxi, a, b, hab⟩ := (hΛ x).1 hx
    refine (hΛ _).2 ⟨hwi.mul hxi, -(b * d), a, ?_⟩
    rw [hab]
    push_cast
    linear_combination (b : ℂ) * hw2
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    simp [hw, hs.ne']

end GlobalTheory.IntLatMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrtStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  first | exact @GlobalTheory.IntLatMul.main | exact GlobalTheory.IntLatMul.main | (intros; apply GlobalTheory.IntLatMul.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMulTorsMemLatticeIff

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

theorem natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b

end GlobalTheory.WpFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestLast

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ hτ).1
    refine GlobalTheory.T.denominator_bound_weierstrass_cm_torsion l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
end
end
