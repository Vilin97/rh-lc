module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortOfSixUnitStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCubeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisStableTorsionFamilyKerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralModelOfGaloisStableTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStableStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIntegralModelOfForms
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.GaloisValuations.GlobalB
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortTwistFourMulAddOne

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem modelAt_shortTwist_four_mul_add_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  intro V F a₄ a₆ D k _ _ h
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  set d : ℂ := 4 * (k : ℂ) + 1 with hd
  have hkV : (k : ℂ) ∈ V := intCast_mem V k
  have hdV : d ∈ V := add_mem (mul_mem (by exact_mod_cast intCast_mem V 4 : (4 : ℂ) ∈ V) hkV) (one_mem V)
  have hkF : (k : ℂ) ∈ F := by simpa using IntermediateField.intCast_mem F k
  have hdF : d ∈ F := F.add_mem (F.mul_mem (by simpa using IntermediateField.intCast_mem F 4) hkF) F.one_mem
  let W₀ : WeierstrassCurve ℂ := ⟨0, 0, 0, a₄, a₆⟩
  let C' : VariableChange ℂ := ⟨C.u, d * C.r, C.s, d * C.t⟩
  refine ⟨C', hu, F.mul_mem hdF hr, hs, F.mul_mem hdF ht, ?_, ?_⟩
  · have e1 : (C' • shortTwist d a₄ a₆).a₁ = (C • W₀).a₁ := by
      simp only [variableChange_a₁, shortTwist, W₀, C']
    have e2 : (C' • shortTwist d a₄ a₆).a₂ = d * (C • W₀).a₂ + k * (C • W₀).a₁ ^ 2 := by
      simp only [variableChange_a₁, variableChange_a₂, shortTwist, W₀, C', hd]; ring
    have e3 : (C' • shortTwist d a₄ a₆).a₃ = d * (C • W₀).a₃ := by
      simp only [variableChange_a₃, shortTwist, W₀, C']; ring
    have e4 : (C' • shortTwist d a₄ a₆).a₄ = d ^ 2 * (C • W₀).a₄ + 2 * k * d * (C • W₀).a₁ * (C • W₀).a₃ := by
      simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, shortTwist, W₀, C', hd]; ring
    have e6 : (C' • shortTwist d a₄ a₆).a₆ = d ^ 3 * (C • W₀).a₆ + k * d ^ 2 * (C • W₀).a₃ ^ 2 := by
      simp only [variableChange_a₃, variableChange_a₆, shortTwist, W₀, C', hd]; ring
    have h2V : (2 : ℂ) ∈ V := by simpa using intCast_mem V 2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact add_mem (mul_mem hdV h2) (mul_mem hkV (pow_mem h1 2))
    · rw [e3]; exact mul_mem hdV h3
    · rw [e4]; exact add_mem (mul_mem (pow_mem hdV 2) h4)
        (mul_mem (mul_mem (mul_mem (mul_mem h2V hkV) hdV) h1) h3)
    · rw [e6]; exact add_mem (mul_mem (pow_mem hdV 3) h6)
        (mul_mem (mul_mem hkV (pow_mem hdV 2)) (pow_mem h3 2))
  · have eΔ : (C' • shortTwist d a₄ a₆).Δ = d ^ 6 * (C • W₀).Δ := by
      rw [variableChange_Δ, variableChange_Δ]
      simp only [C', W₀, shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [eΔ, map_mul, map_mul, hΔ]

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortTwistFourMulAddOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  first | exact @GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | exact GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | (intros; apply GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromP

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul hβ)
      exact GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp hp4 hp3 hD).2 hQ)
      (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromPStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  first | exact @GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | exact GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | (intros; apply GlobalTheory.CMModel.modelAt_one_of_sqProd_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCu

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll


open GlobalTheory.CMModel.LocAll in
theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCuStatement

section

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  first | exact @GlobalTheory.CMModel.twist_modelAt_all | exact GlobalTheory.CMModel.twist_modelAt_all | (intros; apply GlobalTheory.CMModel.twist_modelAt_all <;> assumption)
end
end
