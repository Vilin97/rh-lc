module

public import Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
public import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts
import Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
import Mathlib.RingTheory.Henselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorOfRootSubsetProductEquation
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootSubsetProductEquationOfHenselianReduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.EtaleCohomology.EtaleSheaves.FiniteChartSurjPf
import Development.EtaleCohomology.EtaleSheaves.HensIdemCut
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.EtaleCohomology.EtaleSheaves.HensIdemCut
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts.EtaleSurjectiveChartOfFiniteChartSurj

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorLiftOfPowMulSubOnePow

section

section

noncomputable section
open Polynomial

theorem UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m := by
  intro A _ I _ g hg n m hgm
  by_cases hR : Nontrivial (A ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact ⟨g, 1, hg, monic_one, (mul_one g).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI := hR
  haveI hA : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  have h1 : ((X : (A ⧸ I)[X]) - 1) = X - C 1 := by simp
  have hdeg : g.natDegree = n + m := by
    have h := congrArg natDegree hgm
    rw [hg.natDegree_map, h1, (monic_X_pow n).natDegree_mul ((monic_X_sub_C 1).pow m),
      natDegree_X_pow, (monic_X_sub_C (1 : A ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one] at h
    exact h
  obtain ⟨α, c, hα, hc⟩ := UpperTheory.exists_root_subset_product_equation_of_henselian_reduction A I g n m (n + m) rfl hg hdeg hgm
  obtain ⟨P, Q, hP, hQ, hPQ, hQd, hQm, hQ0⟩ := UpperTheory.exists_monic_factor_of_root_subset_product_equation A g n m (n + m) rfl hg hdeg α c hc
  have hQdeg : Q.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQm]; exact one_ne_zero)
  have hPdeg : P.natDegree = n := by
    have h := hP.natDegree_mul hQ
    rw [← hPQ, hdeg, hQdeg] at h
    omega
  set φ := Ideal.Quotient.mk I
  have hPb : (P.map φ).Monic := hP.map φ
  have hprod : P.map φ * Q.map φ = X ^ n * (X - 1) ^ m := by
    rw [← Polynomial.map_mul, ← hPQ, hgm]
  have hQ0b : (Q.map φ).eval 0 = (-1) ^ m := by
    rw [eval_zero_map, hQ0, map_mul, map_pow, map_neg, map_one, Ideal.Quotient.eq.mpr hα, map_one, mul_one]
  have hcop : IsCoprime (X : (A ⧸ I)[X]) (Q.map φ) := by
    have hd : X ∣ Q.map φ - C ((Q.map φ).coeff 0) := X_dvd_sub_C
    obtain ⟨r, hr⟩ := hd
    rw [coeff_zero_eq_eval_zero, hQ0b] at hr
    refine ⟨-(C ((-1) ^ m) * r), C ((-1) ^ m), ?_⟩
    have hu : ((-1 : A ⧸ I) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc -(C ((-1) ^ m) * r) * X + C ((-1) ^ m) * Q.map φ
        = C ((-1) ^ m) * (Q.map φ - X * r) := by ring
      _ = 1 := by rw [← hr, sub_sub_cancel, ← C_mul, hu, C_1]
  obtain ⟨s, hs⟩ := hcop.pow_left.dvd_of_dvd_mul_right ⟨(X - 1) ^ m, hprod⟩
  have hsm : s.Monic := (monic_X_pow n).of_mul_monic_left (by rw [← hs]; exact hPb)
  have hsdeg : s.natDegree = 0 := by
    have h := congrArg natDegree hs
    rw [hP.natDegree_map φ, (monic_X_pow n).natDegree_mul hsm, natDegree_X_pow, hPdeg] at h
    omega
  have hs1 : s = 1 := eq_one_of_monic_natDegree_zero hsm hsdeg
  have hPmap : P.map φ = X ^ n := by rw [hs, hs1, mul_one]
  have hQmap : Q.map φ = (X - 1) ^ m := by
    rw [hPmap] at hprod
    have h : X ^ n * (Q.map φ - (X - 1) ^ m) = 0 := by rw [mul_sub, hprod, sub_self]
    exact sub_eq_zero.mp ((monic_X_pow n).mul_right_eq_zero_iff.mp h)
  exact ⟨P, Q, hP, hQ, hPQ, hPmap, hQmap⟩

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds

section

section

noncomputable section

theorem UpperTheory.liftIdempotentFactorization_holds :
    LateralTheory.E.LIdemLiftPf.LFact := by
  intro A _ I _ g hg n m h
  exact UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow A I g hg n m h

end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LIdemPf

section

section

noncomputable section
open Polynomial

namespace LateralTheory.E.LIdemPf

theorem LIdem_of : LateralTheory.E.HensIdemCut.LIdem := by
  intro A _ I B _ φ hJ b hb N g h hg hh hgh
  set J := I.map φ with hJdef
  let π := Ideal.Quotient.mk J
  let ψ : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hcomp : ψ.comp (Ideal.Quotient.mk I) = π.comp φ := by
    ext a; simp [ψ, π, Ideal.quotientMap_mk]
  have key : ∀ p : A[X], π (p.eval₂ φ b) = (p.map (Ideal.Quotient.mk I)).eval₂ ψ (π b) := by
    intro p
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  set G := g.eval₂ φ b with hGdef
  set H := h.eval₂ φ b with hHdef
  set e := π b with hedef
  have hG : π G = e ^ N := by rw [key, hg]; simp
  have hH : π H = (e - 1) ^ N := by rw [key, hh]; simp [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]
  have he : e * e = e := by
    have : π (b * b - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_mul] at this
    exact sub_eq_zero.mp this
  have hcop : IsCoprime (e ^ N) ((e - 1) ^ N) :=
    (show IsCoprime e (e - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v', rfl⟩ := Ideal.Quotient.mk_surjective v
  set s := u' * G + v' * H with hsdef
  have hs : π s = π 1 := by
    simp only [hsdef, map_add (f := _), map_mul, hG, hH, map_one]
    exact huv
  have hsJ : s - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := hJ (Ideal.Quotient.eq.mp hs)
  have hunit : IsUnit s := by
    have := (Ideal.mem_jacobson_bot.mp hsJ) 1
    simpa using this
  obtain ⟨w, hw⟩ := hunit
  have hsum : (↑w⁻¹ * u') * G + (↑w⁻¹ * v') * H = 1 := by
    have : (↑w⁻¹ : B) * s = 1 := by rw [← hw]; exact Units.inv_mul w
    rw [hsdef] at this
    linear_combination this
  refine ⟨(↑w⁻¹ * u') * G, ?_, ?_⟩
  · show (↑w⁻¹ * u') * G * ((↑w⁻¹ * u') * G) = (↑w⁻¹ * u') * G
    linear_combination ((↑w⁻¹ * u') * G) * hsum - (↑w⁻¹ * u') * (↑w⁻¹ * v') * hgh
  · rw [← Ideal.Quotient.eq]
    change π ((↑w⁻¹ * u') * G) = e
    have hsum' := congrArg π hsum
    simp only [map_add (f := _), map_mul, map_one, hG, hH] at hsum' ⊢
    set α := π ↑w⁻¹ * π u'
    set γ := π ↑w⁻¹ * π v'
    cases N with
    | zero =>
      have h0 : (1 : B ⧸ J) = 0 := by
        have := congrArg π hgh
        simpa [map_mul, hG, hH] using this
      have := subsingleton_of_zero_eq_one h0.symm
      exact Subsingleton.elim _ _
    | succ n =>
      have hp : e ^ (n + 1) = e := IsIdempotentElem.pow_succ_eq n he
      have h1 : e * (e - 1) ^ (n + 1) = 0 := by
        calc e * (e - 1) ^ (n + 1) = (e * e - e) * (e - 1) ^ n := by ring
          _ = 0 := by rw [he, sub_self, zero_mul]
      rw [hp] at hsum' ⊢
      linear_combination e * hsum' - α * he - γ * h1

end LateralTheory.E.LIdemPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LJacPf

section

@[expose] public section

namespace LateralTheory.E.LJacPf

theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := by simpa only [Ideal.jacobson_bot] using hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LMonicPf

section

section

noncomputable section
open Polynomial

namespace LateralTheory.E.LMonicPf

theorem map_mk_eq_X_pow {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) (hp : p.Monic)
    (h : ∀ i ≠ p.natDegree, p.coeff i ∈ I) :
    p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
  ext i
  rw [coeff_map, coeff_X_pow]
  split_ifs with hi
  · subst hi; rw [hp.coeff_natDegree, map_one]
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i hi)

theorem LMonic_of : LateralTheory.E.HensIdemCut.LMonic := by
  intro A _ I B _ φ hφ b hb
  cases subsingleton_or_nontrivial A
  · have : Subsingleton B := by
      refine ⟨fun x y => ?_⟩
      rw [← mul_one x, ← mul_one y, ← map_one φ, Subsingleton.elim (1 : A) 0, map_zero,
        mul_zero, mul_zero]
    exact ⟨0, 1, monic_one, Subsingleton.elim _ _, by simp⟩
  let := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  obtain ⟨p, hpm, hp0, hpI⟩ :=
    exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B) (I := I) (x := b * b - b) hb
  have hqe : ((X : A[X]) * X - X) = X ^ 2 - X := by rw [sq]
  have hq : ((X : A[X]) * X - X).Monic := by
    rw [hqe]
    exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have hqd : ((X : A[X]) * X - X).natDegree ≠ 0 := by
    intro h
    have h1 := congrArg (eval 0) ((Polynomial.Monic.natDegree_eq_zero hq).mp h)
    simp at h1
  refine ⟨p.natDegree, p.comp (X * X - X), hpm.comp hq hqd, ?_, ?_⟩
  · rw [eval₂_comp]
    simp only [eval₂_mul, eval₂_sub, eval₂_X]
    rw [aeval_def] at hp0
    exact hp0
  · rw [Polynomial.map_comp, map_mk_eq_X_pow I p hpm hpI, X_pow_comp, ← mul_pow]
    congr 1
    simp [C_1]
    ring
end LateralTheory.E.LMonicPf
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.HenselianIdempotents

section

@[expose] public section

namespace UpperTheory.Et.HenselianIdempotents

theorem a0 : LateralTheory.E.HensIdemCut.LJac := LateralTheory.E.LJacPf.LJac_of
theorem a1 : LateralTheory.E.HensIdemCut.LMonic := LateralTheory.E.LMonicPf.LMonic_of
theorem a2 : LateralTheory.E.LIdemLiftPf.LFact := UpperTheory.liftIdempotentFactorization_holds
theorem a3 : LateralTheory.E.LChartPf.LIdemLift := LateralTheory.E.LIdemLiftPf.LIdemLift_of a2
theorem a4 : LateralTheory.E.LSurjChartPf.FiniteChartSurj := LateralTheory.E.FiniteChartSurjPf.FiniteChartSurj_of
theorem a5 : LateralTheory.E.LChartPf.LSurjChart := LateralTheory.E.LSurjChartPf.etale_surjective_chart_of_finite_chart_surj a4
theorem a6 : LateralTheory.E.LEtaleLiftPf.LChart := LateralTheory.E.LChartPf.LChart_of a3 a5
theorem a7 : LateralTheory.E.LFactorPf.LEtaleLift := LateralTheory.E.LEtaleLiftPf.LEtaleLift_of a6
theorem a8 : LateralTheory.E.HensIdemCut.LFactor := LateralTheory.E.LFactorPf.LFactor_of a7
theorem a9 : LateralTheory.E.HensIdemCut.LIdem := LateralTheory.E.LIdemPf.LIdem_of
theorem a10 : LateralTheory.E.t_E1Cut.HensIdem := LateralTheory.E.HensIdemCut.goal_of a0 a1 a8 a9

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.HensIdem := a10

end UpperTheory.Et.HenselianIdempotents
end
end
