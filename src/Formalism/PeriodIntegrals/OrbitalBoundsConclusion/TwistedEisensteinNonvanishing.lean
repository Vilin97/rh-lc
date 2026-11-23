module

public import Formalism.PeriodIntegrals.TwistedEisensteinNonvanishing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TestFunctionPeriodicity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumScaling
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.SumSliceEq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.FreeCoordinateAffineInvertible
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IntegralApproximationByInteger
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IsUnitRedP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.JacobianTransformationLaw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.SumSliceEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfHypotheses
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnfoldingMatrixFreeCoordinate

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumToGaussSum

section

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function

variable {E K : Type} [Field E] [NumberField E] [Field K]

section QTdef

variable (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι]

def QT (T : (ι → E) → (ι → E)) (c : K) : Prop :=
  ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
    Good P a' b' (fun t => H (T t)) ∧ RS P a' b' (fun t => H (T t)) = c * RS P a b H

variable {P}

theorem qt_comp {T1 T2 : (ι → E) → (ι → E)} {c1 c2 : K} (h1 : QT P T1 c1) (h2 : QT P T2 c2) :
    QT P (fun t => T1 (T2 t)) (c2 * c1) := by
  intro a b
  obtain ⟨a1, b1, h1'⟩ := h1 a b
  obtain ⟨a2, b2, h2'⟩ := h2 a1 b1
  refine ⟨a2, b2, fun H hH => ?_⟩
  obtain ⟨g1, r1⟩ := h1' H hH
  obtain ⟨g2, r2⟩ := h2' (fun t => H (T1 t)) g1
  exact ⟨g2, r2.trans (by rw [r1]; ring)⟩

theorem qt_congr {T T' : (ι → E) → (ι → E)} {c c' : K} (h : QT P T c) (hT : ∀ t, T' t = T t) (hc : c' = c) :
    QT P T' c' := by
  have hTT : T' = T := funext hT
  subst hTT
  subst hc
  exact h

def em (k l : ι) (d c β : E) (t : ι → E) : ι → E := update t k (d * t k + c * t l + β)

end QTdef

section Em

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

theorem weighted_sum_to_gauss_sum {N : ℕ} {f g : E → K} {c : K} (h : W1 P N N f = c * W1 P N N g) :
    Sg P N N f = c * Sg P N N g := by
  have hq0 : ((qOf P : K) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hK)
  unfold W1 at h
  apply mul_left_cancel₀ hq0
  rw [h]
  ring

theorem qt_em {ι : Type} [Fintype ι] [DecidableEq ι] (k l : ι) {d : E} (hd : d ≠ 0) (c β : E)
    (hkl : l ≠ k ∨ c = 0) : QT P (em k l d c β) ((qOf P : K) ^ vq P d) := by
  have hq0 := qE_ne P hp
  intro a b
  obtain ⟨gc, hgc⟩ := ia_bound P hN hp hq c
  obtain ⟨gβ, hgβ⟩ := ia_bound P hN hp hq β
  obtain ⟨gd, hgd⟩ := ia_bound P hN hp hq d
  obtain ⟨gi, hgi⟩ := ia_bound P hN hp hq d⁻¹
  obtain ⟨a2, b2, hsc⟩ := weighted_sum_scaling (K := K) hN hp hq hK hd (a + gc + gβ) b

  have hcl : ∀ t : ι → E, (∀ j, IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
        (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
          (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
      rw [pow_add, pow_add]
      ring
    rw [e]
    exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l))) (ia_mul P (ia_qpow P _) hgβ)
  have hcl' : ∀ t : ι → E, (∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    rcases hkl with hlk | hc0
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
          (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
            (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [pow_add, pow_add]
        ring
      rw [e]
      exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l hlk))) (ia_mul P (ia_qpow P _) hgβ)
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) = (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [hc0, pow_add]
        ring
      rw [e]
      exact ia_mul P (ia_qpow P _) hgβ
  have hupd : ∀ (t : ι → E) (u : E), c * update t k u l = c * t l := by
    intro t u
    rcases hkl with hlk | hc0
    · rw [update_of_ne hlk]
    · rw [hc0, zero_mul, zero_mul]
  refine ⟨a + gc + gβ + gi, b + gd + gc, fun H hH => ?_⟩
  have hgood : Good P (a + gc + gβ + gi) (b + gd + gc) (fun t => H (em k l d c β t)) := by
    refine ⟨fun t ht j => ?_, fun t δ hδ => ?_⟩
    · have hs := hH.1 _ ht
      have hoth : ∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j) := by
        intro j hj
        have := hs j
        rwa [em, update_of_ne hj] at this
      by_cases hj : j = k
      · subst hj
        have hx := hs j
        rw [em, update_self] at hx
        have e : (qOf P : E) ^ (a + gc + gβ + gi) * t j = ((qOf P : E) ^ gi * d⁻¹) *
            ((qOf P : E) ^ (gc + gβ) * ((qOf P : E) ^ a * (d * t j + c * t l + β)) -
              (qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
          rw [pow_add, pow_add, pow_add, pow_add]
          field_simp
          ring
        rw [e]
        exact ia_mul P hgi (ia_sub P (ia_mul P (ia_qpow P _) hx) (hcl' t hoth))
      · exact ia_up P (by omega) (hoth j hj)
    · have e : em k l d c β (t + δ) = em k l d c β t + update δ k (d * δ k + c * δ l) := by
        ext j
        by_cases hj : j = k
        · subst hj
          simp only [em, update_self, Pi.add_apply]
          ring
        · simp only [em, update_of_ne hj, Pi.add_apply]
      show H (em k l d c β (t + δ)) = H (em k l d c β t)
      rw [e]
      apply hH.2
      intro j
      by_cases hj : j = k
      · subst hj
        rw [update_self]
        have e2 : (d * δ j + c * δ l) / (qOf P : E) ^ b = ((qOf P : E) ^ gd * d) * (δ j / (qOf P : E) ^ (b + gd)) +
            ((qOf P : E) ^ gc * c) * (δ l / (qOf P : E) ^ (b + gc)) := by
          rw [pow_add, pow_add]
          field_simp
        rw [e2]
        exact ia_add P (ia_mul P hgd (ia_div_down P hp (by omega) (hδ j)))
          (ia_mul P hgc (ia_div_down P hp (by omega) (hδ l)))
      · rw [update_of_ne hj]
        exact ia_div_down P hp (by omega) (hδ j)
  refine ⟨hgood, ?_⟩
  set N := max (max (a + gc + gβ + gi) (b + gd + gc)) (max (max a2 b2) (a + gc + gβ + b)) with hNdef
  rw [← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hgood,
    ← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hH]
  have key : ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H (em k l d c β t) =
      (qOf P : K) ^ vq P d * ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H t := by
    have h0 := sum_slice_eq k (fun _ : ι => valsQ E (qOf P) N N) (valsQ E (qOf P) N N) (valsQ E (qOf P) N N)
      (fun t => H (em k l d c β t)) H ((qOf P : K) ^ vq P d) ?_
    · rwa [update_eq_self k (fun _ : ι => valsQ E (qOf P) N N)] at h0
    intro t
    have e1 : ∀ u, em k l d c β (update t k u) = update t k (d * u + (c * t l + β)) := by
      intro u
      rw [em, update_idem, update_self, hupd, add_assoc]
    simp only [e1]
    by_cases hz : ∀ u, H (update t k u) = 0
    · rw [Finset.sum_eq_zero (fun u _ => hz _), Finset.sum_eq_zero (fun u _ => hz _), mul_zero]
    simp only [not_forall] at hz
    obtain ⟨u0, hu0⟩ := hz
    have hs := hH.1 _ hu0
    have hβ' : IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
      apply hcl'
      intro j hj
      have := hs j
      rwa [update_of_ne hj] at this
    obtain ⟨gψ, eψ⟩ := sg_transl hN hp hq (good_function_mono (by omega) (good_slice hH t k)) hβ'
    obtain ⟨gs, es⟩ := hsc _ gψ
    have s1 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k (d * u + (c * t l + β))) =
        Sg P N N (fun u => H (update t k (d * u + (c * t l + β)))) := sum_vals hp N N _
    have s2 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k u) = Sg P N N (fun u => H (update t k u)) :=
      sum_vals hp N N _
    rw [s1, s2]
    apply weighted_sum_to_gauss_sum hN hp hq hK
    have w1 : W1 P N N (fun u => H (update t k (d * u + (c * t l + β)))) =
        W1 P a2 b2 (fun u => H (update t k (d * u + (c * t l + β)))) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) gs
    have w2 : W1 P N N (fun u => H (update t k u)) = W1 P (a + gc + gβ) b (fun u => H (update t k u)) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) (good_function_mono (by omega) (good_slice hH t k))
    rw [w1, es, w2]
    unfold W1
    rw [eψ]
  unfold RS
  rw [key]
  ring

end Em

end PI.TwistedEisensteinNonvanishing.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.ChangeVariablesDeterminantOne

section

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function Matrix

variable {E K : Type} [Field E] [NumberField E] [Field K]

theorem qt_id {P : HeightOneSpectrum (𝓞 E)} {ι : Type} [Fintype ι] [DecidableEq ι] :
    QT P (fun t : ι → E => t) (1 : K) :=
  fun a b => ⟨a, b, fun _ h => ⟨h, (one_mul _).symm⟩⟩

section Lin

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem qt_transvec (t : TransvectionStruct ι E) :
    QT P (fun v => t.toMatrix *ᵥ v) ((qOf P : K) ^ vq P t.toMatrix.det) := by
  have hmv : ∀ v : ι → E, t.toMatrix *ᵥ v = em t.i t.j 1 t.c 0 v := by
    intro v
    funext k
    by_cases h : k = t.i
    · subst h
      simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em] <;> ring
    · simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em, h]
  exact qt_congr (qt_em hN hp hq hK t.i t.j one_ne_zero t.c 0 (Or.inl t.hij.symm)) hmv (by rw [t.det])

theorem qt_diag (D : ι → E) (hD : ∀ i, D i ≠ 0) :
    QT P (fun v => diagonal D *ᵥ v) ((qOf P : K) ^ vq P (diagonal D).det) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then D k * v k else v k)
      ((qOf P : K) ^ (∑ k ∈ s, vq P (D k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) (by simp)
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a (hD a) 0 0 (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [Finset.sum_insert ha, zpow_add₀ hK, mul_comm]
  refine qt_congr (key Finset.univ) (fun v => by funext k; simp [Matrix.mulVec_diagonal]) ?_
  rw [Matrix.det_diagonal, vq_prod (s := Finset.univ) (f := D) (hf := fun i _ => hD i)]
  all_goals assumption

theorem qt_matrix (M : Matrix ι ι E) (hM : M.det ≠ 0) :
    QT P (fun v => M *ᵥ v) ((qOf P : K) ^ vq P M.det) := by
  classical
  obtain ⟨L, L', D, hMLD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hlist : ∀ l : List (TransvectionStruct ι E),
      QT P (fun v => (l.map TransvectionStruct.toMatrix).prod *ᵥ v) (1 : K) := by
    intro l
    induction l with
    | nil => exact qt_congr qt_id (fun v => by simp) rfl
    | cons t l ih =>
      refine qt_congr (qt_comp (qt_transvec hN hp hq hK t) ih) (fun v => by simp [Matrix.mulVec_mulVec]) ?_
      rw [t.det, vq_one, zpow_zero, one_mul]
      all_goals assumption
  have hl1 : ∀ l : List (TransvectionStruct ι E), ((l.map TransvectionStruct.toMatrix).prod).det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => simp [Matrix.det_mul, t.det, ih]
  have hdetM : M.det = (diagonal D).det := by
    rw [hMLD, Matrix.det_mul, Matrix.det_mul, hl1, hl1, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hM
    rw [hdetM, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine qt_congr (qt_comp (hlist L) (qt_comp (qt_diag hN hp hq hK D hD) (hlist L')))
    (fun v => by rw [hMLD]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]) ?_
  rw [hdetM, one_mul, mul_one]

theorem qt_transl (τ : ι → E) : QT P (fun v : ι → E => v + τ) (1 : K) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then v k + τ k else v k) (1 : K) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) rfl
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a one_ne_zero 0 (τ a) (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [vq_one, zpow_zero, one_mul]
        all_goals assumption
  exact qt_congr (key Finset.univ) (fun v => by funext k; simp) rfl

theorem qt_aff (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E) :
    QT P (fun t => L t + τ) ((qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)))) := by
  have hL : ∀ t, L t = LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E)) *ᵥ t :=
    fun t => (LinearMap.toMatrix'_mulVec _ t).symm
  have hdet : (LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E))).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' L).ne_zero
  refine qt_congr (qt_comp (qt_transl hN hp hq hK τ) (qt_matrix hN hp hq hK _ hdet))
    (fun t => by simp only [hL]) ?_
  rw [LinearMap.det_toMatrix', mul_one]

end Lin

theorem cov_of (hN : NTAll) : CoVP := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ
  exact ⟨(qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E))), zpow_ne_zero _ hK,
    qt_aff hN hp hq hK L τ⟩

end PI.TwistedEisensteinNonvanishing.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfRemaining

section

@[expose] public section

namespace PI.TwistedEisensteinNonvanishing.W

theorem ntAll : NTAll := ⟨integer_integral_iff_dvd, integral_approximation_by_integer, element_eq_prime_power_mul_unit, valuation_exponent_unique, unit_congruent_to_integer⟩

theorem twisted_eisenstein_of_remaining (hPS : PhiSuppP) (hPP : PhiPerP) (hBE : BddEntP) : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  twisted_eisenstein_of_hypotheses (stab_of ntAll) (cov_of ntAll) (omStep_of jacobian_transformation_law (muNe_of ntAll)) hPS hPP hBE translated_function_support
    translated_function_invariance unfolding_integrand_good character_argument_bounded unfolding_affine_space_invariant free_coordinate_affine_invertible restriction_to_affine_surjective character_argument_constant_shift

end PI.TwistedEisensteinNonvanishing.W
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwistedEisensteinNonvanishing

section

@[expose] public section

theorem TwistedEisensteinNonvanishing : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing :=
  PI.TwistedEisensteinNonvanishing.W.twisted_eisenstein_of_remaining PI.TwistedEisensteinNonvanishing.W.test_function_support PI.TwistedEisensteinNonvanishing.W.test_function_periodicity PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries
end
end
