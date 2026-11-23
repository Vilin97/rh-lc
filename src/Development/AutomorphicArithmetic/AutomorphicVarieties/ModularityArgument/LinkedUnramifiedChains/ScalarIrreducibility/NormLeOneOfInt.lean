module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfIsFiniteLength
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsUnitOfInvIntegral
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DigitExpansionLattice

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.digit_expansion_lattice :
    ∀ {O Ω : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NormedField Ω] [IsUltrametricDist Ω] [Algebra O Ω]
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (ϖ : O) (hϖ : Irreducible ϖ) (hlt : ‖algebraMap O Ω ϖ‖ < 1)
        (S : Submodule O Ω) (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (E : Finset Ω) (hE : ∀ e ∈ E, e ∈ S)
        (hdig : ∀ s ∈ S, ∃ e ∈ E, ∃ s' ∈ S, s = e + ϖ • s'),
        Module.Finite O S := by
  intro O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig
  classical
  have hI : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hhaus : IsHausdorff (maximalIdeal O) S := by
    refine ⟨fun x hx => ?_⟩
    have hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n := by
      intro n
      have h := hx n
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      obtain ⟨t, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      have : (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω) := by
        simp [Algebra.smul_def]
      rw [this, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hS _ t.2)
    have hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
    have h0 : ‖(x : Ω)‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hpre : IsPrecomplete (maximalIdeal O) (E → O) := by
    refine ⟨fun g hg => ?_⟩
    have hcoord : ∀ {m : ℕ} (x : E → O),
        x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m := by
      intro m x hx i
      have h := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx
      rw [Submodule.map_smul''] at h
      have h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O) :=
        Submodule.smul_mono le_rfl le_top h
      simpa using h2
    have hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_
      intro m n hmn
      have h := (SModEq.sub_mem.1 (hg hmn))
      refine SModEq.sub_mem.2 ?_
      have h2 := hcoord _ h i
      simpa using h2
    choose L hL using hc
    refine ⟨L, fun n => ?_⟩
    refine SModEq.sub_mem.2 ?_
    have hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h := SModEq.sub_mem.1 (hL i n)
    simpa using h
  let v : E → S := fun e => ⟨e, hE e e.2⟩
  let f : (E → O) →ₗ[O] S := Fintype.linearCombination O v
  have hsurj : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_
    intro y
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, he, s', hs', hs⟩ := hdig s s.2
    refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    have hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩ := by
      simp [f, v, Fintype.linearCombination_apply_single]
    simp only [LinearMap.comp_apply, hf]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
      Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩
    apply Subtype.ext
    simp [hs]
  exact Module.Finite.of_surjective f hsurj
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResidueHomNorm

section

@[expose] public section

theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoPoint

section

@[expose] public section

theorem UpperTheory.Reformulated.B.CoPoint.coPt :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) [UpperTheory.V.Fr.IsCoef l ↥c.O] (R : Type)
    [inst_2 : CommRing R] [inst_3 : Algebra (↥c.O) R] [inst_4 : UpperTheory.V.Alg.IsCO (↥c.O) R]
    (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
    Module.Finite ↥c.O ↥y.range ∧
      (∀ (a : R), ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ (1 : ℝ)) ∧
        ∀ a ∈ IsLocalRing.maximalIdeal R,
          ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ <
            (1 :
              ℝ) := by
  intro l _ c _ R _ _ _ y
  obtain ⟨hint, hO, hm⟩ := UpperTheory.integral_dvr_norm l c.O
  have hO' : ∀ a : c.O, ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) a‖ ≤ 1 := hO
  have hres : ∀ x : R, ∃ a : c.O, x - algebraMap c.O R a ∈ IsLocalRing.maximalIdeal R :=
    UpperTheory.V.Alg.IsCO.res_surj
  obtain ⟨hb1, hb2⟩ := UpperTheory.residue_hom_norm (O := c.O) (Ω := Formalism.ConjugateSelfDual.Qbar l) hres hO' hint y
  refine ⟨?_, hb1, hb2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hJ : ∀ x : R, ∃ P : Polynomial c.O, P.Monic ∧ Polynomial.aeval x P ∈ RingHom.ker y := fun x => by
    obtain ⟨P, hP, h0⟩ := hint (y x) (hb1 x)
    refine ⟨P, hP, ?_⟩
    rw [RingHom.mem_ker]
    have h1 : Polynomial.aeval (y x) P = 0 := h0
    rw [Polynomial.aeval_algHom_apply] at h1
    exact h1
  have hfin := UpperTheory.monic_ideal_completion hres (RingHom.ker y) hJ ϖ hϖ
  have hlt : ‖algebraMap c.O (Formalism.ConjugateSelfDual.Qbar l) ϖ‖ < 1 :=
    hm ϖ hϖ.not_isUnit
  classical
  letI := Fintype.ofFinite (R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}))
  have key := UpperTheory.digit_expansion_lattice hO' ϖ hϖ hlt (Subalgebra.toSubmodule y.range)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      exact hb1 r)
    (Finset.univ.image fun q : R ⧸ (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) => y (Quotient.out q))
    (fun e he => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 he
      exact ⟨_, rfl⟩)
    (fun s hs => by
      obtain ⟨r, rfl⟩ := hs
      have hq : r - Quotient.out (Ideal.Quotient.mk (RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ}) r) ∈
          RingHom.ker y ⊔ Ideal.span {algebraMap c.O R ϖ} := by
        rw [← Ideal.Quotient.eq]
        simp [Ideal.Quotient.mk_out]
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ r, Finset.mem_univ _, rfl⟩, y a, ⟨a, rfl⟩, ?_⟩
      have h2 := congrArg y hjt
      rw [map_add (f := _), RingHom.mem_ker.1 hj, map_sub, map_mul, AlgHom.commutes] at h2
      rw [Algebra.smul_def, mul_comm]
      linear_combination -h2)
  exact key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NormLeOneOfInt

section

@[expose] public section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J

end UpperTheory.V.J

theorem UpperTheory.V.J.coPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        Module.Finite c.O y.range ∧ (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.CoPoint.coPt
end
end
