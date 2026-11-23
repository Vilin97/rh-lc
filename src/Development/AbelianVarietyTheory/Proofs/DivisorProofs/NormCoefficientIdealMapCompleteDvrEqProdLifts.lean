module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAlgebraSplittingNormFormStatement
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFinite

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem exists_lift_to_complete_dvr_of_finite : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  intro A R _ _ _ hinj hfin V _ _ _ _ hC h
  classical
  let p : Ideal A := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R) (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  let K := FractionRing V
  let Ω := AlgebraicClosure K
  letI : Algebra (A ⧸ p) (R ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hQp.symm)
  have hcomp : (algebraMap (A ⧸ p) (R ⧸ Q)).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk Q).comp (algebraMap A R) := rfl
  haveI : Algebra.IsIntegral (A ⧸ p) (R ⧸ Q) := by
    constructor
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact IsIntegral.map_of_comp_eq (Ideal.Quotient.mk p) (Ideal.Quotient.mk Q) hcomp
      (Algebra.IsIntegral.isIntegral r)
  have hinj0 : Function.Injective (algebraMap (A ⧸ p) (R ⧸ Q)) :=
    Ideal.quotientMap_injective' (le_of_eq hQp)
  let g0 : (A ⧸ p) →+* Ω := (algebraMap K Ω).comp ((algebraMap V K).comp (RingHom.kerLift h))
  have hg0 : Function.Injective g0 :=
    (algebraMap K Ω).injective.comp ((IsFractionRing.injective V K).comp (RingHom.kerLift_injective h))
  letI : Algebra (A ⧸ p) Ω := g0.toAlgebra
  haveI : Module.IsTorsionFree (A ⧸ p) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj0
  haveI : Module.IsTorsionFree (A ⧸ p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hg0
  haveI : Algebra.IsAlgebraic (A ⧸ p) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (R ⧸ Q) →ₐ[A ⧸ p] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ρ1 : R →+* Ω := σ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hρ1 : ∀ a : A, ρ1 (algebraMap A R a) = algebraMap K Ω (algebraMap V K (h a)) := by
    intro a
    show σ (Ideal.Quotient.mk Q (algebraMap A R a)) = _
    rw [← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, σ.commutes]
    rfl
  obtain ⟨s, hs⟩ := hfin.fg_top
  let M : IntermediateField K Ω := IntermediateField.adjoin K (ρ1 '' (s : Set R))
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ r : R, ρ1 r ∈ M := by
    intro r
    have hr : r ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def, map_mul, hρ1]; exact M.mul_mem (M.algebraMap_mem _) hx
  let ψ : R →+* M := ρ1.codRestrict M hmem
  have hψ : (algebraMap V M).comp h = ψ.comp (algebraMap A R) := by
    ext a
    simp only [RingHom.comp_apply]
    show (algebraMap V M (h a) : Ω) = ρ1 (algebraMap A R a)
    rw [hρ1]
    rfl
  have hint : ∀ r : R, ψ r ∈ integralClosure V M := fun r =>
    IsIntegral.map_of_comp_eq h ψ hψ (Algebra.IsIntegral.isIntegral r)
  let ρ : R →+* integralClosure V M := ψ.codRestrict (integralClosure V M) hint
  haveI hdvr := Formalism.L2.G.IntCl.isDVR V K M hC
  have hfinj := Formalism.L2.G.IntCl.alg_injective V K M
  haveI : FaithfulSMul V (integralClosure V M) := (faithfulSMul_iff_algebraMap_injective _ _).2 hfinj
  refine ⟨integralClosure V M, inferInstance, inferInstance, hdvr,
    (RingHom.charZero_iff hfinj).1 inferInstance, algebraMap V (integralClosure V M), ρ,
    Formalism.L2.G.IntCl.complete V K M hC, hfinj, Algebra.IsIntegral.isLocalHom _ _, ?_⟩
  ext a
  show ρ1 (algebraMap A R a) = (algebraMap V M (h a) : Ω)
  rw [hρ1]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFiniteStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinear

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory
namespace GaussContentLinearForms

variable {V : Type} [CommRing V] {σ : Type}

theorem span_coeff_C_mul (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext x
  simp only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

theorem span_coeff_eq_top_iff [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by
  have h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔
      Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V := by
    rw [Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]
    refine forall_congr' fun s => ?_
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      IsLocalRing.residue_eq_zero_iff]
    rfl
  rw [ne_eq, h1]
  constructor
  · intro h h'
    rw [h, top_le_iff] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top h'
  · intro h
    by_contra h'
    exact h (IsLocalRing.le_maximalIdeal h')

theorem span_coeff_one :
    Ideal.span (Set.range fun s => (1 : MvPolynomial σ V).coeff s) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩

theorem exists_primitive_part [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span (Set.range fun s => f.coeff s))).principal
  have ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a} := ha
  have hd : C a ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro s
    rw [← Ideal.mem_span_singleton, ← ha']
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨g, rfl⟩ := hd
  by_cases h0 : a = 0
  · exact ⟨0, 1, by simp [h0], span_coeff_one⟩
  · refine ⟨a, g, rfl, ?_⟩
    rw [span_coeff_C_mul] at ha'
    have hne : Ideal.span {a} ≠ (0 : Ideal V) := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact h0
    apply mul_left_cancel₀ hne
    rw [ha', Ideal.mul_top]

theorem span_coeff_mul [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by
  obtain ⟨a, f', rfl, hf⟩ := exists_primitive_part f
  obtain ⟨b, g', rfl, hg⟩ := exists_primitive_part g
  have hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤ := by
    rw [span_coeff_eq_top_iff] at hf hg ⊢
    rw [map_mul]
    exact mul_ne_zero hf hg
  have e : C a * f' * (C b * g') = C (a * b) * (f' * g') := by
    rw [map_mul]; ring
  rw [e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top,
    Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]

theorem span_coeff_prod [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]

theorem span_coeff_linear {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro s
    simp only [coeff_sum, coeff_C_mul, SetLike.mem_coe]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Finsupp.single i 1, ?_⟩
    simp only [coeff_sum, coeff_C_mul, coeff_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right, mul_zero]
      intro h
      exact hj (Finsupp.single_left_injective one_ne_zero h)
    · simp

theorem span_coeff_prod_linear (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  rw [span_coeff_prod]
  exact Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)

end GaussContentLinearForms
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinearStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.span_coeff_prod_linear_eq_prod_span : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (d m : ℕ)
    (c : Fin d → Fin m → V),
    Ideal.span (Set.range fun s => (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  first | exact @GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | exact GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear | (intros; apply GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLifts

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM


open MvPolynomial in
theorem GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp J V _ _ _ _ hV h
  obtain ⟨R, _, _, hinj, hfin, σ, hσ, hP⟩ := GlobalTheory.T.exists_finite_algebra_splitting_normForm A B K L φ hφ hcomp
  obtain ⟨V', _, _, _, _, f, ρ, hV', hf, hloc, hρ⟩ := GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' A R hinj hfin V hV h
  let ψ : Fin (Module.finrank K L) → (B →+* V') := fun j => ρ.comp (σ j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hloc, ?_, ?_⟩
  · intro j
    show (ρ.comp (σ j)).comp φ = f.comp h
    rw [RingHom.comp_assoc, hσ j, hρ]
  have key : ∀ (m : ℕ) (g : Fin m → B) (P : MvPolynomial (Fin m) A),
      P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i →
      Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) =
        ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by
    intro m g P hPR
    rw [← GlobalTheory.T.span_coeff_prod_linear_eq_prod_span V' _ m (fun j i => ψ j (g i))]
    have hE : (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V') = (P.map (algebraMap A R)).map ρ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPR]; simp [map_prod, map_sum, ψ]
    have hfun : (fun s => (f.comp h) (P.coeff s)) =
        fun s => (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V').coeff s := by
      funext s
      rw [hE, MvPolynomial.map_map, MvPolynomial.coeff_map, hρ]
    rw [hfun]
  unfold GlobalTheory.NormSheaf.normIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨m, g, hgJ, s, hs⟩, rfl⟩
    obtain ⟨P, hPK, hPR⟩ := hP m g
    have ha : a = P.coeff s := IsFractionRing.injective A K (by rw [hs, ← hPK, MvPolynomial.coeff_map])
    have hmem : (f.comp h) a ∈ Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) :=
      Ideal.subset_span ⟨s, by rw [ha]⟩
    rw [key m g P hPR] at hmem
    have hle : ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) ≤ ∏ j, J.map (ψ j) :=
      Finset.prod_le_prod' (fun j _ => Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)))
    exact hle hmem
  · have hfg : ∀ j, ∃ t : Finset V', (↑t : Set V') ⊆ ψ j '' (J : Set B) ∧ J.map (ψ j) = Ideal.span (↑t : Set V') := by
      intro j
      have h1 : (J.map (ψ j)).FG := IsNoetherian.noetherian _
      rw [Ideal.map] at h1 ⊢
      exact (Submodule.fg_span_iff_fg_span_finset_subset _).1 h1
    choose t ht hspan using hfg
    have hpre : ∀ (x : Σ j, (t j : Set V')), ∃ b ∈ J, ψ x.1 b = x.2 := by
      rintro ⟨j, x, hx⟩
      obtain ⟨b, hb, e⟩ := ht j hx
      exact ⟨b, hb, e⟩
    choose pre hpreJ hpreψ using hpre
    let e := Fintype.equivFin (Σ j, (t j : Set V'))
    let g : Fin (Fintype.card (Σ j, (t j : Set V'))) → B := fun i => pre (e.symm i)
    have hgJ : ∀ i, g i ∈ J := fun i => hpreJ _
    obtain ⟨P, hPK, hPR⟩ := hP _ g
    have hj : ∀ j, Ideal.span (Set.range fun i => ψ j (g i)) = J.map (ψ j) := by
      intro j
      apply le_antisymm
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)
      · rw [hspan j, Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        refine ⟨e ⟨j, x, hx⟩, ?_⟩
        simp only [g, Equiv.symm_apply_apply]
        exact hpreψ ⟨j, x, hx⟩
    calc ∏ j, J.map (ψ j) = ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by simp_rw [hj]
      _ = Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) := (key _ g P hPR).symm
      _ ≤ _ := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        apply Ideal.subset_span
        exact ⟨P.coeff s, ⟨_, g, hgJ, s, by rw [← hPK, MvPolynomial.coeff_map]⟩, rfl⟩
end
end
