module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsRealIndependent
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Data.Pi.Interval
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionFubiniStudyPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootFlatPushforwardGeoFun
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroup

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem finite_of_bounded_image_closure_finset :
    ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (Φ : V →+ E),
      (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) →
      ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) →
        ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  intro V E _ _ _ _ _ Φ hΦ S Y hY R hR
  set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef
  have hMY : Y ⊆ (M : Set V) := by
    intro y hy
    have := hY hy
    rw [← Submodule.span_int_eq_addSubgroupClosure] at this
    exact this
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ M
  set n := Module.finrank ℤ M
  let e : Fin n → V := fun j => (b j : V)
  have heZ : LinearIndependent ℤ e := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ
  have heR := hΦ n e heQ
  let T : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (fun j => Φ (e j))
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT

  let f : V → (Fin n → ℤ) := fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0
  have hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j := fun y h => by simp [f, h]
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hyz
    have h1 := hMY hy
    have h2 := hMY hz
    rw [hfy y h1, hfy z h2] at hyz
    have : b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩ := by
      ext j; exact congrFun hyz j
    have := b.repr.injective this
    simpa using congrArg Subtype.val this
  have hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)) := by
    intro y h
    have hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j := by
      have := congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [hs']

    simp [T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  set N : ℤ := ⌈(K : ℝ) * R⌉
  have hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hMY hy
    rw [hfy y h]
    set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)
    have hc : ‖c‖ ≤ (K : ℝ) * R := by
      have h1 := ZeroHomClass.bound_of_antilipschitz T hK c
      rw [← hΦy y h] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)
    have hcj : ∀ j, |c j| ≤ (K : ℝ) * R := fun j => by
      have h0 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
      rw [Real.norm_eq_abs] at h0
      exact h0.trans hc
    constructor <;> intro j
    · have h3 : -((K : ℝ) * R) ≤ c j := (abs_le.1 (hcj j)).1
      have h4 : (-(N : ℝ)) ≤ c j := le_trans (neg_le_neg (Int.le_ceil _)) h3
      have h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ) := by push_cast; exact h4
      exact Int.cast_le.1 h5
    · have h4 : c j ≤ (N : ℝ) := ((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)
      exact Int.cast_le.1 h4
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroupStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup : ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Φ : V →+ E), (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) → ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) → ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  first | (exact @GlobalTheory.finite_of_bounded_image_closure_finset) | (exact GlobalTheory.finite_of_bounded_image_closure_finset) | (intros; apply GlobalTheory.finite_of_bounded_image_closure_finset  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorSquaredBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fixed_vector_squared_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKCx.entries_sq_le_of_fixL) | (exact GlobalTheory.LKCx.entries_sq_le_of_fixL) | (intros; apply GlobalTheory.LKCx.entries_sq_le_of_fixL  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominatorsStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.formGroup_testFunction_support_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  first | (exact @GlobalTheory.LKCx.BoundedDen.main) | (exact GlobalTheory.LKCx.BoundedDen.main) | (intros; apply GlobalTheory.LKCx.BoundedDen.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicDenominatorBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.p_adic_denominator_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  first | (exact @GlobalTheory.AtP.main) | (exact GlobalTheory.AtP.main) | (intros; apply GlobalTheory.AtP.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe

section

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

variable {p : ℕ} [Fact p.Prime]

theorem exists_int_of_den_le (D k : ℕ) (hD : 0 < D) (q : ℚ)
    (h1 : ∀ ℓ : ℕ, ℓ ≠ p → q.den.factorization ℓ ≤ D.factorization ℓ) (h2 : q.den.factorization p ≤ k) :
    ∃ m : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = m := by
  have hp : p.Prime := Fact.out
  have hN : 0 < D * p ^ k := Nat.mul_pos hD (pow_pos hp.pos k)
  have hdvd : q.den ∣ D * p ^ k := by
    rw [← Nat.factorization_le_iff_dvd q.den_nz hN.ne']
    intro ℓ
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow, hp.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : ℓ = p
    · subst hl; simp only [Finsupp.single_eq_same, mul_one]; have := h2; omega
    · have := h1 ℓ hl; omega
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c * q.num, ?_⟩
  rw [hc]
  calc ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * q.den) := by push_cast; ring
    _ = _ := by rw [Rat.mul_den_eq_num]; push_cast; ring

theorem grp_val_injective (G : HTGroup p) (β : G.Cˣ) :
    Function.Injective (fun y : grp G β => (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
  intro y y' hyy
  have hu : (y : G.Cˣ × ℚˣ).1 = (y' : G.Cˣ × ℚˣ).1 := Units.ext hyy
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  have h2 : (((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y'.2.1
  rw [hu] at h1
  have h3 : algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
    have := h1.symm.trans h2
    simpa using congrArg (· * ((β⁻¹ : G.Cˣ) : G.C)) this
  have h4 : (y : G.Cˣ × ℚˣ).2 = (y' : G.Cˣ × ℚˣ).2 := Units.ext ((algebraMap ℚ G.C).injective h3)
  exact Subtype.ext (Prod.ext hu h4)

theorem finite_fix_core (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f')
    (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (hsym : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) :
    Set.Finite {y : grp G β | FixL G v β y z ∧
      f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0} := by
  obtain ⟨D, hD, hAf⟩ := GlobalTheory.T.formGroup_testFunction_support_bounded_denominators p G β x t hx L f hf h.1
  obtain ⟨k, hP⟩ := GlobalTheory.T.p_adic_denominator_bound p G β K' f' hf' h.2
  obtain ⟨K, hK⟩ := GlobalTheory.T.fixed_vector_squared_bound p G hG v hv β hsym hR z hz
  set N : ℕ := D * p ^ k with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)
  set b := Module.finBasis ℚ G.C with hb
  set S : Finset G.C := Finset.univ.image (fun i => ((N : ℚ)⁻¹) • b i) with hS
  let Φ : G.C →+ (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    AddMonoidHom.mk' (fun c w i l => G.psi w c i l) (by intro a c; funext w i l; simp [map_add (f := _)])
  refine Set.Finite.of_finite_image ?_ ((grp_val_injective G β).injOn)
  refine GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup Φ (fun k e he => GlobalTheory.T.embeddings_real_independent p G k e he) S _ ?_ (Real.sqrt (max K 0 * N)) ?_
  · rintro _ ⟨y, ⟨-, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    show (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ AddSubgroup.closure (S : Set G.C)
    rw [← b.sum_repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; exact_mod_cast (Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)).ne'
    have e : b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i • b i = m • ((N : ℚ)⁻¹ • b i) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hm, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by
      simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨i, rfl⟩)) m
  · rintro _ ⟨y, ⟨hfix, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hNpos) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
        calc (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = 1 * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := (one_mul _).symm
          _ ≤ ((N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹) * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
            mul_le_mul_of_nonneg_right h2 hs.le
          _ = N := by field_simp
      exact_mod_cast this
    have hsR : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast hs
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    have h1 := hK y hfix w i j
    have h2 : ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ max K 0 * N :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) hsR.le).trans
        (mul_le_mul_of_nonneg_left hsN (le_max_right K 0)))
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3

end GlobalTheory.FinFix
end
end
end
