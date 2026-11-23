module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZeroStatement
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpanStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmoduleStatement

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule : ∀ (A₀ R K₀ L : Type) [CommRing A₀] [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
  [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R] [Algebra K₀ L] [Algebra A₀ L]
  [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L] [FiniteDimensional K₀ L] [IsGalois K₀ L]
  (N : ℕ), 0 < N →
  (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → ¬ Ideal.map (algebraMap A₀ R) (Q.comap (algebraMap A₀ R)) ≤ Q ^ 2) →
  (∀ c : ClassGroup A₀, ∃ d, c = d ^ N) →
  ∀ w : L, w ≠ 0 → (∀ σ : L ≃ₐ[K₀] L, ∃ u : L, u ≠ 0 ∧ σ w = w * u ^ N) →
  ∃ (f : K₀) (J : Submodule R L), f ≠ 0 ∧ J ^ N = Submodule.span R {w / algebraMap K₀ L f} := by
  first | exact @GlobalTheory.DivisorDescent.descent_submodule | exact GlobalTheory.DivisorDescent.descent_submodule | (intros; apply GlobalTheory.DivisorDescent.descent_submodule <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kummer_aeval_mem_integralClosure {A₀ F E : Type} [CommRing A₀] [Field F] [Field E] [Algebra A₀ F]
    [Algebra F E] [Algebra A₀ E] [IsScalarTower A₀ F E] {x : E} (hx : IsIntegral A₀ x)
    (p : (integralClosure A₀ F)[X]) : IsIntegral A₀ (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial]
    refine IsIntegral.mul ?_ (hx.pow n)
    have : algebraMap (integralClosure A₀ F) E c = algebraMap F E (c : F) := rfl
    rw [this]
    exact c.2.map (IsScalarTower.toAlgHom A₀ F E)

theorem kummer_dual_step (A₀ K₀ F E : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [Field F] [Field E] [Algebra K₀ F] [Algebra F E] [Algebra K₀ E]
    [IsScalarTower K₀ F E] [Algebra A₀ F] [Algebra A₀ E] [IsScalarTower A₀ K₀ F] [IsScalarTower A₀ K₀ E]
    [IsScalarTower A₀ F E] [FiniteDimensional K₀ F] [FiniteDimensional F E] [CharZero K₀]
    (N : ℕ) (hN : IsUnit (N : A₀)) (x : E) (u : A₀ˣ) (hx : x ^ N = algebraMap A₀ E u)
    (hgen : Algebra.adjoin F {x} = ⊤)
    (hF : ∀ y : F, (∀ z : F, IsIntegral A₀ z → Algebra.trace K₀ F (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y) :
    ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y := by
  intro y hy
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K₀ F).injective
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : Algebra.IsSeparable F E := inferInstance
  let C := integralClosure A₀ F
  haveI : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ F C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hxA : IsIntegral A₀ x := by
    refine ⟨X ^ N - Polynomial.C (u : A₀), monic_X_pow_sub_C _ hN0, ?_⟩
    simp [eval₂_sub, hx]
  have hxC : IsIntegral C x := hxA.tower_top
  have key := traceForm_dualSubmodule_adjoin C F hgen hxC

  have hymem : y ∈ (Algebra.traceForm F E).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin C {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    have hzA : IsIntegral A₀ (aeval x p) := kummer_aeval_mem_integralClosure hxA p
    rw [Algebra.traceForm_apply]
    have hw : IsIntegral A₀ (Algebra.trace F E (y * aeval x p)) := by
      apply hF
      intro c hc
      have : Algebra.trace F E (y * aeval x p) * c =
          Algebra.trace F E (y * (aeval x p * algebraMap F E c)) := by
        rw [mul_comm _ c, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
        ring_nf
      rw [this, Algebra.trace_trace]
      exact hy _ (hzA.mul (hc.map (IsScalarTower.toAlgHom A₀ F E)))
    exact Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩
  rw [key, Submodule.mem_smul_pointwise_iff_exists] at hymem
  obtain ⟨z, hz, rfl⟩ := hymem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨q, rfl⟩ := hz
  have hmin : minpoly F x = map (algebraMap C F) (minpoly C x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' F hxC
  have hdvd : minpoly C x ∣ X ^ N - Polynomial.C (algebraMap A₀ C u) := by
    apply minpoly.isIntegrallyClosed_dvd hxC
    simp [hx, ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := hdvd
  have hder := congrArg (fun p => aeval x (derivative p)) hg
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul, map_add (f := _), map_mul,
    minpoly.aeval, zero_mul, add_zero] at hder
  set d := aeval x (derivative (minpoly C x))
  let v : A₀ˣ := hN.unit * u
  have hinv : (aeval x (derivative (minpoly F x)))⁻¹ = aeval x g * x * algebraMap A₀ E (↑v⁻¹ : A₀) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
    apply inv_eq_of_mul_eq_one_right
    change d * _ = 1
    have h1 : d * aeval x g = (N : E) * x ^ (N - 1) := by rw [← hder]; simp
    have hv : ((v : A₀)) = (N : A₀) * u := by simp [v]
    calc d * (aeval x g * x * algebraMap A₀ E ↑v⁻¹)
        = (N : E) * (x ^ (N - 1) * x) * algebraMap A₀ E ↑v⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, h1]; ring
      _ = algebraMap A₀ E ((v : A₀) * ↑v⁻¹) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0), hx, map_mul, hv, map_mul,
          map_natCast]
      _ = 1 := by simp
  rw [smul_eq_mul, hinv]
  refine IsIntegral.mul (IsIntegral.mul (kummer_aeval_mem_integralClosure hxA g) hxA) isIntegral_algebraMap
    |>.mul (kummer_aeval_mem_integralClosure hxA q)

end GlobalTheory

namespace GlobalTheory

theorem kummer_dual_induction (A₀ K₀ : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [CharZero K₀] (N : ℕ) (hN : IsUnit (N : A₀)) :
    ∀ (n : ℕ) (E : Type) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (s : Finset E), s.card = n → IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
        IsIntegral A₀ y := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ s hs hadj _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    rw [Finset.coe_empty, IntermediateField.adjoin_empty] at hadj
    have hr : Module.finrank K₀ E = 1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hadj
    have hyb : y ∈ (⊥ : IntermediateField K₀ E) := hadj ▸ IntermediateField.mem_top
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.mp hyb
    obtain ⟨a, ha⟩ := hy 1 isIntegral_one
    rw [mul_one, Algebra.trace_algebraMap, hr, one_smul] at ha
    rw [← ha, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  | succ n ih =>
    intro E _ _ _ _ _ s hs hadj hu y hy
    classical
    obtain ⟨x, hxs⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    let t := s.erase x
    let F := IntermediateField.adjoin K₀ (t : Set E)
    let s' : Finset F := t.subtype (· ∈ F)
    have hs' : s'.card = n := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem (s := t) (p := (· ∈ F))
        (fun y hy => IntermediateField.subset_adjoin K₀ (t : Set E) hy),
        Finset.card_erase_of_mem hxs, hs]
      rfl
    have hadj' : IntermediateField.adjoin K₀ (s' : Set F) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
      change _ = IntermediateField.adjoin K₀ (t : Set E)
      congr 1
      ext w
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Finset.mem_subtype.mp hw
      · intro hw
        exact ⟨⟨w, IntermediateField.subset_adjoin K₀ _ hw⟩, Finset.mem_subtype.mpr hw, rfl⟩
    have hu' : ∀ y ∈ s', ∃ u : A₀ˣ, y ^ N = algebraMap A₀ F u := by
      intro y hy
      obtain ⟨u, hu⟩ := hu y (Finset.mem_of_mem_erase (Finset.mem_subtype.mp hy))
      exact ⟨u, Subtype.ext hu⟩
    have hF := ih F s' hs' hadj' hu'
    obtain ⟨u, hux⟩ := hu x hxs
    have hgen : Algebra.adjoin F {x} = ⊤ := by
      have h1 : IntermediateField.adjoin F ({x} : Set E) = ⊤ := by
        apply IntermediateField.restrictScalars_injective K₀
        rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← hadj]
        congr 1
        rw [Set.union_singleton, ← Finset.coe_insert, Finset.insert_erase hxs]
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun z _ => Algebra.IsAlgebraic.isAlgebraic z), h1]
      rfl
    haveI : IsScalarTower A₀ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact kummer_dual_step A₀ K₀ F E N hN x u hux hgen hF y hy

end GlobalTheory

namespace GlobalTheory

theorem kummer_not_map_comap_le_sq :
    ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀]
      [IsFractionRing A₀ K₀] [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
      ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
        ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E))
          (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  intro A₀ K₀ E _ _ _ _ _ _ _ _ _ _ _ N hN s hadj hu P hP hP0 hle
  have hdual := kummer_dual_induction A₀ K₀ N hN _ E s rfl hadj hu
  haveI : IsFractionRing (integralClosure A₀ E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ E _
  haveI : IsDedekindDomain (integralClosure A₀ E) := integralClosure.isDedekindDomain A₀ K₀ E
  haveI : Module.Finite A₀ (integralClosure A₀ E) := IsIntegralClosure.finite A₀ K₀ E _
  have hinj : Function.Injective (algebraMap A₀ E) := by
    rw [IsScalarTower.algebraMap_eq A₀ K₀ E]
    exact (algebraMap K₀ E).injective.comp (IsFractionRing.injective A₀ K₀)
  haveI : FaithfulSMul A₀ (integralClosure A₀ E) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree A₀ (integralClosure A₀ E) := inferInstance
  have hone : Submodule.traceDual A₀ K₀ (1 : Submodule (integralClosure A₀ E) E) = 1 := by
    refine le_antisymm ?_ Submodule.one_le_traceDual_one
    intro y hy
    rw [Submodule.mem_traceDual] at hy
    refine Submodule.mem_one.mpr ⟨⟨y, hdual y fun z hz => ?_⟩, rfl⟩
    exact hy z (Submodule.mem_one.mpr ⟨⟨z, hz⟩, rfl⟩)
  have hdiff : differentIdeal A₀ (integralClosure A₀ E) = 1 := by
    rw [← FractionalIdeal.coeIdeal_eq_one (K := E), coeIdeal_differentIdeal A₀ K₀ E]
    have : FractionalIdeal.dual A₀ K₀
        (1 : FractionalIdeal (nonZeroDivisors (integralClosure A₀ E)) E) = 1 := by
      apply FractionalIdeal.coeToSubmodule_injective
      simp only [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one, hone]
    rw [this, inv_one]
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hp0 : P.comap (algebraMap A₀ (integralClosure A₀ E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hb0 hbP (Algebra.IsIntegral.isIntegral b)
  haveI : (P.comap (algebraMap A₀ (integralClosure A₀ E))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  have h := pow_sub_one_dvd_differentIdeal_aux A₀ K₀ E
    (p := P.comap (algebraMap A₀ (integralClosure A₀ E))) P (e := 2) hp0
    (Ideal.dvd_iff_le.mpr hle)
  rw [hdiff, Ideal.dvd_iff_le] at h
  apply hP.ne_top
  simpa using h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSqStatement

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq : ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
  [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E] [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
  ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ → (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
  ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
    ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E)) (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  first | exact @GlobalTheory.kummer_not_map_comap_le_sq | exact GlobalTheory.kummer_not_map_comap_le_sq | (intros; apply GlobalTheory.kummer_not_map_comap_le_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionField

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem descent_abstract (A K E Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K]
    [IsFractionRing A K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [Field Ω] [Algebra E Ω] (N : ℕ) (hN : 0 < N) (hNu : IsUnit (N : A))
    (s : Finset E) (hs : IntermediateField.adjoin K (s : Set E) = ⊤)
    (hsu : ∀ x ∈ s, ∃ u : Aˣ, x ^ N = algebraMap A E u)
    (hcl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (w : E) (hw : w ≠ 0)
    (hσ : ∀ σ : E ≃ₐ[K] E, ∃ u : E, u ≠ 0 ∧ σ w = w * u ^ N) :
    ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, (∀ x : A, algebraMap E Ω (algebraMap A E x) ∈ B) →
      ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / algebraMap K E f / c ^ N)) = 1 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, J, hf, hJ⟩ := GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule A (integralClosure A E) K E N hN
    (GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ
  refine ⟨f, hf, fun B hB => ?_⟩
  refine GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ
  · intro x
    show algebraMap E Ω (x : E) ∈ B
    obtain ⟨p, hp, hpx⟩ : IsIntegral A (x : E) := x.2
    let φ : A →+* B := ((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB
    have hint : IsIntegral B (algebraMap E Ω x) := by
      refine ⟨p.map φ, hp.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg (algebraMap E Ω) hpx
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  · exact div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)

theorem isGalois_adjoin_pair (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hζK : ζ ∈ Set.range (algebraMap K Ω))
    (a b : K) (α β : Ω) (ha : a ≠ 0) (hb : b ≠ 0) (hα : α ^ N = algebraMap K Ω a) (hβ : β ^ N = algebraMap K Ω b) :
    IsGalois K (IntermediateField.adjoin K {α, β}) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} →
      x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β} := by
    intro c γ x hc hγ hm hx
    have hc' : algebraMap K Ω c ≠ 0 := (_root_.map_ne_zero _).mpr hc
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hγ
      exact hc' hγ.symm
    have h1 : (x / γ) ^ N = 1 := by rw [div_pow, hx, hγ, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    obtain ⟨z, rfl⟩ := hζK
    have : x = algebraMap K Ω z ^ i * γ := by rw [hi, div_mul_cancel₀ _ hγ0]
    rw [this]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm
  let p : K[X] := (X ^ N - C a) * (X ^ N - C b)
  have hp0 : p ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)
  have hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b := by
    intro x
    rw [mem_rootSet_of_ne hp0]
    simp [p, sub_eq_zero]
  have heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω) := by
    apply le_antisymm
    · apply IntermediateField.adjoin.mono
      rintro x (rfl | rfl)
      · exact (hroot _).mpr (Or.inl hα)
      · exact (hroot _).mpr (Or.inr hβ)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases (hroot x).mp hx with h | h
      · exact key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h
      · exact key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h
  rw [heq]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)
  haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p
  exact ⟨⟩

theorem adjoin_pair_eq_top (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (α β : Ω)
    (α' β' : IntermediateField.adjoin K {α, β}) (hα : (α' : Ω) = α) (hβ : (β' : Ω) = β) :
    IntermediateField.adjoin K ({α', β'} : Set (IntermediateField.adjoin K {α, β})) = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    Set.image_pair]
  simp [hα, hβ]

theorem divisor_descends : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hNu : IsUnit (N : FunctionField.ringOfIntegers k K) := by
    have h1 : IsUnit (N : k) := (Nat.cast_ne_zero.mpr hN.ne').isUnit
    have h2 := h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)
    rwa [map_natCast] at h2
  let α' : IntermediateField.adjoin K {α, β} := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : IntermediateField.adjoin K {α, β} := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  obtain ⟨f, hf, hB⟩ := descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω
    N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
          Subtype.ext hα⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩,
          Subtype.ext hβ⟩)
    (GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))
    (by
      intro σ
      obtain ⟨u, hu, hu0, h⟩ := hs (σ.liftNormal Ω)
      refine ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      exact (σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)
  refine ⟨f, hf, fun B hO => ?_⟩
  obtain ⟨c, hc, hv⟩ := hB B fun x => hO x.1 x.2
  refine ⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩
  rw [div_div, map_div₀, map_mul, map_pow] at hv
  exact hv

end GlobalTheory.KummerCob
end
end
