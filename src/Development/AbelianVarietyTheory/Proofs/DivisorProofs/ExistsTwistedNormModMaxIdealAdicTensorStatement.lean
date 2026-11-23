module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import GroundTheory.GlobalFields.LocalAtPlace
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingNormFormSurjective

section

@[expose] public section

open IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.FinRingNorm

theorem field_case (F : Type) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (d s : F) (hd : d ≠ 0) :
    ∃ a b : F, a ^ 2 - d * b ^ 2 = s := by
  classical
  cases nonempty_fintype F
  have hc : ringChar F ≠ 2 := by
    intro h; apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this; exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F) (f := X ^ 2)
    (g := -(C d * X ^ 2) - C s) (by simp) (by compute_degree!) (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_neg, eval_mul, eval_C] at hab
  linear_combination hab

theorem reduced_case (S : Type) [CommRing S] [Finite S] [IsReduced S] (h2 : IsUnit (2 : S))
    (d s : S) (hd : IsUnit d) : ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  classical
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 - (Ideal.Quotient.mk I.asIdeal d) * b ^ 2 = Ideal.Quotient.mk I.asIdeal s := by
    intro I
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    have h2' : (2 : S ⧸ I.asIdeal) ≠ 0 := by
      have := (h2.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
      rwa [map_ofNat] at this
    exact field_case _ h2' _ _ (hd.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
  choose A B hAB using key
  refine ⟨(IsArtinianRing.equivPi S).symm A, (IsArtinianRing.equivPi S).symm B, ?_⟩
  apply (IsArtinianRing.equivPi S).injective
  funext I
  simp only [map_sub, map_mul, map_pow, AlgEquiv.apply_symm_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply]
  exact hAB I

theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (S : Type) [CommRing S] [Finite S], Nat.card S = n → IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn h2 d s hd hs
  by_cases hred : IsReduced S
  · exact reduced_case S h2 d s hd

  obtain ⟨x, hx0, hx2⟩ : ∃ x : S, x ≠ 0 ∧ x ^ 2 = 0 := by
    rw [isReduced_iff] at hred
    push_neg at hred
    obtain ⟨y, ⟨k, hk⟩, hy⟩ := hred
    classical
    have hex : ∃ m, y ^ m = 0 := ⟨k, hk⟩
    let m := Nat.find hex
    have hm : y ^ m = 0 := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h
      have : y ^ m = 1 := by rw [h, pow_zero]
      apply hy
      rw [← mul_one y, ← this, hm, mul_zero]
    have hm1 : m ≠ 1 := by
      intro h; apply hy; rw [← pow_one y, ← h, hm]
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨y ^ j, ?_, ?_⟩
    · exact Nat.find_min hex (by omega)
    · rw [← pow_mul]
      obtain ⟨t, ht⟩ : ∃ t, j * 2 = m + t := ⟨j * 2 - m, by omega⟩
      rw [ht, pow_add, hm, zero_mul]
  set I : Ideal S := Ideal.span {x} with hI
  have hlt : Nat.card (S ⧸ I) < n := by
    rw [← hn]
    classical
    cases nonempty_fintype S
    haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    cases nonempty_fintype (S ⧸ I)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_surjective_not_injective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    intro hinj
    apply hx0
    apply hinj
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a', b', hab'⟩ := ih _ hlt (S ⧸ I) rfl (h2.map (Ideal.Quotient.mk I)) _ _
    (hd.map (Ideal.Quotient.mk I)) (hs.map (Ideal.Quotient.mk I))
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have hmem : a0 ^ 2 - d * b0 ^ 2 - s ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    rw [hab', sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  set iv := t - t ^ 2 * r * x with hiv
  have hv : (s + r * x) * iv - 1 = 0 := by
    rw [hiv]; linear_combination (1 - t * r * x) * ht - t ^ 2 * r ^ 2 * hx2
  refine ⟨a0 - r * a0 * iv * u * x, b0 - r * b0 * iv * u * x, ?_⟩
  linear_combination (1 - r * x * 2 * u * iv) * hr.symm - r * x * 2 * u * hv - r * x * hu + (r * iv * u) ^ 2 * (a0 ^ 2 - d * b0 ^ 2) * hx2

theorem exists_sq_sub_mul_sq_eq : ∀ (S : Type) [CommRing S] [Finite S], IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s :=
  fun S _ _ h2 d s hd hs => finiteRing_sq_sub_mul_sq_eq_of_card _ S rfl h2 d s hd hs

end GlobalTheory.FinRingNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensor

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ResidueNorm

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
  (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isSmallB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsSmallB v b x) (hy : IsSmallB v b y) :
    IsSmallB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact Valuation.map_add_lt _ (hx i) (hy i)

theorem isSmallB_zero : IsSmallB v b (0 : v.adicCompletion ℚ ⊗[ℚ] M) := fun i => by simp

theorem isSmallB_sub_of_residue_eq {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y)
    (h : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hx i⟩ =
      IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hy i⟩) : IsSmallB v b (x - y) := fun i => by
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers ℚ) (⟨_, hx i⟩ - ⟨_, hy i⟩) = 0 := by
    rw [map_sub, h i, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h0
  rw [map_sub, Finsupp.sub_apply]
  exact h1

theorem eq_neg_inv_of_mul_neg {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * -↑u = 1) : x = -↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(↑u⁻¹ : R)) * h + (-x) * k2

theorem eq_inv_of_mul {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * ↑u = 1) : x = ↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (↑u⁻¹ : R) * h - x * k2

theorem sq_mul_inv_sq {R : Type*} [CommRing R] (u : Rˣ) : (↑u * ↑u : R) * (↑u⁻¹ * ↑u⁻¹) = 1 := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem norm_expand {R : Type*} [CommRing R] (a b t e : R) :
    (a + b * t) * (a - b * t) - e = a ^ 2 - t * t * b ^ 2 - e := by ring

end GlobalTheory.ResidueNorm


open GlobalTheory.ResidueNorm in
theorem GlobalTheory.ResidueNorm.exists_norm_mod_small : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  intro v L _ _ c _ κ bL h2 h1 hmul hsm _ θ hθ hθi hσθ e hσe he hei
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef

  obtain ⟨P, hP⟩ : ∃ P : Subring (v.adicCompletion ℚ ⊗[ℚ] L), ∀ x, x ∈ P ↔ IsIntB v bL x ∧ σ x = x := ⟨
    { carrier := {x | IsIntB v bL x ∧ σ x = x}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨h1, map_one σ⟩
      add_mem' := fun {a b} ha hb => ⟨isIntB_add v bL ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2]⟩
      zero_mem' := ⟨isIntB_zero v bL, map_zero σ⟩
      neg_mem' := fun {a} ha => ⟨isIntB_neg v bL ha.1, by rw [map_neg, ha.2]⟩ }, fun x => Iff.rfl⟩
  have hPi : ∀ x : P, IsIntB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := fun x => ((hP _).1 x.2).1
  have hPs : ∀ x : P, σ (x : v.adicCompletion ℚ ⊗[ℚ] L) = x := fun x => ((hP _).1 x.2).2
  obtain ⟨I, hmemI⟩ : ∃ I : Ideal P, ∀ x : P, x ∈ I ↔ IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := ⟨
    { carrier := {x | IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L)}
      add_mem' := fun {a b} ha hb => isSmallB_add v bL ha hb
      zero_mem' := isSmallB_zero v bL
      smul_mem' := fun a b hb => hsm _ _ (hPi a) hb }, fun x => Iff.rfl⟩

  haveI : Finite κ := Module.Finite.finite_basis bL
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  let φ : P → κ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) := fun x i =>
    IsLocalRing.residue _ ⟨_, hPi x i⟩
  let out := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  haveI : Finite (P ⧸ I) := by
    refine Finite.of_injective (fun q => φ (out q)) fun q1 q2 h => ?_
    rw [← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q1,
      ← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q2, Ideal.Quotient.eq, hmemI]
    exact isSmallB_sub_of_residue_eq v bL (hPi (out q1)) (hPi (out q2)) fun i => congrFun h i

  have hσθi : σ ↑θ⁻¹ = -↑θ⁻¹ :=
    eq_neg_inv_of_mul_neg θ _ (by rw [← hσθ, ← map_mul, Units.inv_mul, map_one])
  have hσei : σ ↑e⁻¹ = ↑e⁻¹ :=
    eq_inv_of_mul e _ (by rw [← hσe, ← map_mul, Units.inv_mul, map_one])

  have memP : ∀ x, IsIntB v bL x → σ x = x → x ∈ P := fun x h h' => (hP x).2 ⟨h, h'⟩
  have hθθ : σ (↑θ * ↑θ) = ↑θ * ↑θ := by rw [map_mul, hσθ, neg_mul_neg]
  have hθθi : σ (↑θ⁻¹ * ↑θ⁻¹) = ↑θ⁻¹ * ↑θ⁻¹ := by rw [map_mul, hσθi, neg_mul_neg]
  have dmem : (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθ hθ) hθθ
  let dP : P := ⟨_, dmem⟩
  have dimem : (↑θ⁻¹ * ↑θ⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθi hθi) hθθi
  let diP : P := ⟨_, dimem⟩
  have emem : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ he hσe
  let eP : P := ⟨_, emem⟩
  have eimem : (↑e⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ hei hσei
  let eiP : P := ⟨_, eimem⟩
  have hhalf : (2⁻¹ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  have hmem2 : ((2⁻¹ : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ∈ P := memP _ (fun i => by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hhalf (h1 i)) (by
      rw [Algebra.smul_def, mul_one, Algebra.TensorProduct.algebraMap_apply, hσdef,
        Algebra.TensorProduct.map_tmul, map_one]; rfl)
  let hh : P := ⟨_, hmem2⟩
  have h2P : (2 : P) * hh = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2⁻¹ : v.adicCompletion ℚ) • 1) = 1
    have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := by
      intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
    rw [mul_smul_comm, mul_one, ← map_ofNat (algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)) 2,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h20, one_smul]
  have hdP : dP * diP = 1 := by
    apply Subtype.ext
    show (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) * (↑θ⁻¹ * ↑θ⁻¹) = 1
    exact sq_mul_inv_sq θ
  have heP : eP * eiP = 1 := Subtype.ext (Units.mul_inv e)
  obtain ⟨a', b', hab⟩ := GlobalTheory.FinRingNorm.exists_sq_sub_mul_sq_eq (P ⧸ I)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I hh) (by rw [← map_ofNat (Ideal.Quotient.mk I) 2, ← map_mul, h2P, map_one]))
    (Ideal.Quotient.mk I dP) (Ideal.Quotient.mk I eP)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I diP) (by rw [← map_mul, hdP, map_one]))
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I eiP) (by rw [← map_mul, heP, map_one]))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : a ^ 2 - dP * b ^ 2 - eP ∈ I := by
    refine Ideal.Quotient.eq.1 ?_
    simpa only [map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I),
      map_pow (Ideal.Quotient.mk I)] using hab
  rw [hmemI] at hmem
  refine ⟨(a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L), isIntB_add v bL (hPi a) (hmul _ _ (hPi b) hθ), ?_⟩
  have hσz : σ ((a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L)) = (a : v.adicCompletion ℚ ⊗[ℚ] L) - (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [map_add (f := _), map_mul, hPs a, hPs b, hσθ, mul_neg, ← sub_eq_add_neg]
  rw [hσz, norm_expand]
  exact hmem
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensorStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  first | (exact @GlobalTheory.ResidueNorm.exists_norm_mod_small) | (exact GlobalTheory.ResidueNorm.exists_norm_mod_small) | (intros; apply GlobalTheory.ResidueNorm.exists_norm_mod_small  <;> assumption)
end
end
