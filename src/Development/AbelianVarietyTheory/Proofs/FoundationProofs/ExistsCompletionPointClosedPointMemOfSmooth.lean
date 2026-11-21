module

public import Mathlib

namespace GlobalTheory

open Polynomial IsLocalRing
open scoped TensorProduct

-- The algebraic proofs from ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa are local
-- here because that file uses legacy imports.
section Lift

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private theorem isUnit_of_isUnit_map_of_henselian (I : Ideal B) [HenselianRing B I] (π : B →+* C)
    (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) {b : B} (hb : IsUnit (π b)) :
    IsUnit b := by
  have hker : RingHom.ker π ≤ Ring.jacobson B :=
    fun x hx => HenselianRing.jac (I := I) ((hI x).mpr hx)
  have := isLocalHom_of_le_jacobson hker
  apply (isUnit_map_iff (Ideal.Quotient.mk (RingHom.ker π)) b).mp
  simpa only [RingHom.quotientKerEquivOfSurjective_symm_apply] using
    hb.map (π.quotientKerEquivOfSurjective hπ).symm

private theorem isLocalRing_of_surjective_of_henselian [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (π : B →+* C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) : IsLocalRing C := by
  have : Nontrivial C := by
    by_contra hC
    rw [not_nontrivial_iff_subsingleton] at hC
    exact not_isUnit_zero (isUnit_of_isUnit_map_of_henselian I π hπ hI (b := 0)
      (isUnit_of_subsingleton _))
  exact IsLocalRing.of_surjective' π hπ

private theorem exists_algHom_lift_of_isStandardEtale [Algebra.IsStandardEtale R A] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R A) := inferInstance
  have h₀ : P.P.HasMap (φ P.x) := P.hasMap.map φ
  obtain ⟨t₀, ht₀⟩ := hπ (φ P.x)
  have hu : ∀ b, IsUnit (π b) → IsUnit b := fun b hb =>
    isUnit_of_isUnit_map_of_henselian I (π : B →+* C) hπ hI hb
  obtain ⟨t, ht, htt⟩ := HenselianRing.is_henselian (I := I)
    (P.f.map (algebraMap R B)) (P.monic_f.map _) t₀
    (by rw [hI, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]; exact h₀.1)
    (by
      refine IsUnit.map _ (hu _ ?_)
      rw [derivative_map, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]
      exact h₀.isUnit_derivative_f)
  have hπt : π t = φ P.x := by
    rw [hI, map_sub, sub_eq_zero] at htt
    rw [htt, ht₀]
  have h₁ : P.P.HasMap t :=
    ⟨by rwa [IsRoot.def, eval_map_algebraMap] at ht,
      hu _ (by rw [← aeval_algHom_apply, hπt]; exact h₀.2)⟩
  exact ⟨(P.P.lift t h₁).comp P.equivRing.toAlgHom, P.hom_ext (by simp [hπt])⟩

private theorem exists_algHom_lift_of_smooth [Algebra.Smooth R A] [IsLocalRing B] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  have : IsLocalRing C := isLocalRing_of_surjective_of_henselian I (π : B →+* C) hπ hI
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := (maximalIdeal C).comap φ)
  have hφf : IsUnit (φ f) := by simpa using hf
  let φ' : Localization.Away f →ₐ[R] C := IsLocalization.Away.liftAlgHom f hφf
  choose b hb using fun i : Fin n => hπ (φ' (algebraMap _ _ (MvPolynomial.X (R := R) i)))
  let χ : MvPolynomial (Fin n) R →ₐ[R] C := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : π.comp (MvPolynomial.aeval b) = χ := by ext i; simp [χ, hb]
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  letI := χ.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  let π' : B →ₐ[MvPolynomial (Fin n) R] C := ⟨π, fun r => congr($hχ r)⟩
  let φ'' : Localization.Away f →ₐ[MvPolynomial (Fin n) R] C := ⟨φ', fun r => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_isStandardEtale I π' hπ hI φ''
  refine ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A _ a)).trans (show φ' (algebraMap A _ a) = φ a by simp [φ'])

end Lift

section SeparablePoints

variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]

private theorem nonempty_algHom_of_etale_of_isSepClosed [IsSepClosed K] [Algebra.Etale R A] (q : Ideal A)
    [q.IsPrime] (hq : q.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  let p := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have : q.LiesOver p := ⟨hq.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let ι : p.ResidueField →ₐ[R] K := Ideal.ResidueField.liftₐ p (Algebra.ofId R K) le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, p])
  letI := ι.toAlgebra
  have : IsScalarTower R p.ResidueField K := .of_algebraMap_eq fun r => (ι.commutes r).symm
  let j : q.ResidueField →ₐ[p.ResidueField] K := IsSepClosed.lift
  exact ⟨(j.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩

private theorem nonempty_algHom_of_smooth_of_isSepClosed [IsSepClosed K] [Algebra.Smooth R A] (p : Ideal A)
    [p.IsPrime] (hp : p.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  have : Infinite K := by
    by_contra hK
    rw [not_infinite_iff_finite] at hK
    have := IsSepClosed.isAlgClosed_of_perfectField K
    exact not_finite K
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := p)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let p' : PrimeSpectrum S := ⟨p.map (algebraMap A S),
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› hdisj⟩
  have hp' : p'.asIdeal.comap (algebraMap R S) = RingHom.ker (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R A S, ← Ideal.comap_comap, ← hp]
    exact congrArg _ (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj)
  have hopen := (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := P) (S := S)).isOpen_range
  obtain ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hh, hsub⟩ := PrimeSpectrum.isBasis_basic_opens
    |>.exists_subset_of_mem_open (Set.mem_range_self p') hopen
  obtain ⟨b, hb⟩ : ∃ b : Fin n → K, MvPolynomial.aeval b h ≠ 0 := by
    by_contra hc
    push Not at hc
    have h₀ : h.map (algebraMap R K) = 0 :=
      MvPolynomial.funext fun b => by rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, hc, map_zero]
    apply hh
    rw [h.as_sum]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [MvPolynomial.monomial_eq]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap P S (algebraMap R P _) ∈ p'.asIdeal
    rw [← IsScalarTower.algebraMap_apply, ← Ideal.mem_comap, hp', RingHom.mem_ker,
      ← MvPolynomial.coeff_map, h₀]
    simp
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  have : IsScalarTower R P K :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  obtain ⟨q, hq⟩ := hsub (a := ⟨RingHom.ker (algebraMap P K), RingHom.ker_isPrime _⟩) hb
  obtain ⟨ψ⟩ := nonempty_algHom_of_etale_of_isSepClosed (R := P) (K := K) q.asIdeal
    congr($(hq).asIdeal)
  exact ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩

private theorem exists_etale_subset_range [IsLocalRing B] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K]
    {ι : Type*} [Finite ι] (b : ι → K) :
    ∃ (P : StandardEtalePair B) (ε : P.Ring →ₐ[B] K), ∀ i, b i ∈ Set.range ε := by
  let k := ResidueField B
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hi)
  let P : StandardEtalePair B := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : B[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap B k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  refine ⟨P, P.lift _ hP, fun i => ?_⟩
  have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g, rfl⟩ := map_surjective (algebraMap B k) residue_surjective g
  refine ⟨aeval P.X g, ?_⟩
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  exact congrArg Subtype.val hg

end SeparablePoints

section EtaleLift

universe u

variable {R : Type*} {A B : Type u} {K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsLocalRing B] [Algebra B K] [IsScalarTower R B K]
  [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]

private theorem exists_etale_algHom_lift_of_smooth [Algebra.Smooth R A] (φ : A →ₐ[R] K) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (ψ : A →+* W)
      (ε : W →ₐ[B] K), ψ.comp (algebraMap R A) = (algebraMap B W).comp (algebraMap R B) ∧
        ∀ a, ε (ψ a) = φ a := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  let φ' : S →ₐ[R] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨Q, ε, hε⟩ := exists_etale_subset_range (B := B)
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let E := Q.Ring
  letI : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B E := .of_algebraMap_eq' rfl
  let χ : P →ₐ[R] K := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : (ε.restrictScalars R).comp (MvPolynomial.aeval c) = χ := by
    ext i
    exact (congrArg ε (MvPolynomial.aeval_X c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := R) c).toAlgebra
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower B E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp B E W,
    (Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap A S), ε'.restrictScalars B, RingHom.ext fun r => ?_, fun a => ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap A S (algebraMap R A r) = (algebraMap R E r) ⊗ₜ[P] (1 : S)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R P S,
      ← (MvPolynomial.aeval (R := R) c).commutes r]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  · change ε' ((1 : E) ⊗ₜ[P] algebraMap A S a) = φ a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (show φ' (algebraMap A _ a) = φ a by simp [φ'])

end EtaleLift

section DiscreteValuation

private theorem exists_isDiscreteValuationRing_of_maximalIdeal_eq_span {B : Type*} [CommRing B]
    [IsLocalRing B] {t : B} (ht : t ∈ nonZeroDivisors B) (hm : maximalIdeal B = Ideal.span {t})
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  classical
  have key : ∀ x : B, x ≠ 0 → ∃ (n : ℕ) (u : Bˣ), t ^ n * u = x := by
    intro x hx
    have h : ∃ n : ℕ, ¬ t ^ n ∣ x := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← Ideal.mem_bot, ← hs, Ideal.mem_iInf]
      intro n
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hc n
    have h₀ : Nat.find h ≠ 0 := fun h₀ => Nat.find_spec h (by simp [h₀])
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h₀
    obtain ⟨u, rfl⟩ := not_not.mp (Nat.find_min h (hn ▸ n.lt_succ_self))
    have hu : IsUnit u := by
      by_contra hu
      have h₁ : u ∈ maximalIdeal B := hu
      rw [hm, Ideal.mem_span_singleton] at h₁
      exact Nat.find_spec h (by rw [hn, pow_succ]; exact mul_dvd_mul_left _ h₁)
    exact ⟨n, hu.unit, rfl⟩
  have hreg : ∀ x : B, x ≠ 0 → x ∈ nonZeroDivisors B := fun x hx => by
    obtain ⟨n, u, rfl⟩ := key x hx
    exact mul_mem (pow_mem ht n) u.isUnit.mem_nonZeroDivisors
  have : NoZeroDivisors B := ⟨fun {a b} hab => by
    by_contra hc
    push Not at hc
    exact hc.1 (mem_nonZeroDivisors_iff_right.mp (hreg b hc.2) a hab)⟩
  have : IsDomain B := NoZeroDivisors.to_isDomain B
  have hp : Prime t := by
    rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero ht), ← hm]
    infer_instance
  exact ⟨this, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨t, hp.irreducible, fun {x} hx => by
      obtain ⟨n, u, h⟩ := key x hx
      exact ⟨n, u, h⟩⟩⟩

variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

private theorem exists_isDiscreteValuationRing_of_unramified (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [IsLocalHom (algebraMap V B)] [Module.Flat V B] [Algebra.EssFiniteType V B]
    [Algebra.FormallyUnramified V B] : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing V B
  have hs := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine exists_isDiscreteValuationRing_of_maximalIdeal_eq_span (t := algebraMap V B t) ?_ ?_ hs
  · rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)
    exact this (show t • x = t • (0 : B) by rw [smul_zero, Algebra.smul_def, hx])
  · rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := V), ht.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]

end DiscreteValuation

end GlobalTheory

@[expose] public section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

section Lift

variable {X S : Scheme.{u}} (f : X ⟶ S)


theorem _root_.GlobalTheory.range_subset_opens_of_isLocalRing {B : CommRingCat.{u}} [IsLocalRing B] (s : Spec B ⟶ S)
    {U : S.Opens} (h : s (closedPoint B) ∈ U) : Set.range s ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((specializes_closedPoint y).map s.base.hom.continuous).mem_open U.isOpen h


theorem _root_.GlobalTheory.exists_isAffineOpen_pair (x : X) {O : X.Opens} (hx : x ∈ O) :
    ∃ (U : S.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ f ⁻¹ᵁ U ∧ V ≤ O ∧
      x ∈ V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((O ⊓ f ⁻¹ᵁ U : X.Opens) : Set X) from ⟨hx, hxU⟩) (O ⊓ f ⁻¹ᵁ U).isOpen
  exact ⟨U, V, hU, hV, fun y hy => (hVle hy).2, fun y hy => (hVle hy).1, hxV⟩


theorem _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen [Smooth f] {U : S.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {B C : CommRingCat.{u}}
    (π : B ⟶ C) (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s)
    (hs : Set.range s ⊆ U) (hx : Set.range x₀ ⊆ V)
    (H : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
      [Algebra R B] [Algebra R C] (π' : B →ₐ[R] C), (∀ b, π' b = π b) →
      ∀ φ : A →ₐ[R] C, ∃ ψ : A →ₐ[R] B, π'.comp ψ = φ) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  have hsm : (f.appLE U V hVU).hom.Smooth := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hxV : Set.range x₀.base ⊆ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hx
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hs
  set a : Γ(X, V) ⟶ C := Spec.preimage (IsOpenImmersion.lift hV.fromSpec x₀ hxV) with ha_def
  set b : Γ(S, U) ⟶ B := Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have ha : Spec.map a ≫ hV.fromSpec = x₀ := by
    rw [ha_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hab : f.appLE U V hVU ≫ a = b ≫ π := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb, reassoc_of% ha, h]
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) C := (b ≫ π).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  let π' : B →ₐ[Γ(S, U)] C := { π.hom with commutes' := fun _ => rfl }
  let φ : Γ(X, V) →ₐ[Γ(S, U)] C :=
    { a.hom with commutes' := fun r => congrArg (fun k => k.hom r) hab }
  obtain ⟨ψ, hψ⟩ := H Γ(S, U) Γ(X, V) π' (fun _ => rfl) φ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← ha]
    congr 2
    ext y
    exact congrArg (fun k => k y) hψ
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc,
      ← Spec.map_comp, ← hb]
    congr 2
    ext r
    exact ψ.commutes r


theorem _root_.GlobalTheory.lift_ext_of_unramified [FormallyUnramified f] [LocallyOfFiniteType f]
    {B C : CommRingCat.{u}} (π : B ⟶ C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥) {x₁ x₂ : Spec B ⟶ X}
    (h₀ : Spec.map π ≫ x₁ = Spec.map π ≫ x₂) (h : x₁ ≫ f = x₂ ≫ f) : x₁ = x₂ := by
  let g : Spec B ⟶ pullback f f := pullback.lift x₁ x₂ h
  have hg : Spec.map π ≫ g = (Spec.map π ≫ x₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp only [g, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [g, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, h₀]
  have hrange : Set.range g.base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hkm : RingHom.ker π.hom ≤ m := hj.trans (sInf_le ⟨bot_le, hm⟩)
    haveI := hm.isPrime
    let z : PrimeSpectrum C := ⟨m.map π.hom, Ideal.map_isPrime_of_surjective hπ hkm⟩
    have hz : PrimeSpectrum.comap π.hom z = ⟨m, hm.isPrime⟩ := by
      ext1
      show Ideal.comap π.hom (m.map π.hom) = m
      rw [Ideal.comap_map_of_surjective' _ hπ, sup_eq_left.mpr hkm]
    have hgp : g.base ⟨m, hm.isPrime⟩ ∈ (pullback.diagonal f).opensRange := by
      rw [← hz]
      show (Spec.map π ≫ g).base z ∈ _
      rw [hg]
      exact ⟨_, rfl⟩
    have hsp : y ⤳ ⟨m, hm.isPrime⟩ := (PrimeSpectrum.le_iff_specializes y ⟨m, hm.isPrime⟩).mp hym
    exact (hsp.map g.base.hom.continuous).mem_open (pullback.diagonal f).opensRange.isOpen hgp
  obtain ⟨l, hl⟩ : ∃ l, l ≫ pullback.diagonal f = g :=
    ⟨IsOpenImmersion.lift (pullback.diagonal f) g hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have e₁ : x₁ = l := by
    rw [← pullback.lift_fst x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  have e₂ : x₂ = l := by
    rw [← pullback.lift_snd x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  rw [e₁, e₂]

noncomputable def reducePoint {B C : CommRingCat.{u}} (π : B ⟶ C) (s : Spec B ⟶ S)
    (x : {x : Spec B ⟶ X // x ≫ f = s}) : {x₀ : Spec C ⟶ X // x₀ ≫ f = Spec.map π ≫ s} :=
  ⟨Spec.map π ≫ x.1, by rw [Category.assoc, x.2]⟩

section Quotient

variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
variable {X S : Scheme.{u}} (f : X ⟶ S) in
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S) in

theorem _root_.GlobalTheory.reducePoint_quotient_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (Ideal.Quotient.mk I)) s) := by
  rintro ⟨x₀, hx₀⟩
  have hker : ∀ b : B, b ∈ I ↔ Ideal.Quotient.mk I b = 0 := fun b =>
    Ideal.Quotient.eq_zero_iff_mem.symm
  haveI : IsLocalRing (B ⧸ I) := isLocalRing_of_surjective_of_henselian I
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hker
  haveI : IsLocalRing (CommRingCat.of (B ⧸ I)) := ‹IsLocalRing (B ⧸ I)›
  have hclosed : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base
      (closedPoint (CommRingCat.of (B ⧸ I))) = closedPoint B := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (B ⧸ I)) = maximalIdeal B
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    _root_.GlobalTheory.exists_isAffineOpen_pair f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) (O := ⊤) trivial
  have hfx : f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) = s (closedPoint B) := by
    change (x₀ ≫ f).base _ = _
    rw [hx₀]
    exact congrArg s.base hclosed
  have hs : Set.range s ⊆ U := _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  have hx : Set.range x₀ ⊆ V := _root_.GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV
  obtain ⟨x, hπx, hxf⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU _ s x₀ hx₀ hs hx
    (fun R A _ _ _ _ _ _ π' hπ' φ =>
      exists_algHom_lift_of_smooth I π'
        (fun c => by
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨b, hπ' b⟩)
        (fun b => by rw [hπ']; exact hker b) φ)
  exact ⟨⟨x, hxf⟩, Subtype.ext hπx⟩

end Quotient

section Residue

variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)


theorem _root_.GlobalTheory.reducePoint_residue_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (residue B)) s) :=
  _root_.GlobalTheory.reducePoint_quotient_surjective f B (maximalIdeal B) s

end Residue

end Lift

section QuasiSection

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]


theorem _root_.GlobalTheory.exists_etale_point_of_smooth (B : Type u) [CommRing B] [IsLocalRing B]
    (K : Type*) [Field K] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K] [IsSepClosed K]
    (s : Spec (.of B) ⟶ S) (O : X.Opens) (hO : ∃ x ∈ O, f x = s (closedPoint B)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (_ : W →ₐ[B] K)
      (y : Spec (.of W) ⟶ X),
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B W)) ≫ s ∧ Set.range y ⊆ O := by
  obtain ⟨x, hxO, hfx⟩ := hO
  obtain ⟨U, V, hU, hV, hVU, hVO, hxV⟩ := _root_.GlobalTheory.exists_isAffineOpen_pair f x hxO
  have hsm := HasRingHomProperty.appLE @Smooth f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  have hsU : Set.range s.base ⊆ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  set b : Γ(S, U) ⟶ CommRingCat.of B :=
    Spec.preimage (IsOpenImmersion.lift hU.fromSpec s hsU) with hb_def
  have hb : Spec.map b ≫ hU.fromSpec = s := by
    rw [hb_def, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨P, hP⟩ : x ∈ Set.range hV.fromSpec.base := by rw [hV.range_fromSpec]; exact hxV
  have hPm : Ideal.comap (f.appLE U V hVU).hom P.asIdeal = Ideal.comap b.hom (maximalIdeal B) := by
    have e : hU.fromSpec.base ((Spec.map (f.appLE U V hVU)).base P) =
        hU.fromSpec.base ((Spec.map b).base (closedPoint B)) := by
      change (Spec.map (f.appLE U V hVU) ≫ hU.fromSpec).base P = (Spec.map b ≫ hU.fromSpec).base _
      rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, hb]
      change f.base (hV.fromSpec.base P) = _
      rw [hP, hfx]
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e)
  letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(S, U) B := b.hom.toAlgebra
  letI : Algebra Γ(S, U) K := ((algebraMap B K).comp b.hom).toAlgebra
  haveI : IsScalarTower Γ(S, U) B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Smooth Γ(S, U) Γ(X, V) := hsm
  haveI := P.isPrime
  obtain ⟨φ⟩ := nonempty_algHom_of_smooth_of_isSepClosed (K := K) P.asIdeal (by
    change Ideal.comap (f.appLE U V hVU).hom P.asIdeal = _
    rw [hPm]
    ext r
    change b.hom r ∈ maximalIdeal B ↔ algebraMap B K (b.hom r) = 0
    rw [IsScalarTower.algebraMap_apply B (ResidueField B) K, map_eq_zero]
    exact (residue_eq_zero_iff (b.hom r)).symm)
  obtain ⟨W, iW, iBW, hE, ψ, ε, hψ, -⟩ := exists_etale_algHom_lift_of_smooth (B := B) (K := K) φ
  refine ⟨W, iW, iBW, hE, ε, Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : f.appLE U V hVU ≫ CommRingCat.ofHom ψ = b ≫ CommRingCat.ofHom (algebraMap B W) := by
      ext r
      exact congrArg (fun k => k r) hψ
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← hb,
      ← Spec.map_comp_assoc, e, Spec.map_comp_assoc]
  · rintro _ ⟨z, rfl⟩
    apply hVO
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base z, rfl⟩


theorem _root_.GlobalTheory.range_fst_residue {B : Type u} [CommRing B] [IsLocalRing B] (g : X ⟶ Spec (.of B)) :
    Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (residue B)))) =
      g ⁻¹' {closedPoint B} := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  have key : ∀ z : Spec (.of (ResidueField B)),
      (Spec.map (CommRingCat.ofHom (residue B))).base z = closedPoint B := by
    intro z
    apply PrimeSpectrum.ext
    show Ideal.comap (residue B) z.asIdeal = maximalIdeal B
    haveI := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, ker_residue]
  ext y
  constructor
  · rintro ⟨z, rfl⟩; exact key z
  · rintro rfl; exact ⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩

end QuasiSection

section Field

end Field

section DiscreteValuation


theorem _root_.GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom (V V' : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsLocalRing V'] [Algebra V V']
    [IsLocalHom (algebraMap V V')] [Algebra.Etale V V'] :
    ∃ (_ : IsDomain V') (_ : IsDiscreteValuationRing V'),
      (maximalIdeal V).map (algebraMap V V') = maximalIdeal V' ∧
      Module.FaithfullyFlat V V' ∧
      Module.Finite (ResidueField V) (ResidueField V') ∧
      Algebra.IsSeparable (ResidueField V) (ResidueField V') ∧
      ∃ (_ : Algebra (FractionRing V) (FractionRing V'))
        (_ : IsScalarTower V (FractionRing V) (FractionRing V')),
        Module.Finite (FractionRing V) (FractionRing V') ∧
        Algebra.IsSeparable (FractionRing V) (FractionRing V') := by
  obtain ⟨hD, hR⟩ := exists_isDiscreteValuationRing_of_unramified V V'
  have hF : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap V V') := FaithfulSMul.algebraMap_injective V V'
  haveI : FaithfulSMul V (FractionRing V') := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V V' (FractionRing V')]
    exact (IsFractionRing.injective V' (FractionRing V')).comp hinj
  letI := FractionRing.liftAlgebra V (FractionRing V')
  haveI := FractionRing.isScalarTower_liftAlgebra V (FractionRing V')
  have : Algebra.EssFiniteType V' (FractionRing V') :=
    .of_isLocalization _ (nonZeroDivisors V')
  have : Algebra.FormallyUnramified V' (FractionRing V') := .of_isLocalization (nonZeroDivisors V')
  have : Algebra.EssFiniteType V (FractionRing V') := .comp V V' _
  have : Algebra.FormallyUnramified V (FractionRing V') := .comp V V' _
  have : Algebra.EssFiniteType (FractionRing V) (FractionRing V') := .of_comp V _ _
  have : Algebra.FormallyUnramified (FractionRing V) (FractionRing V') := .of_restrictScalars V _ _
  have hfin := Algebra.FormallyUnramified.finite_of_free (FractionRing V) (FractionRing V')
  have hsep := Algebra.FormallyUnramified.isSeparable (FractionRing V) (FractionRing V')
  exact ⟨hD, hR, Algebra.FormallyUnramified.map_maximalIdeal, hF, inferInstance, inferInstance,
    _, inferInstance, hfin, hsep⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

end DiscreteValuation

section SpecialFibre

variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of V)) [Smooth f]
  (U : (pullback f (Spec.map (CommRingCat.ofHom (residue V)))).Opens)

end SpecialFibre

section Main

end Main

end GlobalTheory
