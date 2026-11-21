module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

namespace GlobalTheory

open Polynomial IsLocalRing

universe u

variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K]
  [IsScalarTower B (ResidueField B) K]

omit [Algebra B W] [CommRing W] in
theorem algebraMap_eq_zero_iff_mem_maximalIdeal (b : B) :
    algebraMap B K b = 0 ↔ b ∈ maximalIdeal B := by
  rw [IsScalarTower.algebraMap_apply B (ResidueField B) K, map_eq_zero]
  exact residue_eq_zero_iff b

theorem isUnit_adjoinRoot_mk_of_aeval_ne_zero {θ : K} (hθ : IsIntegral (ResidueField B) θ)
    {μ : B[X]} (hμm : μ.Monic) (hμ : μ.map (residue B) = minpoly (ResidueField B) θ) {g : B[X]}
    (hg : aeval θ g ≠ 0) : IsUnit (AdjoinRoot.mk μ g) := by
  have : Module.Finite B (AdjoinRoot μ) := hμm.finite_adjoinRoot
  by_contra hn
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits hn
  have hM' : M.comap (algebraMap B (AdjoinRoot μ)) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap B (AdjoinRoot μ)) (algebraMap_isIntegral_iff.mpr inferInstance) M)
  have hco : IsCoprime (minpoly (ResidueField B) θ) (g.map (residue B)) := by
    rw [(minpoly.irreducible hθ).coprime_iff_not_dvd, minpoly.dvd_iff]
    rwa [← aeval_map_algebraMap (ResidueField B)] at hg
  obtain ⟨a, b, hab⟩ := hco
  obtain ⟨a, rfl⟩ := map_surjective (residue B) residue_surjective a
  obtain ⟨b, rfl⟩ := map_surjective (residue B) residue_surjective b
  have h₀ : (a * μ + b * g - 1).map (residue B) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add (f := _), Polynomial.map_mul,
      Polynomial.map_mul, hμ, hab, Polynomial.map_one, sub_self]
  have h₁ : AdjoinRoot.mk μ (a * μ + b * g - 1) ∈ M := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(a * μ + b * g - 1).as_sum_support_C_mul_X_pow, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap B (AdjoinRoot μ) _ ∈ M
    rw [← Ideal.mem_comap, hM', ← residue_eq_zero_iff, ← coeff_map, h₀, coeff_zero]
  rw [map_sub, map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, mul_zero,
    zero_add, map_one] at h₁
  have h₂ := sub_mem (M.mul_mem_left (AdjoinRoot.mk μ b) hgM) h₁
  rw [sub_sub_cancel] at h₂
  exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h₂)

theorem exists_isDiscreteValuationRing_of_maximalIdeal_eq_span {B : Type*} [CommRing B]
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

theorem exists_isDiscreteValuationRing_of_flat (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [Module.Flat V B]
    (hm : (maximalIdeal V).map (algebraMap V B) = maximalIdeal B)
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine exists_isDiscreteValuationRing_of_maximalIdeal_eq_span (t := algebraMap V B t) ?_ ?_ hs
  · rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)
    exact this (show t • x = t • (0 : B) by rw [smul_zero, Algebra.smul_def, hx])
  · rw [← hm, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

theorem exists_finite_dvr_algHom_mem_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (θ : K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ θ ∈ Set.range e := by
  let k := ResidueField B
  letI : Algebra k K := (ResidueField.lift (algebraMap B K)).toAlgebra
  have : IsScalarTower B k K := .of_algebraMap_eq fun b =>
    (ResidueField.lift_residue_apply (algebraMap B K) b).symm
  have hθ : IsIntegral k θ := (Algebra.IsIntegral.isIntegral (R := B) θ).tower_top
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hθ)
  let B' := AdjoinRoot μ
  have hμθ : aeval θ μ = 0 := by
    rw [← aeval_map_algebraMap k]
    exact (congrArg (aeval θ) hμ).trans (minpoly.aeval k θ)
  let e : B' →ₐ[B] K := AdjoinRoot.liftAlgHom μ (Algebra.ofId B K) θ hμθ
  have he₀ : e (AdjoinRoot.root μ) = θ := AdjoinRoot.liftAlgHom_root ..
  have he : ∀ g : B[X], e (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, he₀]
  have hu : ∀ y : B', e y ≠ 0 → IsUnit y := fun y hy => by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
    exact isUnit_adjoinRoot_mk_of_aeval_ne_zero hθ hμm hμ (he g ▸ hy)
  have : Nontrivial B' := e.toRingHom.domain_nontrivial
  have : IsLocalRing B' := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => by
    by_cases hy : e y = 0
    · exact Or.inr (hu _ (by simp [hy]))
    · exact Or.inl (hu _ hy)
  have hm : ∀ y : B', y ∈ maximalIdeal B' ↔ e y = 0 := fun y =>
    ⟨fun hy => by_contra fun h => hy (hu y h), fun hy h => (h.map e).ne_zero hy⟩
  have hfin : Module.Finite B B' := hμm.finite_adjoinRoot
  have : Module.Free B B' := hμm.free_adjoinRoot
  have hmap : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap, hm, AlgHom.commutes, algebraMap_eq_zero_iff_mem_maximalIdeal (K := K)]
      exact hb
    · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [hm, he, ← aeval_map_algebraMap k] at hy
      obtain ⟨c, hc⟩ := minpoly.dvd k θ hy
      obtain ⟨c, rfl⟩ := map_surjective (algebraMap B k) residue_surjective c
      have h₀ : (g - μ * c).map (algebraMap B k) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hμ, hc, sub_self]
      have h₁ : AdjoinRoot.mk μ (g - μ * c) ∈ (maximalIdeal B).map (algebraMap B B') := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [(g - μ * c).as_sum_support_C_mul_X_pow, map_sum]
        refine Ideal.sum_mem _ fun i _ => ?_
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        change algebraMap B B' _ ∈ _
        refine Ideal.mem_map_of_mem _ ?_
        rw [← residue_eq_zero_iff]
        change algebraMap B k _ = 0
        rw [← coeff_map, h₀, coeff_zero]
      rwa [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero] at h₁
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite B B'
  obtain ⟨_, _⟩ := exists_isDiscreteValuationRing_of_flat B B' hmap
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B').ne_top)
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := B) B'
  rw [hmap] at hc
  exact ⟨B', inferInstance, inferInstance, inferInstance, hc, inferInstance, hfin,
    FaithfulSMul.algebraMap_injective B B', e, ⟨fun y hy => hu y hy.ne_zero⟩,
    AdjoinRoot.root μ, he₀⟩

theorem exists_finite_dvr_algHom_subset_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (s : Finset K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ (s : Set K) ⊆ Set.range e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun _ _ h => h, Algebra.ofId B K, ‹IsLocalHom (algebraMap B K)›, by simp⟩
  | insert θ s _ ih =>
    obtain ⟨C, _, _, _, _, _, hfin, hinj, e, hloc, hs⟩ := ih
    letI : Algebra C K := (e : C →+* K).toAlgebra
    have : IsScalarTower B C K := .of_algebraMap_eq fun b => (e.commutes b).symm
    have : IsLocalHom (algebraMap C K) := hloc
    have : Module.Finite C K := .of_restrictScalars_finite B C K
    obtain ⟨D, _, _, _, _, _, hfin', hinj', e', hloc', hθ⟩ :=
      exists_finite_dvr_algHom_mem_range (B := C) θ
    letI : Algebra B D := ((algebraMap C D).comp (algebraMap B C)).toAlgebra
    have : IsScalarTower B C D := .of_algebraMap_eq fun _ => rfl
    refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Finite.trans C D, hinj'.comp hinj, e'.restrictScalars B, hloc', ?_⟩
    rw [Finset.coe_insert]
    refine Set.insert_subset hθ fun x hx => ?_
    obtain ⟨c, rfl⟩ := hs hx
    exact ⟨algebraMap C D c, e'.commutes c⟩

theorem exists_finite_dvr_residueField_ringHom :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by
  intro W _ _ _ _ K _ _ _
  letI : Algebra W K := ((algebraMap (ResidueField W) K).comp (residue W)).toAlgebra
  have : IsScalarTower W (ResidueField W) K := .of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap W K) := ⟨fun b hb => by
    by_contra hn
    exact hb.ne_zero ((algebraMap_eq_zero_iff_mem_maximalIdeal (K := K) b).mpr hn)⟩
  have hfin : Module.Finite W K := Module.Finite.trans (ResidueField W) K
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨W', _, _, _, _, _, hfin', hinj, e, hloc, hsub⟩ :=
    exists_finite_dvr_algHom_subset_range (B := W) s
  have hsurj : Function.Surjective e := fun x => by
    have : x ∈ LinearMap.range e.toLinearMap := by
      have h : Submodule.span W (s : Set K) ≤ LinearMap.range e.toLinearMap :=
        Submodule.span_le.mpr hsub
      exact h (hs ▸ Submodule.mem_top)
    exact this
  let f : ResidueField W' →+* K := ResidueField.lift (e : W' →+* K)
  have hf : ∀ w, f (residue W' w) = e w := fun w => ResidueField.lift_residue_apply _ w
  have hbij : Function.Bijective f := ⟨f.injective, fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨_, hf w⟩⟩
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfin',
    hinj, (RingEquiv.ofBijective f hbij).symm, fun v => ?_⟩
  refine (RingEquiv.symm_apply_eq _).mpr ?_
  rw [RingEquiv.ofBijective_apply, hf, e.commutes]
  rfl

end GlobalTheory
