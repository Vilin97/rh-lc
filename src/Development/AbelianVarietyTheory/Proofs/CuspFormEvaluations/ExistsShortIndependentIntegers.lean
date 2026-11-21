module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

@[expose] public section

open NumberField Module Submodule
open scoped nonZeroDivisors

namespace GlobalTheory

namespace ShortIntegers

section Pairing

variable {V : Type} [AddCommGroup V] [Module ℚ V]

end Pairing

variable {K : Type} [Field K] [NumberField K]

noncomputable def realCoords {M : ℕ} (e : Fin M ≃ (K →+* ℂ)) (ε : ℝ) :
    K →ₗ[ℚ] EuclideanSpace ℝ (Fin M) where
  toFun x := WithLp.toLp 2 fun i => (e i x).re + ε * (e i x).im
  map_add' x y := by
    ext i
    simp
    ring
  map_smul' c x := by
    ext i
    simp [Rat.smul_def]
    ring

end ShortIntegers

open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma sum_embeddings_eq_zero_of_conjugate_neg {K : Type} [Field K] [NumberField K] (f : (K →+* ℂ) → ℝ)
    (hf : ∀ σ, f (NumberField.ComplexEmbedding.conjugate σ) = - f σ) : ∑ σ, f σ = 0 := by
  have h := Equiv.sum_comp (NumberField.ComplexEmbedding.involutive_conjugate K).toPerm f
  simp only [Function.Involutive.coe_toPerm, hf, Finset.sum_neg_distrib] at h
  linarith

open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma inner_realCoords_one_neg_one_eq_trace {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) (x y : K) :
    inner ℝ (_root_.GlobalTheory.ShortIntegers.realCoords e 1 x) (_root_.GlobalTheory.ShortIntegers.realCoords e (-1) y)
      = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) := by
  have htrace : ((Algebra.trace ℚ K (x * y) : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ (x * y) := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ (x * y))
      (fun σ => σ (x * y)) (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ)]
    simp
  have ht := congrArg Complex.re htrace
  simp [PiLp.inner_apply, _root_.GlobalTheory.ShortIntegers.realCoords]
  simp at ht
  rw [ht, Equiv.sum_comp e (fun σ => ((σ y).re + -(σ y).im) * ((σ x).re + (σ x).im)),
    ← Finset.sum_sub_distrib]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => (σ x).im * (σ y).re - (σ x).re * (σ y).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq]; ring)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

open NumberField Module Submodule in
open scoped nonZeroDivisors in
private lemma norm_sq_realCoords_eq_sum_norm_sq {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) {ε : ℝ} (hε : ε ^ 2 = 1) (x : K) :
    ‖_root_.GlobalTheory.ShortIntegers.realCoords e ε x‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [_root_.GlobalTheory.ShortIntegers.realCoords, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs,
    sq_abs]
  rw [Equiv.sum_comp e (fun σ => ((σ x).re + ε * (σ x).im) ^ 2)]
  have h0 := sum_embeddings_eq_zero_of_conjugate_neg (K := K) (fun σ => 2 * ε * (σ x).re * (σ x).im)
    (by intro σ; simp [NumberField.ComplexEmbedding.conjugate_coe_eq])
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  linear_combination (σ x).im ^ 2 * hε

private lemma norm_embedding_le_norm_realCoords {K : Type} [Field K] [NumberField K] {M : ℕ}
    (e : Fin M ≃ (K →+* ℂ)) {ε : ℝ} (hε : ε ^ 2 = 1) (x : K) (σ : K →+* ℂ) :
    ‖σ x‖ ≤ ‖ShortIntegers.realCoords e ε x‖ := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
  rw [norm_sq_realCoords_eq_sum_norm_sq e hε]
  exact Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ x‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ σ)

private lemma inv_abs_discr_le_prod_norm {K : Type} [Field K] [NumberField K] {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (hx0 : x ≠ 0) :
    |(NumberField.discr K : ℝ)|⁻¹ ≤ ∏ σ : K →+* ℂ, ‖σ x‖ := by
  let J : FractionalIdeal (𝓞 K)⁰ K := (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
  have hxJ : x ∈ J := by
    dsimp only [J]
    rw [← FractionalIdeal.mem_coeToSubmodule, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K),
      inv_inv, FractionalIdeal.coeToSubmodule_dual_one]
    exact hx
  have hJ : J ≠ 0 := by
    rintro h
    exact hx0 ((FractionalIdeal.mem_zero_iff _).mp (h ▸ hxJ))
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc
      _ ≤ J * J⁻¹ := by
        gcongr
        exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hxJ
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact hx0 (by simpa using hspan)
  have hNorm : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hspan, map_mul,
      FractionalIdeal.coeIdeal_absNorm]
    exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0))
  have hDiscr : FractionalIdeal.absNorm J = |(NumberField.discr K : ℚ)|⁻¹ := by
    dsimp only [J]
    rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal K (𝓞 K)]
    simp
  have hprod : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ x) (fun σ => σ x)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    simp
  rw [← norm_prod, ← hprod, Complex.norm_ratCast]
  rw [hDiscr] at hNorm
  simpa only [Rat.cast_inv, Rat.cast_abs, Rat.cast_intCast] using (Rat.cast_le (K := ℝ)).mpr hNorm


theorem _root_.GlobalTheory.exists_short_independent_integers (K : Type) [Field K] [NumberField K] :
    ∃ ω : Fin (Module.finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun k => (ω k : K)) ∧
      ∀ (s : K →+* ℂ) k, ‖s (ω k : K)‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  let e : Fin n ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq (NumberField.Embeddings.card K ℂ)).symm
  let φ := _root_.GlobalTheory.ShortIntegers.realCoords e 1
  let ψ := _root_.GlobalTheory.ShortIntegers.realCoords e (-1)
  have hpair : ∀ x y : K, inner ℝ (φ x) (ψ y) = ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) :=
    inner_realCoords_one_neg_one_eq_trace e
  let eι : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin n :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (NumberField.integralBasis K)).symm
  let α : Module.Basis (Fin n) ℚ K := (NumberField.integralBasis K).reindex eι
  let β := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) α
  have hαβ : ∀ i j, Algebra.trace ℚ K (α i * β j) = if i = j then 1 else 0 := by
    intro i j
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
  have hli : LinearIndependent ℝ (fun j => ψ (β j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ (φ (α i)) v) hc
    simp only [inner_sum, inner_smul_right, hpair, hαβ, inner_zero_right] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  have hliφ : LinearIndependent ℝ (fun j => φ (α j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v => inner ℝ v (ψ (β i))) hc
    simp only [sum_inner, inner_smul_left, hpair, hαβ, inner_zero_left] at h
    simpa [apply_ite (Rat.cast : ℚ → ℝ), mul_ite] using h
  have : NeZero n := ⟨(Module.finrank_pos (R := ℚ) (M := K)).ne'⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bφ := basisOfLinearIndependentOfCardEqFinrank hliφ hcard
  have hα_int : ∀ j, α j = algebraMap (𝓞 K) K (RingOfIntegers.basis K (eι.symm j)) := by
    intro j
    simp [α, NumberField.integralBasis_apply]
  have hdual : ∀ c : Fin n → ℤ,
      (∑ i, (c i : ℚ) • β i) ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    intro c
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    have hspan : algebraMap (𝓞 K) K a' ∈ Submodule.span ℤ (Set.range α) := by
      rw [show Set.range α = Set.range (NumberField.integralBasis K) from
        Module.Basis.range_reindex _ _]
      exact (NumberField.mem_span_integralBasis K).mpr ⟨a', rfl⟩
    refine Submodule.span_induction (p := fun x _ =>
      (Algebra.traceForm ℚ K) (∑ i, (c i : ℚ) • β i) x ∈ (algebraMap ℤ ℚ).range)
      ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨k, rfl⟩
      refine ⟨c k, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      simp [Algebra.traceForm_apply, mul_comm (β _) (α k), hαβ]
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro m x _ hx
      rw [map_zsmul]
      exact zsmul_mem hx m
  set D : ℝ := |((NumberField.discr K : ℤ) : ℝ)| with hDdef
  have hD : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  set lam : ℝ := D ^ (-(1 / (n : ℝ))) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hD _
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have hxz : ∑ i, c i • b i = ψ (∑ i, (c i : ℚ) • β i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul, Int.cast_smul_eq_zsmul, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [hxz] at hx0 ⊢
    have hz0 : (∑ i, (c i : ℚ) • β i) ≠ 0 := by
      rintro h
      apply hx0
      rw [h, map_zero]
    have hprod := inv_abs_discr_le_prod_norm (hdual c) hz0
    have hle := Finset.prod_le_prod₀ (s := Finset.univ) (fun σ _ => norm_nonneg
      (σ (∑ i, (c i : ℚ) • β i))) (g := fun _ => ‖ψ (∑ i, (c i : ℚ) • β i)‖)
      (fun σ _ => norm_embedding_le_norm_realCoords e (ε := -1) (by norm_num) _ σ)
    simp only [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card K ℂ] at hle
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    rw [hlam, one_div, Real.rpow_neg hD.le, ← Real.inv_rpow hD.le,
      Real.rpow_inv_le_iff_of_pos (inv_nonneg.mpr hD.le) (norm_nonneg _) hn0, Real.rpow_natCast]
    exact hprod.trans hle
  obtain ⟨y, hyli, hyint, hynorm⟩ := _root_.ReciprocityTheory.ChartRestriction.G.T0.transference_dual b lam hlam0 hmin
  choose m hm using hyint
  let ω : Fin n → 𝓞 K := fun i => ∑ j, m i j • RingOfIntegers.basis K (eι.symm j)
  have hω : ∀ i, ((ω i : 𝓞 K) : K) = ∑ j, (m i j : ℚ) • α j := by
    intro i
    simp [ω, hα_int, Int.cast_smul_eq_zsmul]
  have hy : ∀ i, y i = φ (ω i) := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis b fun j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, coe_basisOfLinearIndependentOfCardEqFinrank, hpair, hω, Finset.sum_mul, map_sum]
    simp [hαβ]
  refine ⟨ω, ?_, ?_⟩
  · have h := hyli.restrict_scalars' ℚ
    rw [show y = fun k => φ (ω k) from funext hy] at h
    exact LinearIndependent.of_comp φ h
  · intro s k
    have h1 : ‖s (ω k : K)‖ ≤ ‖y k‖ := by
      rw [hy]
      exact norm_embedding_le_norm_realCoords e (ε := 1) (by norm_num) _ s
    have h2 : (n : ℝ) ^ 2 / lam = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := by
      rw [hlam, Real.rpow_neg hD.le, div_inv_eq_mul]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    calc ‖s (ω k : K)‖ ≤ (n : ℝ) ^ 2 / lam := h1.trans (hynorm k)
      _ = (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := h2
      _ ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by norm_num))
          (Real.rpow_nonneg hD.le _)

end GlobalTheory
