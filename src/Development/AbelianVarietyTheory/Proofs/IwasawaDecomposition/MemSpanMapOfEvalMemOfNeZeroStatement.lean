module

public import Mathlib

@[expose] public section

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  intro k _ _ σ τ M D hD P hP
  classical
  let Γ : Finset (τ →₀ ℕ) := P.support.biUnion (fun m => (P.coeff m).support)
  let Q : (τ →₀ ℕ) → MvPolynomial σ k := fun γ =>
    ∑ m ∈ P.support, monomial m ((P.coeff m).coeff γ)
  have hQ : ∀ γ m, (Q γ).coeff m = (P.coeff m).coeff γ := by
    intro γ m
    simp only [Q, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp [notMem_support_iff.mp h]
  have hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) •
      map (algebraMap k (MvPolynomial τ k)) (Q γ) := by
    ext m : 1
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]
    have hmul (γ : τ →₀ ℕ) :
        monomial γ (1 : k) * C ((P.coeff m).coeff γ) =
          monomial γ ((P.coeff m).coeff γ) := by
      rw [mul_comm, C_mul_monomial, mul_one]
    simp only [hmul]
    by_cases hm : m ∈ P.support
    · conv_lhs => rw [as_sum (P.coeff m)]
      apply Finset.sum_subset
      · intro γ hγ
        exact Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩
      · intro γ _ hγ
        rw [notMem_support_iff.mp hγ, monomial_zero]
    · rw [notMem_support_iff.mp hm]
      simp
  have hevid (y : τ → k) : (eval y).comp (algebraMap k (MvPolynomial τ k)) =
      RingHom.id k := by
    ext c
    simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]
  have hevP (y : τ → k) : map (eval y) P =
      ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ := by
    conv_lhs => rw [hdec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]
  have hQM : ∀ γ ∈ Γ, Q γ ∈ M := by
    intro β hβ
    by_contra hnot
    obtain ⟨L, hLβ, hLM⟩ := Submodule.exists_le_ker_of_notMem hnot
    let R : MvPolynomial τ k := ∑ γ ∈ Γ, monomial γ (L (Q γ))
    have hR (y : τ → k) : eval y R = L (map (eval y) P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hevP, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]
    have hRD : R * D = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_zero]
      by_cases hy : eval y D = 0
      · rw [hy, mul_zero]
      · rw [hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]
    have hR0 : R = 0 := (mul_eq_zero.mp hRD).resolve_right hD
    have hcoef : R.coeff β = L (Q β) := by
      simp only [R, coeff_sum, coeff_monomial]
      rw [Finset.sum_ite_eq', ite_eq_left hβ]
    exact hLβ (by simp [← hcoef, hR0])
  rw [hdec]
  refine Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨Q γ, hQM γ hγ, rfl⟩
