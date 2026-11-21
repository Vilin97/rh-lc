module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem core {K V : Type} [NormedField K] [IsUltrametricDist K] [SMul K V] {N g : ℕ}
    (P Q : V → Fin N → K) (L : V → Fin g → K) (Λ : V → Prop) (π δ : K) (ε : ℝ)
    (hπ0 : π ≠ 0) (hπ : ‖π‖ < 1) (hε0 : 0 ≤ ε) (hε : ε ≤ ‖π‖ ^ 2 * ‖δ‖)
    (hP : ∀ (c : K) v k, P (c • v) k = c * P v k) (hL : ∀ (c : K) v k, L (c • v) k = c * L v k)
    (hPQ : ∀ v k, ‖P v k - Q v k‖ ≤ ε * ‖L v‖) (hΛ : ∀ v, Λ v ↔ ∀ k, ‖Q v k‖ ≤ ‖δ‖)
    (hb : ∀ v, Λ v → ∀ j, ‖π * L v j‖ ≤ 1) (v : V) : Λ v ↔ ∀ k, ‖P v k‖ ≤ ‖δ‖ := by
  have hπp : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have key : ∀ v, ‖π‖ ^ 2 * ‖L v‖ ≤ 1 → (Λ v ↔ ∀ k, ‖P v k‖ ≤ ‖δ‖) := by
    intro v hv
    have h1 : ∀ k, ‖P v k - Q v k‖ ≤ ‖δ‖ := fun k => by
      refine (hPQ v k).trans ?_
      calc ε * ‖L v‖ ≤ ‖π‖ ^ 2 * ‖δ‖ * ‖L v‖ := by gcongr
        _ = (‖π‖ ^ 2 * ‖L v‖) * ‖δ‖ := by ring
        _ ≤ 1 * ‖δ‖ := by gcongr
        _ = _ := one_mul _
    rw [hΛ]
    refine forall_congr' fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have : P v k = (P v k - Q v k) + Q v k := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 k) h)
    · have : Q v k = -(P v k - Q v k) + P v k := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_neg]; exact h1 k) h)
  have hb' : ∀ v, Λ v → ‖π‖ * ‖L v‖ ≤ 1 := by
    intro v hv
    rw [← le_div_iff₀' hπp, pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [le_div_iff₀' hπp, ← norm_mul]
    exact hb v hv j
  by_cases hv : ‖π‖ ^ 2 * ‖L v‖ ≤ 1
  · exact key v hv
  have hv' := not_le.1 hv
  constructor
  · intro h
    have := hb' v h
    exfalso
    have h2 : ‖π‖ ^ 2 * ‖L v‖ = ‖π‖ * (‖π‖ * ‖L v‖) := by ring
    have h3 : ‖π‖ * (‖π‖ * ‖L v‖) ≤ ‖π‖ * 1 := by gcongr
    linarith
  · intro h
    exfalso
    have hne : Nonempty (Fin g) := by
      by_contra hh
      haveI := not_nonempty_iff.1 hh
      rw [Subsingleton.elim (L v) 0] at hv'
      simp at hv'
      linarith
    obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖L v j‖)
    have hj' : ‖L v‖ = ‖L v j‖ :=
      le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj) (norm_le_pi_norm _ _)
    have hc : ‖(π ^ 2 * L v j)⁻¹‖ = (‖π‖ ^ 2 * ‖L v‖)⁻¹ := by
      rw [norm_inv, norm_mul, norm_pow, hj']
    have hc1 : ‖(π ^ 2 * L v j)⁻¹‖ ≤ 1 := by
      rw [hc]; exact inv_le_one_of_one_le₀ hv'.le
    have hn : ‖π‖ ^ 2 * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖ = 1 := by
      have : L ((π ^ 2 * L v j)⁻¹ • v) = (π ^ 2 * L v j)⁻¹ • L v := funext fun k => hL _ _ _
      rw [this, norm_smul, hc, mul_left_comm]
      exact inv_mul_cancel₀ (by linarith)
    have hm := (key _ hn.le).2 (fun k => by
      rw [hP, norm_mul]
      calc _ ≤ 1 * ‖δ‖ := by gcongr; exact h k
        _ = _ := one_mul _)
    have := hb' _ hm
    have h2 : ‖π‖ ^ 2 * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖ = ‖π‖ * (‖π‖ * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖) := by ring
    have h3 : ‖π‖ * (‖π‖ * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖) ≤ ‖π‖ * 1 := by gcongr
    linarith

private theorem pr_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] (c : K) (y : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (c • y) a = c * pr Dw y a := by
  simp [pr]

private theorem pr_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] {g : ℕ} (b : (Fin g → K) →ₗ[K] K ⊗[ℤ] Dw.La) (v : Fin g → K) (a : Dw.La) :
    pr Dw (b v) a = ∑ j, pr Dw (b (Pi.single j 1)) a * v j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem eig_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] (σ : 𝓞 E →+* K) (c : K) (y : K ⊗[ℤ] Dw.La) (hy : IsEigL Dw σ y) :
    IsEigL Dw σ (c • y) := fun o => by
  rw [map_smul, hy o, smul_comm]
