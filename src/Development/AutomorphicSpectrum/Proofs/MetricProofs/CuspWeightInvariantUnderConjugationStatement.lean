module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugation
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open LevelTowerAlt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ _
  let σ' : Ψ → (𝓞 E →+* ℂ) := fun τ => (starRingEnd ℂ).comp (σ τ)
  have weight_eq (S : RiemLat E g Λ)
      (hIso : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub S.form I ↔ IsIsoSub R.form I)
      (hGram : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → ∀ τ, ∀ v ∈ I, ∀ w ∈ I,
        S.ip (proj S.B (σ' τ) (S.P v)) (proj S.B (σ' τ) (S.P w)) =
          (starRingEnd ℂ) (R.ip (proj R.B (σ τ) (R.P v)) (proj R.B (σ τ) (R.P w)))) :
      S.cuspW σ' = R.cuspW σ := by
    have nz_eq (I : Submodule (𝓞 E) Λ) (hI : IsIsoSub R.form I) :
        S.nz σ' I = R.nz σ I := by
      unfold RiemLat.nz
      split_ifs with h
      · let v := h.choose_spec.choose
        have hv := h.choose_spec.choose_spec.2.1
        unfold RiemLat.nzOf
        congr 1
        refine Finset.prod_congr rfl fun τ _ => ?_
        have hMatrix : (S.gram fun a => eigComp S.B (σ' τ) (S.P (v a))) =
            (starRingEnd ℂ).mapMatrix (R.gram fun a => eigComp R.B (σ τ) (R.P (v a))) := by
          ext a b
          simp only [RiemLat.gram, eigComp_eq, RingHom.mapMatrix_apply, Matrix.map_apply,
            Matrix.of_apply]
          exact hGram I hI τ _ (hv a) _ (hv b)
        rw [hMatrix, ← RingHom.map_det, Complex.conj_re]
      · rfl
    unfold RiemLat.cuspW RiemLat.IsCusp
    congr 2
    ext x
    constructor
    · rintro ⟨I, ⟨hne, hsat, hiso⟩, rfl⟩
      exact ⟨I, ⟨hne, hsat, (hIso I).mp hiso⟩, by rw [nz_eq I ((hIso I).mp hiso)]⟩
    · rintro ⟨I, ⟨hne, hsat, hiso⟩, rfl⟩
      exact ⟨I, ⟨hne, hsat, (hIso I).mpr hiso⟩, by rw [nz_eq I hiso]⟩
  have proj_conj (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
      proj (conjB R.B) ((starRingEnd ℂ).comp s) (star x) = star (proj R.B s x) := by
    rw [proj_apply, proj_apply, star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjB_star, star_smul, coef_conj]
    rfl
  refine ⟨weight_eq R (fun _ => Iff.rfl) ?_,
    conjLat R, fun _ => rfl, rfl, conjB_star R.B, weight_eq (conjLat R) ?_ ?_⟩
  · intro I hI τ v hv w hw
    exact gram_conj R hI (σ τ) hv hw
  · intro I
    exact forall₄_congr fun v _ w _ => neg_eq_zero
  · intro I _ τ v _ w _
    exact (congrArg₂ (conjLat R).ip (proj_conj (σ τ) (R.P v))
      (proj_conj (σ τ) (R.P w))).trans (conjLat_ip R _ _)
