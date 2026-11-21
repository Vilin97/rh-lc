module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

@[expose] public section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_chart_ideal_prime_and_saturated : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k), IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a → (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
  classical
  intro K _ ι _ Q p hQ hprime hp
  have hker := ker_theta Q hQ p hp
  refine ⟨?_, fun f a hf => ?_⟩
  · have : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (theta Q p)
    exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
  · let r := renR (Σ k, ι k)
    have hbind : ((theta Q p).comp (r.symm : _ →+* _)).comp
        (bind₁ (SncRes.lift p)).toRingHom = theta Q p := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change theta Q p (r.symm (bind₁ (SncRes.lift p) (C c))) = theta Q p (C c)
        have hc : r (C c) = C c := by simp [r, renR, renameEquiv_apply]
        rw [bind₁_C_right, ← hc, RingEquiv.symm_apply_apply]
      · intro q
        change theta Q p (r.symm (bind₁ (SncRes.lift p) (X q))) = theta Q p (X q)
        rw [bind₁_X_right, SncRes.lift]
        split_ifs with h
        · obtain ⟨k, i⟩ := q
          dsimp at h
          subst i
          have hx : phi Q (X ⟨k, p k⟩) ≠ 0 :=
            fun hz => hp k ((phi_eq_zero_iff Q _).1 hz)
          rw [map_one, map_one, theta_X, div_self hx]
        · have hX : X (Fintype.equivFin (Σ k, ι k) q) = r (X q) := by
            simp [r, renR, renameEquiv_apply]
          rw [hX, RingEquiv.symm_apply_apply]
    rw [SncRes.ideal, mem_map_renR_iff, ← hker, RingHom.mem_ker]
    change theta Q p (r.symm (bind₁ (SncRes.lift p) f)) = 0 ↔ f ∈ Q
    rw [show theta Q p (r.symm (bind₁ (SncRes.lift p) f)) = theta Q p f from
      DFunLike.congr_fun hbind f, theta_eq_zero_iff Q p hp hf]
