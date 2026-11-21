module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.SubstDiff in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero :
    ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
      [Algebra B Q] (θ : B →+* O), IsFrame p Q θ →
      ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q)
        (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) →
        DIn N (MvPowerSeries.subst (QLog.up (Q := Q) u) f) ∧
          (In N f → In N (MvPowerSeries.subst (QLog.up (Q := Q) u) f)) := by
  intro p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu
  let NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N
  have memNQ (q : Q) : q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b := by
    change (∃ b ∈ N, algebraMap B Q b = q) ↔ _
    simp only [eq_comm (a := q)]
  have ha : HasSubst (QLog.up (Q := Q) u) :=
    hasSubst_of_constantCoeff_zero fun i => by
      rw [QLog.up, constantCoeff_map, hu i, map_zero]
  have hprod (d : σ →₀ ℕ) : (d.prod fun i n => QLog.up (Q := Q) u i ^ n) =
      map (algebraMap B Q) (∏ i, u i ^ d i) := by
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp only [QLog.up, map_pow]
  have hcoeff (e : τ →₀ ℕ) : coeff e (MvPowerSeries.subst (QLog.up (Q := Q) u) f) =
      ∑ d ∈ (coeff_subst_finite ha f e).toFinset,
        algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f := by
    rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod, coeff_map, smul_eq_mul, mul_comm]
  refine ⟨fun e j => ?_, fun hI e => ?_⟩
  · rw [← memNQ, hcoeff, Finset.mul_sum]
    refine NQ.sum_mem fun d _ => ?_
    have h := smul_mem_of_mem_span NQ (fun i => d i) (coeff d f)
      (fun i => (memNQ _).2 (hD d i)) _ (euler_prod_mem j u (fun i => d i) Finset.univ) e
    convert h using 1
    rw [coeff_euler, Algebra.smul_def, map_mul, map_natCast]
    ring
  · rw [← memNQ, hcoeff]
    refine NQ.sum_mem fun d _ => ?_
    rw [← Algebra.smul_def]
    exact NQ.smul_mem _ ((memNQ _).2 (hI d))
