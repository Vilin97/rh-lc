import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.InstMeasurableSpaceU2
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfForallIntegralCoeff

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace PW

open Matrix MeasureTheory Complex Finset Polynomial

variable (g : U2 → ℂ)

variable {g}

set_option synthInstance.maxHeartbeats 400000 in

theorem eq_zero_of_forall_integral_coeff {g : U2 → ℂ} (hg : Continuous g)
    (h : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2), ∫ k, ((((l₁ * k * l₂ : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n *
      ((k : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * g k) ∂μK = 0) : g = 0 :=
  _root_.UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff hg h

end PW

end GroundTheory.Automorphic.ArchWhittakerC
