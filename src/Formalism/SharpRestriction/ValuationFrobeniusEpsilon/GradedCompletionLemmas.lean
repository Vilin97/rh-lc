import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

noncomputable section

namespace Formalism.MainNotions.UnusedSlot38
open Formalism.BasicNotions.V1 IsLocalRing MvPowerSeries Filter
open scoped Classical

open MvPowerSeries IsLocalRing Filter

section Graded

variable {O : Type} [CommRing O] {a rk : ℕ} (wt : Fin a → (Fin rk → ℤ))

def monoWt (m : Fin a →₀ ℕ) : Fin rk → ℤ := m.sum fun i e => (e : ℤ) • wt i

variable (O) in

variable (O) in

variable (O) in

def comp (j : Fin rk → ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  fun m => if monoWt wt m = j then coeff m f else 0

variable (Jh : Ideal (MvPowerSeries (Fin a) O))

end Graded

section Coh

variable {k : Type} [Field k] {n : ℕ}

end Coh

section Fib

variable (P : LiftProb)

variable {P}

variable (act : P.Gam → MM P →ₗ[kk P] MM P)

variable {act}

variable (act)

variable (N : Submodule (kk P) (MM P)) (localization₂ : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop)

end Fib

section Numbers

variable (P : LiftProb)

end Numbers

section Prob

variable (P : LiftProb)

variable {P}

variable (P)

end Prob

section Lit

variable (P : LiftProb)

variable {P}

section Grp

variable {H : Type} [Group H] [TopologicalSpace H] (ι : H →* P.Gam) (S : Set P.Gam)
  (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P))

end Grp

variable (P)

end Lit

end Formalism.MainNotions.UnusedSlot38
