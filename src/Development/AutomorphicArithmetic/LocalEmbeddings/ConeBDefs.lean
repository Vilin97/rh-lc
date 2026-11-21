module

public import Mathlib

@[expose] public section

noncomputable section

namespace FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

open MeasureTheory

variable {ι : Type} [Fintype ι]

def ec (x : ι → ℂ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ w, x w).re : ℝ) : ℂ))

def FT (f : (ι → ℂ) → ℂ) (y : ι → ℂ) : ℂ := ∫ s, f s * ec (s * y)

def pr {n : ℕ} (v η : Fin n × ι → ℂ) : ι → ℂ := fun w => ∑ i, v (i, w) * η (i, w)

def sc {n : ℕ} (y : ι → ℂ) (η : Fin n × ι → ℂ) : Fin n × ι → ℂ := fun p => y p.2 * η p

theorem norm_ec (x : ι → ℂ) : ‖ec x‖ = 1 := by
  rw [ec, Complex.norm_exp]
  simp

theorem continuous_ec : Continuous (ec : (ι → ℂ) → ℂ) := by
  unfold ec
  fun_prop

omit [Fintype ι] in

end FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

end
