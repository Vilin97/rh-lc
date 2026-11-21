import Mathlib
open NumberField

noncomputable section
namespace GlobalTheory

theorem norm_ratCast_padicComplex (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ‖(q : ℂ_[p])‖ = padicNorm p q := by
  have h := PadicComplex.norm_extends' p (q : ℚ_[p])
  rw [Padic.eq_padicNorm] at h
  rw [← h]
  congr 1
  rw [map_ratCast]
  exact (map_ratCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) q).symm

end GlobalTheory
