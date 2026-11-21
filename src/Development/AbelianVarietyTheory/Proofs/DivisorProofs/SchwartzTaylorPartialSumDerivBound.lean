module

public import Mathlib

@[expose] public section

open SchwartzMap Filter Topology
open scoped Nat

namespace GlobalTheory

theorem norm_iteratedFDeriv_diag_le {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) F)
    (a : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ a (fun y => f (fun _ => y)) x‖ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖x‖ ^ (j - a) := by
  set L : V →L[ℝ] (Fin j → V) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ V) with hL
  have hLn : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_pi_le_of_le (fun _ => ContinuousLinearMap.norm_id_le) zero_le_one
  have hfun : (fun y => f (fun _ => y)) = (⇑f) ∘ ⇑L := rfl
  rw [hfun, L.iteratedFDeriv_comp_right (f.contDiff (n := ⊤)) x (by exact_mod_cast le_top)]
  have hLx : ‖L x‖ ≤ ‖x‖ := by
    have := L.le_opNorm x
    nlinarith [norm_nonneg x]
  calc ‖(iteratedFDeriv ℝ a (⇑f) (L x)).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ a (⇑f) (L x)‖ * ∏ _i : Fin a, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ a (⇑f) (L x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    _ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖L x‖ ^ (j - a) := by
        rw [mul_one]
        have := f.norm_iteratedFDeriv_le a (L x)
        simpa using this
    _ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖x‖ ^ (j - a) := by
        gcongr

end GlobalTheory
