module

public import Mathlib

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold Pointwise

namespace GlobalTheory.Hk

theorem conj_mem_lev {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)}
    (hσ : (σ 1 0 : ZMod (N * l)) = 0 ∧ (σ 1 1 : ZMod N) = d) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 N ⊓ Gamma0 l) : σ * γ * σ⁻¹ ∈ Gamma1 N ⊓ Gamma0 l := by
  obtain ⟨h1, -⟩ := hσ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  have hN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) h1)
  have hl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) h1)
  obtain ⟨hg1, hg0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at hg1
  obtain ⟨hx, hw, hz⟩ := hg1
  rw [Gamma0_mem] at hg0
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdN := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at hdN
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    rw [hN, hx, hw, hz] at *
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdN
    · linear_combination hdN
    · ring
  · rw [Gamma0_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    rw [hl, hg0]
    ring

end GlobalTheory.Hk

namespace GlobalTheory.Hk


theorem dia_cuspForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N →
    (σ 1 0 : ZMod (N * l)) = 0 ∧ (σ 1 1 : ZMod N) = d →
    ∀ f : CuspForm (Gamma1 N ⊓ Gamma0 l : Subgroup SL(2, ℤ)) k,
    ∃ g : CuspForm (Gamma1 N ⊓ Gamma0 l : Subgroup SL(2, ℤ)) k, ⇑g = ⇑f ∣[k] σ := by
  intro N l k d σ _ hσ f
  let Γ : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l
  have hle : ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ) •
      (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv] at hy
    obtain ⟨γ, hγ, hγe⟩ := hy
    refine ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, ?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ (σ * γ * σ⁻¹) = y
    rw [map_mul, map_mul, map_inv, hγe]
    group
  refine ⟨{ toFun := ⇑f ∣[k] σ
            slash_action_eq' := fun A hA => ?_
            holo' := ?_
            zero_at_cusps' := fun {x} hx => ?_ }, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := hA
    have h : (f : ℍ → ℂ) ∣[k] (σ * γ * σ⁻¹) = f :=
      f.slash_action_eq' _ ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, rfl⟩
    show ((f : ℍ → ℂ) ∣[k] σ) ∣[k] γ = (f : ℍ → ℂ) ∣[k] σ
    rw [← SlashAction.slash_mul]
    have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
    rw [e, SlashAction.slash_mul, h]
  · exact MDifferentiable.slash f.holo' _ _
  · have h3 : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • x) (Γ : Subgroup (GL (Fin 2) ℝ)) :=
      (hx.smul _).mono hle
    show x.IsZeroAt ((f : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ) k
    exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3)

end GlobalTheory.Hk
