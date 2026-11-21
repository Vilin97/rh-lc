module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.CartanUnit

variable {n : ℕ}

theorem star_mulVec_map (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : star (A *ᵥ x) = A.map star *ᵥ star x := by
  funext i
  simp [Matrix.mulVec, dotProduct, star_sum]

theorem mulVec_dot (A : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem mul_star_eq_one_of_cartan {M θ k : Matrix (Fin n) (Fin n) ℂ} (hC : IsCartan M θ) (hk : kᵀ * M * k.map star = M)
    (hc : Commute k θ) {x : Fin n → ℂ} (hx : x ≠ 0) {c : ℂ} (hkx : k *ᵥ x = c • x) : c * star c = 1 := by
  have hpos := hC.2.2 x hx
  have hP : (θ *ᵥ x) ⬝ᵥ M *ᵥ star x ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  have h1 : (θ *ᵥ (k *ᵥ x)) ⬝ᵥ M *ᵥ star (k *ᵥ x) = (θ *ᵥ x) ⬝ᵥ M *ᵥ star x := by
    rw [Matrix.mulVec_mulVec, ← hc.eq, ← Matrix.mulVec_mulVec, star_mulVec_map, mulVec_dot, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hk]
  have h2 : (θ *ᵥ (k *ᵥ x)) ⬝ᵥ M *ᵥ star (k *ᵥ x) = c * star c * ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
    rw [hkx, Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have h3 : (c * star c - 1) * ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) = 0 := by rw [sub_mul, ← h2, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hP)

end GlobalTheory.ThK.CartanUnit

namespace GlobalTheory.ThK

end GlobalTheory.ThK
