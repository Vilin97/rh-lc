import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairThetaIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) (x y : U) :
    co.rho ψ (x + y) Φ = ψ (-(⅟(2 : R) * B x y)) • co.rho ψ x (co.rho ψ y Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_schr', ← co.form, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul,
    map_add]

private theorem hTens_vmv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (p p' : α → A) (q q' : β → A) :
    hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q') =
      (p ⬝ᵥ JA *ᵥ fun k => c (p' k)) * (q ⬝ᵥ JB *ᵥ fun l => c (q' l)) := by
  calc hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q')
      = ∑ i, ∑ j, ∑ k, ∑ l, (p i * JA i k * c (p' k)) * (q j * JB j l * c (q' l)) := by
        simp only [hTens, Matrix.vecMulVec_apply, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [dotProduct, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem symp_vmv (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (p q : Fin n → AE F E) (w : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW) (Matrix.vecMulVec p w) (Matrix.vecMulVec q w) =
      -Algebra.trace (AF F) (AE F E) (fA σ J p q * GlobalTheory.UnipMass.hA σ JW w w) := by
  rw [symp, hTens_vmv, neg_one_mul, map_neg]
  rfl

end
