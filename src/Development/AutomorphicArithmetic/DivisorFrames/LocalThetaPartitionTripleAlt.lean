import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section SlopeTestRemainingChoices

open scoped Classical
open GlobalTheory.VanishLoc (liftT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

private theorem rho_rho' {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  simp only [Darboux.rho]
  rw [schr_schr', map_add]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

omit [NumberField E] in
private theorem formA_inc {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  have h : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl
  simp [incV, incM, form, Matrix.mulVec, dotProduct, h]

private theorem coef_eq {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (a t : AE F E) (u : Fin n₁ → AE F E) :
    cA σ (incV F H.x ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i))) = t := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hc : ∀ z : AE F E, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsym : ∀ x y : Fin n → E, form σ X.J y x = σ (form σ X.J x y) := fun x y => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hS.herm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : incM F H.ι *ᵥ u = ∑ j, u j • incV F (H.ι *ᵥ Pi.single j 1) := by
    funext i
    simp [incV, incM, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have e : (fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i)) =
      cA σ a • (fun i => cA σ (incV F H.x i)) + ∑ j, cA σ (u j) • (fun i => cA σ (incV F (H.ι *ᵥ Pi.single j 1) i)) +
        cA σ t • fun i => cA σ (incV F H.y i) := by
    funext i
    simp only [hu, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_add, map_mul, map_sum]
  have h0 : ∀ v, form σ X.J H.x (H.ι *ᵥ v) = 0 := fun v => by rw [hsym, (hA.orth v).1, map_zero]
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul,
    formA_inc, hA.xx, hA.xy, h0, map_zero, map_one, smul_zero, Finset.sum_const_zero, zero_add, smul_eq_mul, mul_one, mul_zero, hc]

omit [NumberField E] in

private theorem partFin_vec {n d : ℕ} (v : Pl F) (a : Fin n → AE F E) (w : Fin d → AE F E) :
    partFin v (Matrix.vecMulVec a w) = Matrix.vecMulVec (GlobalTheory.LatVac.liftV v 1 • a) w := by
  rw [partFin, Matrix.smul_vecMulVec]

private theorem rho_add {B : Base F E} {n d d₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
    (M : Model σ X W) {H' : Plane E d d₁} (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hψ : IsStd B.ψ) (v : Pl F)
    (a b : Fin n → AE F E) {f : (Fin n × Fin d → Fv F v) → ℂ} (hf : f ∈ SB (Fin n × Fin d → Fv F v)) :
    locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec a (incV F H'.x))))
      (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f) =
    locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec (a + b) (incV F H'.x)))) f := by
  have a1 := (locOp_rho M.co hψ.1 v (Matrix.vecMulVec b (incV F H'.x)) hf).1
  have a2 := (locOp_rho M.co hψ.1 v (Matrix.vecMulVec a (incV F H'.x))
    (locOp_mem v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f)).1
  refine (locOp_eq hf (locOp_mem _ _ _) fun r hr => ?_).symm
  have hr' : Rest (evFin F v) (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f) r :=
    ⟨hr.1, by rw [← a1 r hr]; exact GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hr.2⟩
  rw [← a2 r hr', ← a1 r hr, rho_rho']
  · rw [Matrix.add_vecMulVec, partFin, partFin, partFin, smul_add]
  · rw [partFin_vec, partFin_vec, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul]
    exact GlobalTheory.ArchUniq.Coord.sympM_eq_zero _ _ (GlobalTheory.ArchUniq.Coord.gram_xx hH') _ _

end SlopeTestRemainingChoices
