module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixPreservesForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralUnipotentTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairConverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionIsPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSmulLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem form_swap_herm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  unfold form
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

open GlobalTheory.AnisRatInv in
private theorem split_vec {n d₂ : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (H : Plane E n d₂)
    (hH : d₂ + 2 = n ∧ form σ J H.x H.x = 0 ∧ form σ J H.y H.y = 0 ∧ form σ J H.x H.y = 1 ∧
        (∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec)
    (r : Fin n → E) : ∃ (s t : E) (u : Fin d₂ → E), r = s • H.x + H.ι *ᵥ u + t • H.y := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := hH
  have hyx : form σ J H.y H.x = 1 := by rw [form_swap_herm J hσ hJ, hxy, map_one]
  let L : (E × E × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1 • H.x + H.ι *ᵥ p.2.2 + p.2.1 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t, u⟩ h
    change s • H.x + H.ι *ᵥ u + t • H.y = 0 at h
    have e1 := congrArg (fun z => form σ J z H.y) h
    have e2 := congrArg (fun z => form σ J z H.x) h
    simp only [form_add_left, form_smul_left, hxy, hyy, (horth u).2, (horth u).1, hxx, hyx] at e1 e2
    have hz : ∀ z : Fin n → E, form σ J 0 z = 0 := fun z => by unfold form; simp
    rw [hz] at e1 e2
    have hs : s = 0 := by simpa using e1
    have ht : t = 0 := by simpa using e2
    subst hs ht
    simp only [zero_smul, zero_add, add_zero] at h
    have hu : u = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    subst hu; rfl
  have hdim : Module.finrank E (E × E × (Fin d₂ → E)) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, ← hn]; ring
  have hS : Function.Surjective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL
  obtain ⟨⟨s, t, u⟩, hp⟩ := hS r
  exact ⟨s, t, u, hp.symm⟩

private theorem rho_om {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (u : UA σ X.J) (y : Fin n → AE F E)
    (w : Fin d → AE F E) (Ψ : Fn F n d) (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (Matrix.vecMulVec y w) (om (u, 1) Ψ) =
      om (u, 1) (M.co.rho B.ψ (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) Ψ) := by
  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) Ψ hΨ
  have h1 : mat u * mat u⁻¹ = 1 := Units.mul_inv u.1
  have hact : actAB (cA σ) (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ y) w) = Matrix.vecMulVec y w := by
    show mat u * _ * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [hact] at himpl
  exact himpl.symm

open GlobalTheory.AnisRatInv in

end

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
