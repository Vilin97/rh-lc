import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_open_sub (v : Pl F) (n : ℕ) (U : Set (Fin n → Fv F v ⊗[F] E)) (hU : U ∈ 𝓝 0) :
    ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) ∧ ∀ y ∈ L, y ∈ U := by
  let c := GlobalTheory.LocTateInt.coordEv (F := F) (E := E) v
  let f : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    { toFun := fun y i => c (y i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have hf : Continuous f := continuous_pi fun i => c.continuous.comp (continuous_apply i)
  let g : (Fin n → Fin (Module.finrank F E) → Fv F v) → (Fin n → Fv F v ⊗[F] E) := fun z i => c.symm (z i)
  have hg : Continuous g := continuous_pi fun i => c.symm.continuous.comp (continuous_apply i)
  have g0 : g 0 = 0 := by funext i; simp [g]
  have hU' : g ⁻¹' U ∈ 𝓝 0 := hg.continuousAt.preimage_mem_nhds (by rwa [g0])
  haveI : NonarchimedeanAddGroup (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    IsUltrametricDist.nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU'
  refine ⟨V.toAddSubgroup.comap f, V.isOpen.preimage hf, fun y hy => ?_⟩
  have h : g (f y) ∈ U := hV hy
  have e : g (f y) = y := by funext i; simp [g, f]
  rwa [e] at h

private theorem sigR_smul (σ : E →ₐ[F] E) (v : Pl F) (a : Fv F v) (t : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (a • t) = a • sigR (Fv F v) σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

private noncomputable def locY {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (H' : Plane E d d₁) (v : Pl F) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun y := GlobalTheory.LatVac.locCo M.co v (yAt H' v y)
  map_add' s t := by
    rw [← map_add (f := _)]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]
  map_smul' a t := by
    rw [RingHom.id_apply, ← GlobalTheory.VanishLocCont.locCo_smul]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, GlobalTheory.VanishLocCont.liftT_smul,
      smul_mul_assoc]

private noncomputable def trY (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F)
    (x : Fin n → Fv F v ⊗[F] E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v where
  toFun y := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)
  map_add' s t := by rw [pairV_add_right, map_add (f := _)]
  map_smul' a t := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    have e : (fun i => sigR (Fv F v) σ ((a • t) i)) = a • fun i => sigR (Fv F v) σ (t i) :=
      funext fun i => sigR_smul σ v a (t i)
    rw [pairV, pairV, e, Matrix.mulVec_smul, dotProduct_smul]

end
