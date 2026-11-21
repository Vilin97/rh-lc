module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_open_sub (v : Pl (F := F)) (n : ℕ) (U : Set (Fin n → Fv F v ⊗[F] E)) (hU : U ∈ 𝓝 0) :
    ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) ∧ ∀ y ∈ L, y ∈ U := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  let c := ((Module.finBasis F E).baseChange (Fv F v)).equivFun
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
  let f : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    { toFun := fun y i => c (y i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have hf : Continuous f := continuous_pi fun i => hc.comp (continuous_apply i)
  let g : (Fin n → Fin (Module.finrank F E) → Fv F v) → (Fin n → Fv F v ⊗[F] E) := fun z i => c.symm (z i)
  have hg : Continuous g := continuous_pi fun i => hc'.comp (continuous_apply i)
  have g0 : g 0 = 0 := by funext i; simp [g]
  have hU' : g ⁻¹' U ∈ 𝓝 0 := hg.continuousAt.preimage_mem_nhds (by rwa [g0])
  have : NonarchimedeanAddGroup (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    IsUltrametricDist.nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU'
  refine ⟨V.toAddSubgroup.comap f, V.isOpen.preimage hf, fun y hy => ?_⟩
  have h : g (f y) ∈ U := hV hy
  have e : g (f y) = y := by funext i; simp [g, f]
  rwa [e] at h

private theorem sigR_smul (σ : E →ₐ[F] E) (v : Pl (F := F)) (a : Fv F v) (t : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (a • t) = a • sigR (Fv F v) σ t := by
  induction t using TensorProduct.inductionOn with
  | tmul b e => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

private noncomputable def locY {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (H' : Plane E d d₁) (v : Pl (F := F)) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun y := GlobalTheory.LatVac.locCo M.co v (yAt H' v y)
  map_add' s t := by
    rw [← map_add (f := _)]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]
  map_smul' a t := by
    have hCo : GlobalTheory.LatVac.locCo M.co v (GlobalTheory.LatVac.liftV v a • yAt H' v t) =
        a • GlobalTheory.LatVac.locCo M.co v (yAt H' v t) := by
      simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul,
        Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul,
        GlobalTheory.LatVac.evFin_liftV]
      rfl
    rw [RingHom.id_apply, ← hCo]
    have hLift (x : Fv F v ⊗[F] E) :
        GlobalTheory.VanishLoc.liftT v (a • x) =
          GlobalTheory.LatVac.liftV v a • GlobalTheory.VanishLoc.liftT v x := by
      induction x using TensorProduct.inductionOn with
      | tmul b e =>
        have hMul : GlobalTheory.LatVac.liftV v (a * b) =
            GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b :=
          Prod.ext (mul_zero _).symm (GlobalTheory.AdelicU.singleFin_mul v a b)
        rw [TensorProduct.smul_tmul', GlobalTheory.VanishLoc.liftT, LinearMap.rTensor_tmul,
          LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hMul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, hLift, smul_mul_assoc]

private noncomputable def trY (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F))
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
