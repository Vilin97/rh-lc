module

public import Mathlib
public import Development.AutomorphicArithmetic.DivisorFrames.CompactAdeleNormBounded
public import Development.AutomorphicArithmetic.DivisorFrames.SkewUnitaryReductionTheory
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLeviClosureMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

section
open GlobalTheory.LeviDecomp GlobalTheory.StabCosetDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hNN : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hN : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) :=
    ⟨⟨_, _, hNN, hNN⟩, rfl⟩
  have h1 := Matrix.rank_of_isUnit _ hN
  have h2 : (Aᵀ * M * A.map star).rank ≤ M.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hA, h1] at h2
  simp only [Fintype.card_sum, Fintype.card_fin, hrs] at h2
  have h3 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := M.rank_le_width
    simp only [Matrix.rank, Fintype.card_fin] at h2 this
    rw [Module.finrank_fin_fun]; omega
  have hu : IsUnit M := (Matrix.mulVec_surjective_iff_isUnit).mp (LinearMap.range_eq_top.mp h3)
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

private theorem det_ne_zero_skew {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [Matrix.det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm,
    h0, map_zero, mul_zero]

private theorem bdd {X ι : Type} [TopologicalSpace X] [Finite ι] {K : Set X} (hK : IsCompact K) (f : ι → X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hf : ∀ i, Continuous (f i)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ K, ∀ i, ∀ ξ : E, ξ ≠ 0 → ∀ u : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, inclR (F := F) (AF F) ξ * u.1 = f i p →
      (absE F E u : ℝ) ≤ c := by
  obtain ⟨c, hc⟩ := UpperTheory.compact_adele_norm_bounded F E (⋃ i, f i '' K) (isCompact_iUnion fun i => hK.image (hf i))
  refine ⟨max c 0, le_max_right _ _, fun p hp i ξ hξ u hu => le_trans ?_ (le_max_left _ _)⟩
  have h := hc (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 ξ hξ) * u)
    (Set.mem_iUnion.2 ⟨i, p, hp, hu.symm⟩)
  rwa [map_mul, GlobalTheory.Doubling.absE_inclR, one_mul] at h

private theorem incV_mulVec {n k : ℕ} (g : Matrix (Fin n) (Fin k) E) (x : Fin k → E) :
    incV F (g *ᵥ x) = incM F g *ᵥ incV F x :=
  funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) g x i

private theorem rat_act {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ g : Matrix (Fin n) (Fin n) E, (∀ x, incV F (g *ᵥ x) = mat γ *ᵥ incV F x) ∧ ∀ x y, g *ᵥ x = g *ᵥ y → x = y := by
  obtain ⟨g, hg, -⟩ := rat_desc γ hγ
  have h1 : ∀ x, incV F (g *ᵥ x) = mat γ *ᵥ incV F x := fun x => by rw [incV_mulVec, hg]; rfl
  exact ⟨g, h1, fun x y h => eq_of_mulVec γ (h1 x).symm (by rw [h, h1])⟩

private theorem exists_minor {n : ℕ} {v v' : Fin n → E} (hv : v ≠ 0) (h : ∀ c : E, v' ≠ c • v) :
    ∃ j l, v j * v' l - v l * v' j ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  have hj' : v j ≠ 0 := hj
  refine h (v' j / v j) (funext fun l => ?_)
  have := hc j l
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

private theorem indep {B : Base F E} {d d₁ r₁ s₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hW₁ : W₁.IsSkew σ B r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {z : Fin d₁ → E} (hz : z ≠ 0) (c : E) :
    H'.ι *ᵥ z ≠ c • H'.x := by
  intro h
  have h1 := (hH.orth z).2
  have h2 := hH.xy
  unfold form at h1 h2
  rw [h, smul_dotProduct, h2, smul_eq_mul, mul_one] at h1
  rw [h1, zero_smul] at h
  apply hz
  refine Matrix.eq_zero_of_vecMul_eq_zero (det_ne_zero_skew hW₁) ?_
  rw [← hH.gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, h, Matrix.zero_vecMul,
    Matrix.zero_vecMul]

end

