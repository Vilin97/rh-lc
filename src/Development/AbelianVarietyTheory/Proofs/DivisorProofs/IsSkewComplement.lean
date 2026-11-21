module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLeftInverseExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSkewHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementCartanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasisStatement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.KernelZero

theorem isSkew_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → W₁.IsSkew σ B (r - 1) (s - 1) := by
  intro F E _ _ _ _ _ σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH
  obtain ⟨P, hP⟩ := GlobalTheory.T.adapted_plane_left_inverse_exists F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH
  have hLat : W₁.L.IsLattice E :=
    GlobalTheory.T.adapted_plane_complement_lattice F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP
  have hFull : W₁.L.IsFullLattice E := by
    refine { toIsLattice := hLat, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro u _
    have hu : H.ι *ᵥ u ∈ Submodule.span E (W.L : Set (Fin n → E)) := by
      rw [hW.lat.span_eq_top]
      trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (𝓞 E)) E _ (H.ι *ᵥ u) hu
    rw [Submodule.span_eq] at ht
    change (t : 𝓞 E) • (H.ι *ᵥ u) ∈ W.L at ht
    have hmem : (t : 𝓞 E) • u ∈ W₁.L := by
      rw [hH.low]
      change ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) ((t : 𝓞 E) • u) ∈ W.L
      rw [map_smul]
      exact ht
    have ht0 : algebraMap (𝓞 E) E t ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 E) E).ne (nonZeroDivisors.coe_ne_zero t)
    have hspan : (t : 𝓞 E) • u ∈ Submodule.span E (W₁.L : Set (Fin n₁ → E)) := Submodule.subset_span hmem
    have hspan' : (algebraMap (𝓞 E) E t) • u ∈ Submodule.span E (W₁.L : Set (Fin n₁ → E)) := by
      rw [IsScalarTower.algebraMap_smul]
      exact hspan
    have := (Submodule.span E (W₁.L : Set (Fin n₁ → E))).smul_mem
      (algebraMap (𝓞 E) E t)⁻¹ hspan'
    simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using this
  exact ⟨GlobalTheory.T.adapted_plane_complement_skew_hermitian F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH, GlobalTheory.T.adapted_plane_complement_signature F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP,
    hFull, GlobalTheory.T.adapted_plane_complement_dual_lattice F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH,
    GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP, GlobalTheory.T.adapted_plane_complement_split_basis F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH⟩

end GlobalTheory.ThK.KernelZero

end
