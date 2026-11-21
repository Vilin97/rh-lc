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
  exact ⟨GlobalTheory.T.adapted_plane_complement_skew_hermitian F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH, GlobalTheory.T.adapted_plane_complement_signature F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP,
    GlobalTheory.T.adapted_plane_complement_lattice F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP, GlobalTheory.T.adapted_plane_complement_dual_lattice F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH,
    GlobalTheory.T.adapted_plane_complement_cartan F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP, GlobalTheory.T.adapted_plane_complement_split_basis F E σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH⟩

end GlobalTheory.ThK.KernelZero

end
