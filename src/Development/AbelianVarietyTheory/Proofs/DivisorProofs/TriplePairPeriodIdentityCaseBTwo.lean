import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTripleAlt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsCompactSubgroupCharacter
import Development.AutomorphicArithmetic.DivisorFrames.ThetaLocalOpenSubgroup
import Development.AutomorphicArithmetic.DivisorFrames.FiniteUnitContractions
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AutomorphicArithmetic.DivisorFrames.LocalPartEvaluationConfigTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

section SlopeTestRemainingChoices

open GlobalTheory.ConeBumpB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
  {ψ : AddChar (Fv F v) ℂ} [MeasurableSpace (Fv F v ⊗[F] E)] {m : Measure (Fv F v ⊗[F] E)}

omit [NumberField E] in
private theorem four_mod (T : Fv F v ⊗[F] E → ℂ) (c t : Fv F v ⊗[F] E) :
    four v ψ m (fun s => ψ (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * s)) * T s) t = four v ψ m T (t - c) := by
  refine congrArg (integral m) (funext fun s => ?_)
  rw [sub_mul, map_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

omit [NumberField E] in

variable [BorelSpace (Fv F v ⊗[F] E)] [m.IsAddHaarMeasure]

end SlopeTestRemainingChoices

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

private theorem det_ne_zero_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm, h0, map_zero]

open GlobalTheory.ConeBumpB GlobalTheory.LatVac in
open GlobalTheory.Doubling (absE) in
open scoped GlobalTheory.VacAny in
