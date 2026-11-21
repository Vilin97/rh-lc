module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
public import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTripleAlt
public import Development.AutomorphicArithmetic.DivisorFrames.UnitaryStabilizerLiftsToSmallerSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerArchimedean
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisHermitianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisHermitianUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchAStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMapStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) : co.rho ψ 0 Φ = Φ := by
  funext z
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

private theorem sigR_sigR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    show a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

private theorem atV_incV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : Pl F) (x : Fin n → E) (i : Fin n) : atV v (incV F x) i = inclR (F := F) (Fv F v) (x i) := by
  change evFin F v 1 ⊗ₜ[F] x i = (1 : Fv F v) ⊗ₜ[F] x i
  rw [map_one]

private theorem pair_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y : Fin n → E)
    (hxy : form σ J x y = 1) (c : AE F E) (a : Fv F v ⊗[F] E) :
    pairV σ J v (atV v (c • incV F x)) (fun i => sigR (Fv F v) σ a * atV v (incV F y) i) = compFin F E v c * a := by
  have h1 : ∀ i, atV v (c • incV F x) i = compFin F E v c * inclR (F := F) (Fv F v) (x i) := fun i => by
    rw [← atV_incV]
    simp only [atV, Pi.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ e : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := fun _ => rfl
  have h3 := congrArg (inclR (F := F) (Fv F v)) hxy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_one] at h3
  simp only [pairV, dotProduct, Matrix.mulVec, h1, map_mul, sigR_sigR' _ hσ, atV_incV, h2, Matrix.map_apply]
  rw [← mul_one (compFin F E v c * a), ← h3]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem acts_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}
    {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ : (κ → Fv F v) → ℂ} (c : ℂ) (h : Acts (evFin F v) T φ φ₁) :
    Acts (evFin F v) (fun Ψ => c • T Ψ) φ (c • φ₁) := by
  intro r hr
  show c • T _ = _
  rw [h r hr]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
