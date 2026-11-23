module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  first | exact @GlobalTheory.RowLocVec.cosVec_isLocVec | exact GlobalTheory.RowLocVec.cosVec_isLocVec | (intros; apply GlobalTheory.RowLocVec.cosVec_isLocVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) := by
  first | exact @GlobalTheory.RowTheta.rowDatum_isThetaFunO | exact GlobalTheory.RowTheta.rowDatum_isThetaFunO | (intros; apply GlobalTheory.RowTheta.rowDatum_isThetaFunO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  first | exact @GlobalTheory.HaarNorm.vol_nu_eq_of_isAt | exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt | (intros; apply GlobalTheory.HaarNorm.vol_nu_eq_of_isAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalTheta

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowStart

theorem setIntegral_fd_eq {D : D7} (V : HSp D) (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA D V))
    (h1 : IsFundamentalDomain (GQ V) 𝓕 μ) (h2 : IsFundamentalDomain (GQ V) 𝓕' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : ∫ g in 𝓕, f g ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI := hμ
  exact h1.setIntegral_eq h2 fun γ g => by
    simp only [Subgroup.smul_def, smul_eq_mul]
    exact hf γ γ.2 g

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem IsCuspListed.left {θ : InfFam D} {X : Node} {F : Fn G X} (h : IsCuspListed θ X F) :
    ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g := h.1.toIsAutFun.left

theorem measEq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation

theorem kerA_right_rat (W : G.Weil) {i : ℕ} (hi : i < D.R.m) {f : Sch G (.right i 0)}
    (hf : IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) f) :
    ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g h, W.kerA (.right i 0) f (γ * g) h = W.kerA (.right i 0) f g h := by
  intro γ hγ g h
  have H := (GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ (W.om (.chi i 0))
    (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩) f hf).2 1 (Subgroup.one_mem _) γ hγ (negGA _ h) g
  rw [one_mul] at H
  exact H

theorem liftA_right_eq (W : G.Weil) (M M' : Vol G) {i : ℕ} {K : Subgroup (GL (Fin (G.V (.grid i 0)).rank) (Lev.EAf D))}
    (h : M.IsAt (.grid i 0) K) (h' : M'.IsAt (.grid i 0) K) (f : Sch G (.right i 0)) (F : Fn G (.grid i 0))
    (hinv : ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g x, W.kerA (.right i 0) f (γ * g) x * F (γ * g) = W.kerA (.right i 0) f g x * F g) :
    liftA W M (.right i 0) f F = liftA W M' (.right i 0) f F := by
  funext x
  have e := measEq M M' _ _ h h'
  rw [liftA_apply, liftA_apply]
  have h1 := h.haar_fund
  have h2 := h'.haar_fund
  simp only [Arrow.src] at h1 h2 e ⊢
  rw [e] at h1 ⊢
  exact setIntegral_fd_eq _ _ h2.1 _ _ h1.2 h2.2 _ fun γ hγ g => hinv γ hγ g x

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowCore (W : G.Weil) (M₀ M : Vol G) (ρm : RealMatch W) (t : T) (ρ : G.RealVec) (Φ : G.Datum)
    (hstep : CuspStep W M ρm t)
    (hloc : ∀ (i : Fin D.R.m) (κ : G.CosAt i), ∃ e, IsIdemSum e (locPl G t) ∧
      ∃ φ, IsLocVec W (.chi (i : ℕ) 0) e (W.vac i) φ (W.cosVec i κ))
    (hth : ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i))
    (h₀ : M₀.IsRow) (h₁ : M.IsRow) (u : Fn G (.grid 0 0)) (hu : IsCuspListed W.θ (.grid 0 0) u) :
    ∀ n (hn : n ≤ D.R.m), PathConv W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u ∧
      IsCuspListed W.θ (.grid n 0) (liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u) ∧
      liftP W M₀ (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u =
        liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨trivial, hu, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨c, hc, e⟩ := ih (by omega)
    set F := liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u with hF
    let k : Fin D.R.m := ⟨n, by omega⟩
    obtain ⟨e', he', φ, hφ⟩ := hloc k (Φ k)
    have hv : IsLocVec W (Arrow.right n 0 : Arrow T).pair e' (vacOf ρm (.right n 0)) φ (W.cosVec n (Φ k)) := by
      show IsLocVec W (.chi n 0) e' (ρm.vX n 0) φ (W.cosVec n (Φ k))
      rw [ρm.vX_row n]; exact hφ
    obtain ⟨hconv, hcusp⟩ := hstep (.right n 0) (Or.inl ⟨n, 0, by omega, Nat.zero_le _, rfl⟩) e' he' φ _ hv (ρ k) F hc
    refine ⟨⟨c, hconv⟩, hcusp, ?_⟩
    show liftA W M₀ (.right n 0) (W.datum ρ Φ k) (liftP W M₀ (rowPath T 0 n)
        (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u) = liftA W M (.right n 0) (W.datum ρ Φ k) F
    rw [e]
    refine liftA_right_eq W M₀ M (h₀.row n (by omega)) (h₁.row n (by omega)) _ F fun γ hγ g x => ?_
    rw [kerA_right_rat W (by omega) (hth k) γ hγ g x, IsCuspListed.left hc γ hγ g]

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

end GlobalTheory.RowStart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListed

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {D : D7}

theorem hasTypeAll_const_mul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} (c : ℂ) (h : HasTypeAll Lie Gs σ f) :
    HasTypeAll Lie Gs σ fun g => c * f g := by
  obtain ⟨v, h1, ℓ, hℓ, ⟨S, C, hS, h2, h3, B, hB, hc⟩, h4⟩ := hasTypeAll_iff.1 h
  refine hasTypeAll_iff.2 ⟨v, h1, fun i => c • ℓ i, fun i => GlobalTheory.MultMem.sobCont_smul c (hℓ i),
    ⟨S, fun i => ‖c‖ * C i, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, hc⟩, fun g hg => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i w hw) (norm_nonneg c)
  · simpa only [mul_assoc] using (h3 S' hS').mul_left ‖c‖
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using (h4 g hg).mul_left c

def TypedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹))
    fun g => φ (x * atTau θ V τ g)

theorem isTypeAt_of_typedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {φ : GA D V → ℂ} (h : TypedBy θ M τ φ) : IsTypeAt θ V τ (S τ) φ :=
  ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ, fun x => hasTypeAll_iff.1 (h x)⟩

theorem typedBy_value (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar}
    (M : DSModel V Sp) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (τ : D.what₂.Tau) : TypedBy θ M τ (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  intro x
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  refine GlobalTheory.CuspValueType.hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
  have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
  have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
  show ℓ (M.rep τ g (v τ)) = _
  rw [h2, h1]
  rfl

theorem star_lift_isTypeAt (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) (z : SmT M)
    (τ : D.what₂.Tau) : IsTypeAt θ V τ (dualPar (S τ)) fun g => star (PiTensorProduct.lift T z g) := by
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨hsm, hmult⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨T', hT'm, hT'⟩ := hmult J χ T hT
  have hT'' := (GlobalTheory.MultMem.mem_mult_iff D θ V _ M' J _ T').1 hT'm
  refine isTypeAt_of_typedBy θ M' τ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    let f' : M'.Vec := fun ρ => ⟨(c ρ).symm (f ρ), (hsm ρ _).2 (by simp)⟩
    have e : (fun g => star (PiTensorProduct.lift T (r • PiTensorProduct.tprod ℂ f) g)) = fun g => star r * T' f' g := by
      funext g
      rw [hT' f' f (fun ρ => by simp [f']) g, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, star_mul']
    rw [e]
    intro x
    exact hasTypeAll_const_mul (star r) (typedBy_value θ hHC M' hT'' f' τ x)
  | add a b ha hb =>
    intro x
    have e : (fun g => star (PiTensorProduct.lift T (a + b) (x * atTau θ V τ g))) =
        fun g => star (PiTensorProduct.lift T a (x * atTau θ V τ g)) + star (PiTensorProduct.lift T b (x * atTau θ V τ g)) := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add]
    rw [e]
    exact (ha x).add (hb x)

end GlobalTheory.StartCusp

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult

variable {D : D7}

theorem isCuspFun_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) : IsCuspFun V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact GlobalTheory.MultMem.isCuspFun_add (GlobalTheory.EndCusp.isAutFunSm_lift hT a).toIsAutFun
      (GlobalTheory.EndCusp.isAutFunSm_lift hT b).toIsAutFun ha hb


end GlobalTheory.StartCusp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspLiftMemCuspList

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {D : D7}
end GlobalTheory.StartCusp
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult
variable {D : D7}

theorem cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h
end GlobalTheory.StartCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | exact _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | (intros; apply _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaTowerFirstOccurrenceExists

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
theorem theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  intro hP hLC
  refine ((_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun hLC hP).and ((_root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList hP hLC).and (GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector.and GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth))).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t Φ M hM y => ?_⟩
  obtain ⟨hstep, hcusp, hloc, hth⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  have H := rowCore ch.W ch.M M ch.rm t ch.ρ Φ (hstep t M hM) (hloc t) (fun i => hth Φ i) hch.vol hM.isRow
    (ch.cv.lift t y) (hcusp t y) D.R.m le_rfl
  exact ⟨H.1, H.2.2⟩
end GlobalTheory.RowStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | exact _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | (intros; apply _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists <;> assumption)
end
end
end
