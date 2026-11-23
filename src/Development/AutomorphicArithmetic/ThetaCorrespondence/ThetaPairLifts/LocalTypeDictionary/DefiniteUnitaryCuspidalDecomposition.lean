module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEachStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrameStatement
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensionalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

theorem _root_.GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  first | exact @GlobalTheory.RepAdj.rep_adjoint_eq_inv | exact GlobalTheory.RepAdj.rep_adjoint_eq_inv | (intros; apply GlobalTheory.RepAdj.rep_adjoint_eq_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup

section

@[expose] public section

open Finset

namespace GlobalTheory

theorem sum_update_fiber_count {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (G : (∀ i, Fin (m i)) → ℂ) :
    ∑ J : (∀ i, Fin (m i)), ∑ j : Fin (m i₀), G (Function.update J i₀ j) = (m i₀ : ℂ) * ∑ J, G J := by
  let e : (∀ i, Fin (m i)) × Fin (m i₀) ≃ (∀ i, Fin (m i)) × Fin (m i₀) :=
    { toFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Fintype.sum_prod_type' (fun J j => G (Function.update J i₀ j))]
  rw [Fintype.sum_equiv e (fun p => G (Function.update p.1 i₀ p.2)) (fun p => G p.1) (fun p => rfl)]
  rw [Fintype.sum_prod_type' (fun J (_ : Fin (m i₀)) => G J)]
  simp [Finset.mul_sum]

theorem sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  intro ι _ _ X W _ _ m k ℓ i₀ F F' w w' hone v
  have key : ∀ (u : W i₀) (H : (∀ i, X i) → ℂ) (J : ∀ i, Fin (m i)),
      ∑ j, (∏ i, ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)) *
          H (fun i => k i (Function.update J i₀ j i))
        = (∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i)) *
          ∑ j, ℓ i₀ j u * H (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) := by
    intro u H J
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest : ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)
        = ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := by simpa using hi
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hk : (fun i => k i (Function.update J i₀ j i)) = Function.update (fun i => k i (J i)) i₀ (k i₀ j) := by
      funext i
      exact Function.apply_update k J i₀ j i
    rw [hrest, hk, Function.update_self, Function.update_self]
    ring
  by_cases hm : m i₀ = 0
  · haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by
      have h := J i₀
      rw [hm] at h
      exact h.elim0⟩
    simp
  · have hm' : (m i₀ : ℂ) ≠ 0 := by exact_mod_cast hm
    apply mul_left_cancel₀ hm'
    rw [← sum_update_fiber_count, ← sum_update_fiber_count]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [key w' F J, key w F' J, hone J]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroupStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.sum_prod_update_regroup_of_update_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  first | exact @GlobalTheory.sum_prod_update_regroup | exact GlobalTheory.sum_prod_update_regroup | (intros; apply GlobalTheory.sum_prod_update_regroup <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteUnitaryCuspidalDecomposition

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open Classical
namespace GlobalTheory.DefiniteDecomp
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
theorem cusp_forms_decompose_definite_unitary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  intro hP D θ N hθ hs hd φ hφ
  obtain ⟨hAut, -, hType⟩ := hφ
  haveI hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have hmulK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      g * h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun τ g hg h hh => GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh
  have hρ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      (N.M.rep τ (g * h) : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) := by
    intro τ g hg h hh
    rw [rep_mul N.M τ hg hh]
    rfl
  have hframe : ∀ τ, ∃ (m : ℕ) (k : Fin m → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (B : Fin m → (N.M.H τ →ₗ[ℂ] N.M.H τ)), (∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) ∧
      (∀ A : N.M.H τ →ₗ[ℂ] N.M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) =
          ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) *
            LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ
          (B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ))) • B j) :=
    fun τ => GlobalTheory.T.exists_dual_frame_span_unitary_representation (Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) (fun g => (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ))
      (hmulK τ) (hρ τ) (fun g hg => ⟨g⁻¹, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).1, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).2⟩)
  choose m k B hk hB1 hB2 using hframe
  have hexp : ∀ τ x, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), φ (x * atTau θ N.V τ g) =
      ∑ j, φ (x * atTau θ N.V τ (k τ j)) *
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) :=
    fun τ x g hg => GlobalTheory.T.modelType_form_expands_along_dualFrame hP.discreteSeriesHermitianUnique θ N.M τ (k τ) (hk τ) (B τ) (hB1 τ) (hType τ) x hg
  let F : GA D N.V → (D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) → ℂ :=
    fun x g => φ (x * realProd θ N.V g)
  have hsplit : ∀ x (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → ∀ τ₀ g', g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀) →
      F x (Function.update g τ₀ g') = φ ((x * realProd θ N.V (Function.update g τ₀ 1)) * atTau θ N.V τ₀ g') := by
    intro x g hg τ₀ g' hg'
    show φ (x * realProd θ N.V (Function.update g τ₀ g')) = _
    rw [realProd_update hθ hg τ₀ hg', (realProd_commute hθ hg τ₀ hg').eq, mul_assoc]
  have hFexp : ∀ x τ₀ (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → F x g = ∑ j, F x (Function.update g τ₀ (k τ₀ j)) *
        LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ (g τ₀) : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
    intro x τ₀ g hg
    have e0 : F x g = F x (Function.update g τ₀ (g τ₀)) := by rw [Function.update_eq_self]
    rw [e0, hsplit x g hg τ₀ _ (hg τ₀), hexp τ₀ _ _ (hg τ₀)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsplit x g hg τ₀ _ (hk τ₀ j)]
  let bH : ∀ τ, Module.Basis (Fin (Module.finrank ℂ (N.M.H τ))) ℂ (N.M.H τ) := fun τ => Module.finBasis ℂ (N.M.H τ)
  let ℓ : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → ∀ τ, Fin (m τ) → (N.M.sm τ →ₗ[ℂ] ℂ) :=
    fun a τ j => (bH τ).coord (a τ) ∘ₗ B τ j ∘ₗ (N.M.sm τ).subtype
  let T : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → MMap N.M := fun a =>
    ∑ J : (∀ τ, Fin (m τ)), ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap
      (fun τ => ℓ a τ (J τ))).smulRight (fun x => F x (fun τ => k τ (J τ)))
  have hT : ∀ a (v : ∀ τ, N.M.sm τ) (x : GA D N.V), T a v x = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) * F x (fun τ => k τ (J τ)) := by
    intro a v x
    simp only [T, MultilinearMap.sum_apply, Finset.sum_apply, MultilinearMap.smulRight_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Pi.smul_apply, smul_eq_mul]
  have hMult : ∀ a, IsMultMap θ N.M ∅ 1 (T a) := by
    intro a
    refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _,
      fun v k' hk' => absurd hk' (Set.notMem_empty k'), fun τ₀ h hh v w hw => ?_, fun τ v x => ?_⟩
    · have e : T a v = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) •
          rTr N.V (realProd θ N.V (fun τ => k τ (J τ))) φ := by
        funext x
        rw [hT, Finset.sum_apply]
        rfl
      rw [e]
      refine Finset.sum_induction _ (IsAutFunSm θ N.V) (fun f g hf hg => GlobalTheory.MultMem.isAutFunSm_add hf hg) ?_
        (fun J _ => GlobalTheory.MultMem.isAutFunSm_smul _ (isAutFunSm_realProd hθ _ hAut))
      exact Formalism.L2.Theta.isAutFunSm_const (θ := θ) (V := N.V) (c := (0 : ℂ))
    · funext x
      have hkJ : ∀ J : (∀ τ, Fin (m τ)), ∀ τ, (fun τ => k τ (J τ)) τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
        fun J τ => hk τ (J τ)
      have hF' : ∀ J : (∀ τ, Fin (m τ)), F (x * atTau θ N.V τ₀ h) (fun τ => k τ (J τ)) =
          F x (Function.update (fun τ => k τ (J τ)) τ₀ (h * k τ₀ (J τ₀))) := by
        intro J
        show φ (x * atTau θ N.V τ₀ h * realProd θ N.V _) = φ (x * realProd θ N.V _)
        have e1 := realProd_update hθ (hkJ J) τ₀ (hmulK τ₀ h hh _ (hk τ₀ (J τ₀)))
        have e2 := realProd_update hθ (hkJ J) τ₀ (hk τ₀ (J τ₀))
        rw [Function.update_eq_self] at e2
        rw [e1, e2, GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ₀ hh (hk τ₀ (J τ₀))]
        simp only [mul_assoc]
      show T a (Function.update v τ₀ w) x = T a v (x * atTau θ N.V τ₀ h)
      rw [hT, hT]
      simp only [hF']
      have key := GlobalTheory.T.sum_prod_update_regroup_of_update_eq (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) (W := fun τ => N.M.sm τ)
        k (ℓ a) τ₀ (F x) (fun g => F x (Function.update g τ₀ (h * g τ₀))) (v τ₀) w ?_ v
      · rw [Function.update_eq_self] at key
        exact key
      intro J
      simp only [Function.update_idem, Function.update_self]
      have hf : ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀), F x (Function.update (fun τ => k τ (J τ)) τ₀ g') =
          ∑ j, F x (Function.update (fun τ => k τ (J τ)) τ₀ (k τ₀ j)) *
            LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ g' : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
        intro g' hg'
        rw [hsplit x _ (hkJ J) τ₀ g' hg', hexp τ₀ _ g' hg']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsplit x _ (hkJ J) τ₀ _ (hk τ₀ j)]
      have := equiv_one (Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀)) (fun g => (N.M.rep τ₀ g : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀))
        (hρ τ₀) (k τ₀) (hk τ₀) (B τ₀) (hB2 τ₀) _ hf (hmulK τ₀) ((bH τ₀).coord (a τ₀)) (v τ₀ : N.M.H τ₀) hh
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, hw]
      exact this
    · exact GlobalTheory.DefiniteEnd.exists_sobCont N.M τ (T a) v x
  have hmem : ∀ a, PiTensorProduct.lift (T a) ∈ N.Cusp θ := fun a =>
    (mem_multT θ N.M ∅ 1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact Submodule.subset_span (hMult a))
  let e : ∀ τ, Fin (Module.finrank ℂ (N.M.H τ)) → N.M.sm τ := fun τ i => ⟨bH τ i, by rw [sm_eq_top N.M τ]; trivial⟩
  have htr : ∀ τ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ 1 : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) =
      ∑ i, (bH τ).coord i (B τ j (bH τ i)) := by
    intro τ j
    rw [rep_one N.M τ, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.trace_eq_matrix_trace ℂ (bH τ), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  have hrep : ∀ x, φ x = ∑ a : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))), T a (fun τ => e τ (a τ)) x := by
    intro x
    have h1 : φ x = F x (fun _ => 1) := by
      show φ x = φ (x * realProd θ N.V _)
      rw [realProd_one hθ, mul_one]
    have h2 := GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (fun τ => Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) m k hk
      (fun τ j g => LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j)) (F x)
      (fun τ₀ g hg => hFexp x τ₀ g hg) (fun _ => 1) (fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _)
    rw [h1, h2]
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [htr]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  let eqv := Fintype.equivFin (∀ τ, Fin (Module.finrank ℂ (N.M.H τ)))
  refine ⟨Fintype.card _, fun i => ⟨PiTensorProduct.lift (T (eqv.symm i)), hmem _⟩,
    fun i => PiTensorProduct.tprod ℂ (fun τ => e τ (eqv.symm i τ)), ?_⟩
  funext x
  rw [hrep x, Finset.sum_apply]
  simp only [PiTensorProduct.lift.tprod]
  exact (Equiv.sum_comp eqv.symm (fun a => T a (fun τ => e τ (a τ)) x)).symm
end GlobalTheory.DefiniteDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.definite_unitary_cuspidal_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  first | exact @_root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary | exact _root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary | (intros; apply _root_.GlobalTheory.DefiniteDecomp.cusp_forms_decompose_definite_unitary <;> assumption)
end
end
end
