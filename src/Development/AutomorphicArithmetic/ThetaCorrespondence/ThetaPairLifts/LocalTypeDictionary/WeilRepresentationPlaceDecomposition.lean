module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RankOneOperatorMemOfTranslationAverageClosedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMemStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteReproducingFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsKFiniteCuspOfTypeOfMemGKGenerated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeTransport
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewiseDecompositionOfKAverage
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewiseDecompositionTranslationInvariant

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteIsotypicDecompositionAdditive

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.KFinDecomp
theorem kFiniteDecomp_class_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  intro D θ hθ hPr N U f f' hf hf'
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hf
  obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hf'
  refine ⟨⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
    fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ)⟩, fun k hk hkf g => ?_⟩
  simp only [Pi.add_apply, a4 k hk hkf g, b4 k hk hkf g]
end GlobalTheory.KFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  first | exact @_root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | exact _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | (intros; apply _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionExistsExponentialModel

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  intro D θ hθ hPr N τ f hf hty x
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hty
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (N.M.enum τ) hE'
  subst hl he
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (N.M.ε τ) (N.M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ)) _ (N.M.fr τ) P'
    (N.M.fr_unit τ) hP' (N.M.fr_gram τ) hJ' _ _ (N.M.σ τ) σ' (N.M.ds τ) hD'
  have t := GlobalTheory.TypeSum.hasTypeAll_transport _ H' (N.M.H τ) (fun g => σ' (P' * g * P'⁻¹)) (N.M.σ τ)
    (gramAt D N.V τ) (Formalism.REAL.Jm (N.M.ε τ)) (N.M.fr τ) (isUnit_gram (N.M.fr_unit τ) (N.M.fr_gram τ))
    (N.M.fr_unit τ) (N.M.fr_gram τ) U hU (fun g => f (x * atTau θ N.V τ g))
    (GlobalTheory.TypeSum.hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := t
  exact ⟨S, v, ℓ, C, hS, hc, h⟩
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.twist_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionGkMapRankOneValues

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  intro D θ hθ hp N τ φ S v ℓ C hS hc h c ψ hψ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hP := N.M.fr_unit τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hJ := N.M.fr_gram τ
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Sm (N.M.ε τ) (N.M.σ τ) u := fun u => hσ.2.2.1 _ u.2
  have key : ∀ u x, ∀ y ∈ UJset (N.M.ε τ),
      res θ N.V τ (N.M.fr τ) (ψ u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (N.M.σ τ y u) := by
    intro u x y hy
    have := (hψ u x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
    simp only [map_smul, smul_eq_mul] at this
    exact this.tsum_eq.symm
  have hval : ∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
    intro u x
    have := key u x 1 (one_mem_UJ _)
    rwa [res_one hθ hP, sigma_one hσ.1] at this
  refine ⟨hval, fun u u' => funext fun x => ?_, fun z u => funext fun x => ?_, ?_, ?_⟩
  · rw [Pi.add_apply, hval, hval, hval, Submodule.coe_add]
    exact (hb x).1 _ _ (hsm u) (hsm u')
  · rw [Pi.smul_apply, hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact (hb x).2.1 z _ (hsm u)
  · intro k hk u w hw
    funext x
    rw [rTr, ← res_conj hP (ψ u) x k, key u x _ (K_le_UJ hk), hval, hw]
    rfl
  · intro X hX u w hw
    funext x
    have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : N.M.fr τ * X * (N.M.fr τ)⁻¹ ∈ lieSet (N.M.ε τ) := by
      refine Transport.conj_lie (G := gramAt D N.V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (N.M.fr τ * (N.M.fr τ)⁻¹)ᴴ * Jm (N.M.ε τ) * (N.M.fr τ * (N.M.fr τ)⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    have e : (w : N.M.H τ) = dRep (N.M.σ τ) (N.M.fr τ * X * (N.M.fr τ)⁻¹) u := by
      rw [hw]
      unfold dRep
      congr 1
      funext t
      rw [Transport.exp_smul_conj hP]
      rfl
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm u) hY).deriv
    rw [← e] at h1
    rw [hval]
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (ψ u) x, ← Transport.exp_smul_conj hP, key u x _ (exp_mem_UJ hY t)]
end GlobalTheory.PlaceDecomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.twist_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionHasCtpOfIsClosed

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_hasCtp_of_isClosed : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  intro D θ _ hp N U W _ _ ρ τ hadd _ hsmul
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ := (std_of_isDS hp.harishChandraModules (N.M.ds τ)).1
  have hs : ∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T →
      HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w) := by
    rintro c T ⟨A, hA, hm⟩
    refine ⟨fun φ => c • A φ, ⟨fun f hf => (hA.cont f hf).const_smul c, fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hsmul c _ (hA.maps f hf), fun τ' h f hf ht x => ?_, fun τ' h g hg f hf => ?_,
      fun τ' h X hX f hf => ?_⟩, fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).smul hσ hS c⟩
    · simp only [hA.add f f' hf hf', smul_add]
    · simp only [hA.smul a f hf, smul_comm c a]
    · exact Submodule.smul_mem _ c (hA.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨?_, hs, ?_⟩
  · rintro T T' ⟨A, hA, hm⟩ ⟨A', hA', hm'⟩
    refine ⟨⟨fun φ => A φ + A' φ, ⟨fun f hf => (hA.cont f hf).add (hA'.cont f hf), fun f f' hf hf' => ?_,
      fun a f hf => ?_, fun f hf => hadd _ _ (hA.maps f hf) (hA'.maps f hf), fun τ' h f hf ht x => ?_,
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).add hσ (hm' φ hφ x S v ℓ C hS hc h) hS⟩,
      ⟨fun φ => A (A' φ), ⟨fun f hf => hA.cont _ (hA'.cont f hf), fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hA.maps _ (hA'.maps f hf), fun τ' h f hf ht => hA.keep τ' h _ (hA'.maps f hf) (hA'.keep τ' h f hf ht),
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => hm _ (hA'.maps φ hφ) x S _ ℓ C hS hc (hm' φ hφ x S v ℓ C hS hc h)⟩⟩
    · simp only [hA.add f f' hf hf', hA'.add f f' hf hf']
      abel
    · simp only [hA.smul a f hf, hA'.smul a f hf, smul_add]
    · exact Submodule.add_mem _ (hA.keep τ' h f hf ht x) (hA'.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf, hA'.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, hA'.lie τ' h X hX f hf]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hA.maps f hf).1.1.smooth (hA'.maps f hf).1.1.smooth hX).symm
    · simp only [hA'.add f f' hf hf', hA.add _ _ (hA'.cont f hf) (hA'.cont f' hf')]
    · simp only [hA'.smul a f hf, hA.smul a _ (hA'.cont f hf)]
    · simp only [hA'.tr τ' h g hg f hf, hA.tr τ' h g hg _ (hA'.maps f hf)]
    · simp only [hA'.lie τ' h X hX f hf, hA.lie τ' h X hX _ (hA'.maps f hf)]
  · simpa using hs 0 _ (hasCtp_id θ N U _ τ)
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationPlaceDecomposition

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
theorem GlobalTheory.PlaceDecomp.weil_decomposition_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  intro D θ hθ hp N U W _ _ _ ρ hρ τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  obtain ⟨e, he, he1⟩ := GlobalTheory.T.exists_K_finite_reproducing_function _ (N.M.ε τ) (W τ) (ρ τ) (hρ τ)
  have hcl := _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp D θ hθ hp N U W ρ τ (fun f f' hf hf' => _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive D θ hθ hp N U f f' hf hf')
    (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).1 (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).2
  obtain ⟨m, a, c, haK, hQ, hA⟩ := GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ (N.M.ε τ) (N.M.H τ) (N.M.σ τ) hσ (HasCtp θ N U (TyOf θ N ρ) τ)
    (_root_.GlobalTheory.T.placewise_decomposition_translation_invariant D θ hθ hp N U W ρ τ) hcl.1 hcl.2.1 (_root_.GlobalTheory.T.placewise_decomposition_of_K_average D θ hθ hp N U W ρ τ) hcl.2.2 e he
  choose A hAop hAmv using fun j (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) => hA j u u.2
  have hexp := fun (f : GA D N.V → ℂ) (hf : f ∈ Cls θ N U) => _root_.GlobalTheory.T.twist_exists_exponential_model D θ hθ hp N τ f hf.1.1 (hf.1.2.2 τ)
  refine ⟨m, fun j => ⟨a j, haK j⟩, A, hAop, fun j f hf => ?_, fun f hf hTy => ?_⟩
  · choose S v ℓ C hW hc h using hexp f hf
    exact (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f) fun u => hAmv j u f hf).2
  · choose S v ℓ C hW hc h using hexp f hf
    have hform := fun j => (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f)
      fun u => hAmv j u f hf).1
    funext x
    have h1 := (moves_avg hθ (N.M.fr_unit τ) (N.M.fr_gram τ) hσ he f x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1
      (one_mem_UJ _)

    simp only [res_one hθ (N.M.fr_unit τ), sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (haK j))).hasSum)
    have h3 : avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f x = f x := by
      have := he1 _ (hTy x)
      have h4 : f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK (1 : KG (N.M.ε τ)) * N.M.fr τ)) = f x :=
        res_one hθ (N.M.fr_unit τ) f x
      exact this.trans h4
    rw [Finset.sum_apply]
    simp only [hform]
    rw [← h2, h3]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

theorem _root_.GlobalTheory.T.weil_representation_place_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | exact _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | (intros; apply _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place <;> assumption)
end
end
end
