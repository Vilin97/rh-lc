module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeigh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleAlgebraicWeightSubrepStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Mathlib.RingTheory.PicardGroup
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeight

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]

    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeightStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  first | exact @GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual | exact GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual | (intros; apply GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfield

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory

theorem matrix_intertwiner_descends : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  intro K _ e Γ m p _ _ A B ⟨X, hX, hXc⟩
  letI := e.toAlgebra
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K ℂ, ℓ (X a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab ((Module.forall_dual_apply_eq_zero_iff K (X a b)).1 h)
  have h1 : ∀ (x : ℂ) (c : K), ℓ (x * e c) = ℓ x * c := by
    intro x c
    have : x * e c = c • x := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∀ (x : ℂ) (c : K), ℓ (e c * x) = c * ℓ x := by
    intro x c
    have : e c * x = c • x := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
  refine ⟨X.map ℓ, ?_, fun γ => ?_⟩
  · intro h
    apply hℓ
    have := congrFun (congrFun h a) b
    simpa using this
  · ext i j
    have key := congrArg (fun M => ℓ (M i j)) (hXc γ)

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, h1, h2] at key ⊢
    exact key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  first | exact @GlobalTheory.matrix_intertwiner_descends | exact GlobalTheory.matrix_intertwiner_descends | (intros; apply GlobalTheory.matrix_intertwiner_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.WtDescent

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := GlobalTheory.T.exists_irreducible_algebraicWeight_subrep L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat (L := L) (n := n) γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat (L := L) (n := n) γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.mtRatDual_hw L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModuleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.irreducible_weight_descends_to_polynomial_module : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtDescent.weight_descends | exact GlobalTheory.WtDescent.weight_descends | (intros; apply GlobalTheory.WtDescent.weight_descends <;> assumption)
end
end
