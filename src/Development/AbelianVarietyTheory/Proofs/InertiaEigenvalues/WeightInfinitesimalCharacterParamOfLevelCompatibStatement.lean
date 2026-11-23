module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.ConjugationSwap

section

@[expose] public section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {n : ℕ}

theorem upper_inv (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (U⁻¹).val.BlockTriangular id := by
  letI : Invertible U.val := U.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hU

theorem inv_diag (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (i : Fin n) :
    (U⁻¹).val i i * U.val i i = 1 := by
  have h1 := upper_inv U hU
  have key : ((U⁻¹).val * U.val) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at key
  · exact key
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [h1 (show id k < id i from h), zero_mul]
    · rw [hU (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

def swapB (U : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev, (U.val)ᵀ.submatrix Fin.rev Fin.rev,
    by
      rw [show ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev * (U.val)ᵀ.submatrix Fin.rev Fin.rev =
        (((U⁻¹).val)ᵀ * (U.val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm,
    by
      rw [show (U.val)ᵀ.submatrix Fin.rev Fin.rev * ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev =
        ((U.val)ᵀ * ((U⁻¹).val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm⟩

theorem swapB_val (U : GL (Fin n) ℂ) (i j : Fin n) : (swapB U).val i j = (U⁻¹).val (Fin.rev j) (Fin.rev i) := rfl

theorem swapB_inv_val (U : GL (Fin n) ℂ) (i j : Fin n) : ((swapB U)⁻¹).val i j = U.val (Fin.rev j) (Fin.rev i) := rfl

theorem swapB_upper (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (swapB U).val.BlockTriangular id := by
  intro i j hij
  rw [swapB_val]
  apply upper_inv U hU
  exact Fin.rev_lt_rev.mpr hij

theorem swapB_prod (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (lam' : Fin n → ℤ) :
    ∏ i, (swapB U).val i i ^ lam' i = ∏ i, U.val i i ^ (-lam' (Fin.rev i)) := by
  have hd : ∀ i, (swapB U).val i i = (U.val (Fin.rev i) (Fin.rev i))⁻¹ := by
    intro i
    rw [swapB_val]
    exact eq_inv_of_mul_eq_one_left (inv_diag U hU (Fin.rev i))
  simp only [hd, _root_.inv_zpow']
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def ren : (L →+* ℂ) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (p.1, Fin.rev p.2.1, Fin.rev p.2.2)

theorem evPt_swap (τ : L →+* ℂ) (U : GL (Fin n) ℂ) :
    evPt τ U ∘ ren = evPt (ComplexEmbedding.conjugate τ) (swapB U) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.mpr h)
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [evPt, ren, Function.comp_apply, swapB_val, swapB_inv_val, hcc, Fin.rev_inj]
  have hne' : ¬ τ = ComplexEmbedding.conjugate τ := fun h => hne h.symm
  split_ifs <;> first | rfl | (simp_all <;> rfl)

end

theorem conjugation_swap : ConjSwap := by
  intro L _ _ _ n a τ lam' h
  obtain ⟨ι, hι, hd, b, P, hP, v, hv0, hv⟩ := h
  let w : GQ L n := toGQ w0L longest_element_mem
  let e : a.W ≃ₗ[ℂ] a.W := LinearEquiv.ofLinear (a.ρ w) (a.ρ w⁻¹)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine ⟨ι, hι, hd, b.map e, fun i j => MvPolynomial.rename ren (P i j), ?_, v, hv0, ?_⟩
  · intro γ γ₀ hγ
    let γ₀' : GL (Fin n) L := w0L⁻¹ * γ₀ * w0L
    have hγ' : ((((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀' : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      have e1 : (((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
          Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) (w0L⁻¹) *
            ((γ : GAf L n) : GL (Fin n) (AL L)) *
            Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) w0L := by
        rw [map_inv]; rfl
      rw [e1, Units.val_mul, Units.val_mul, hγ]
      simp only [γ₀', Units.val_mul, Matrix.map_mul]
      rfl
    have hq := hP _ _ hγ'
    ext i j
    have hq' := congrFun (congrFun hq i) j
    rw [LinearMap.toMatrix_apply] at hq'
    rw [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
    have e2 : e.symm (a.ρ γ (e (b j))) = a.ρ (w⁻¹ * γ * w) (b j) := by
      rw [map_mul, map_mul]; rfl
    rw [e2, hq', MvPolynomial.eval_rename]
    refine congrArg (fun f => MvPolynomial.eval f (P i j)) ?_
    funext p
    simp only [Function.comp, ren, γ₀', Units.val_mul]
    have e3 : ((w0L⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    have e4 : ((w0L : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    rw [e3, e4, longest_element_conj]
    rfl
  · intro U hU
    have hB := hv (swapB U) (swapB_upper U hU)
    rw [swapB_prod U hU] at hB
    rw [← hB]
    congr 1
    ext i j
    simp only [Matrix.of_apply, MvPolynomial.eval_rename, evPt_swap]

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg

section

@[expose] public section

open NumberField

namespace GlobalTheory

theorem hwAt_conj_swap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) :=
  PI.UnitaryGroupMassFormula.HwConjInf.conjugation_swap

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNegStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.WeightParamTie

open Formalism.L2

theorem paramV_half (R : Ranks) (h : HCParam R) (j : Fin R.m) :
    NG.paramV R h j (1 / 2) = (param h j).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
  simp only [NG.paramV, param, run, Multiset.map_add (f := _), Multiset.map_map]
  congr 1
  · congr 1
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
  · refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]; push_cast; ring

theorem infOf_neg_rev (n : ℕ) (lam : Fin n → ℤ) :
    NG.infOf (fun k => -lam (Fin.rev k)) = (NG.infOf lam).map Neg.neg := by
  have hu : (Finset.univ : Finset (Fin n)).val = Finset.univ.val.map Fin.rev := by
    conv_lhs => rw [← Finset.univ_map_equiv_to_embedding Fin.revPerm]
    rfl
  unfold NG.infOf
  conv_lhs => rw [hu]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  have hk : (k : ℕ) + 1 ≤ n := k.2
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem weightParam_of_levelTied : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E),
    Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) →
    (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ),
      (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  intro D M tup hL hEta hLoc i ρ
  set a := GlobalTheory.WtDual.dualWt (M.loc i).wt with ha
  have hd : (M.loc i).wt.IsDual a := GlobalTheory.WtDual.isDual_dualWt _
  obtain ⟨⟨lam, hlam, -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)
  obtain ⟨⟨lam', hlam', -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (ComplexEmbedding.conjugate (embT D ρ))
  have huniq := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)).1
  have hsw := GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg _ _ a (embT D ρ) lam' hlam'
  have heq : lam = fun k => -lam' (Fin.rev k) := huniq.unique hlam hsw
  have hlam'eq : lam' = fun k => -lam (Fin.rev k) := by
    funext k; rw [heq]; simp [Fin.rev_rev]
  have key : ∀ (k : ℕ) (hk : k = D.nd.j i) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m),
      (M (D.nd.mu i) k h1 h2).wt = (M.loc i).wt := by
    intro k hk h1 h2; subst hk; rfl
  have hj : (liftIdx D i).1 + 1 = D.nd.j i := by
    have := D.nd.j_range i
    simp only [liftIdx]
    omega
  have hwt := hL.wt (D.nd.mu i) (liftIdx D i) ρ (1 / 2) a lam (hEta ρ)
    (by rw [key _ hj]; exact hd) hlam
  have hinf : D.naut.infWt i (embT D ρ) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
    rw [hLoc i a _ lam hd hlam, hwt, paramV_half]
    rfl
  have e0 : embOver D ρ false = embT D ρ := rfl
  have e1 : embOver D ρ true = ComplexEmbedding.conjugate (embT D ρ) := by
    ext x
    rw [GlobalTheory.JumpDictionaryFoundation.embOver_true_apply, ComplexEmbedding.conjugate_coe_eq]
    rfl
  refine ⟨by rw [e0, hinf], ?_⟩
  rw [e1, hLoc i a _ lam' hd hlam', hlam'eq, infOf_neg_rev, ← hLoc i a _ lam hd hlam, hinf, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

end GlobalTheory.WeightParamTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E), Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) → (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  first | exact @GlobalTheory.WeightParamTie.weightParam_of_levelTied | exact GlobalTheory.WeightParamTie.weightParam_of_levelTied | (intros; apply GlobalTheory.WeightParamTie.weightParam_of_levelTied <;> assumption)
end
end
