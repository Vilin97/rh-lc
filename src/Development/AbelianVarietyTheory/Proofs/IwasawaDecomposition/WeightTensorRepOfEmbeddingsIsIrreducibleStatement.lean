module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceStableEqBotOrTopStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperatorsStatement
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightActionMatrixCoeffPolynomialInEntriesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZerStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryExtensionOfCmTypeFamily

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.CMExt

def tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) : GL (Fin n) K :=
  ⟨Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
   by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem coe_tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    ((tinv A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem coe_tinv_inv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    (((tinv A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem comp_conj_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {K : Type} [Field K] (σ : L →+* K) :
    (σ.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ := by
  ext x
  simp [IsCMField.complexConj_apply_apply]

noncomputable def cmExtend {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} {K : Type} [Field K]
    (emb : ι → L →+* K) (g : ι → GL (Fin n) K) (σ : L →+* K) : GL (Fin n) K := by
  classical
  exact if h : ∃ τ, σ = emb τ then g h.choose
    else if h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L) then tinv (g h'.choose) else 1

end GlobalTheory.CMExt

open GlobalTheory.CMExt in
theorem GlobalTheory.cmType_family_extend : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K), GlobalTheory.AlgWtF.CMDist emb → ∀ g : ι → GL (Fin n) K, ∃ B : (L →+* K) → GL (Fin n) K,
    (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ ∀ τ, B (emb τ) = g τ := by
  intro L _ _ _ n ι _ K _ emb hd g
  classical
  have hinj2 : ∀ τ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) → τ = τ' := by
    intro τ τ' h
    apply hd.1
    have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) h
    simpa [comp_conj_conj] using this
  have v1 : ∀ τ, cmExtend emb g (emb τ) = g τ := by
    intro τ
    have h : ∃ τ', emb τ = emb τ' := ⟨τ, rfl⟩
    simp only [cmExtend, dif_pos h]
    rw [hd.1 h.choose_spec.symm]
  have v2 : ∀ τ, cmExtend emb g ((emb τ).comp (IsCMField.complexConj L : L →+* L)) = tinv (g τ) := by
    intro τ
    have h : ¬ ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = emb τ' := by
      rintro ⟨τ', h⟩
      exact hd.2 τ' τ h.symm
    have h' : ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) := ⟨τ, rfl⟩
    simp only [cmExtend, dif_neg h, dif_pos h']
    rw [hinj2 _ _ h'.choose_spec.symm]
  have v3 : ∀ σ, (¬ ∃ τ, σ = emb τ) → (¬ ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)) → cmExtend emb g σ = 1 := by
    intro σ h h'
    simp only [cmExtend, dif_neg h, dif_neg h']
  refine ⟨cmExtend emb g, ?_, v1⟩
  intro σ
  by_cases h : ∃ τ, σ = emb τ
  · obtain ⟨τ, rfl⟩ := h
    rw [v2, v1, coe_tinv]
  · by_cases h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)
    · obtain ⟨τ, rfl⟩ := h'
      rw [comp_conj_conj, v1, v2, coe_tinv_inv, Matrix.transpose_transpose]
    · have e1 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = emb τ := by
        rintro ⟨τ, hτ⟩
        apply h'
        refine ⟨τ, ?_⟩
        rw [← hτ, comp_conj_conj]
      have e2 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = (emb τ).comp (IsCMField.complexConj L : L →+* L) := by
        rintro ⟨τ, hτ⟩
        apply h
        refine ⟨τ, ?_⟩
        have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) hτ
        simpa [comp_conj_conj] using this
      rw [v3 _ e1 e2, v3 _ h h']
      simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryExtensionOfCmTypeFamilyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitary_extension_of_cmType_family : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K), GlobalTheory.AlgWtF.CMDist emb → ∀ g : ι → GL (Fin n) K, ∃ B : (L →+* K) → GL (Fin n) K,
    (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ ∀ τ, B (emb τ) = g τ := by
  first | exact @GlobalTheory.cmType_family_extend | exact GlobalTheory.cmType_family_extend | (intros; apply GlobalTheory.cmType_family_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CoeffSpace

theorem nontrivial_VV : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  intro K _ ι _ n lam
  have hanti : ∀ τ, Antitone (lam τ).natW := fun τ i j hij =>
    Int.toNat_le_toNat (by have := (lam τ).anti hij; omega)
  have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) ∈ Formalism.L2.DIV.VV K lam :=
    Submodule.subset_span ⟨fun τ => Formalism.BasicNotions.extremal K n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (hanti τ), rfl⟩
  refine ⟨⟨⟨_, hmem⟩, 0, fun h => ?_⟩⟩
  have h0 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) = 0 := congrArg Subtype.val h
  rw [Finset.prod_eq_zero_iff] at h0
  obtain ⟨τ, _, h⟩ := h0
  have hinj : Function.Injective (fun v : Fin n × Fin n => (τ, v)) := fun a b hab => (Prod.mk.inj hab).2
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _ (MvPolynomial.rename_injective _ hinj (h.trans (map_zero _).symm))

end GlobalTheory.CoeffSpace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nontrivial_weylCoefficientSpace : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  first | exact @GlobalTheory.CoeffSpace.nontrivial_VV | exact GlobalTheory.CoeffSpace.nontrivial_VV | (intros; apply GlobalTheory.CoeffSpace.nontrivial_VV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOntoStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L), γ₀ ∈ GQ0 L n →
    ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ = γ₀ :=
  GlobalTheory.AlgWtF.ratHom_surjective
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.AlgWtF.tenRepF_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM
  have hstab : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ γ : GQ L n, ∀ w ∈ W, GlobalTheory.AlgWtF.tenRepF emb lam γ w ∈ W) →
      ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W := by
    intro W hW g w hw
    have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ w ∈ W,
        Formalism.L2.DIV.rhoK lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w ∈ W := by
      intro γ₀ hγ₀ w hw
      obtain ⟨γ, rfl⟩ := GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto L n γ₀ hγ₀
      exact hW γ w hw
    by_contra hnot
    have hx : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) ∉
        W.map (Formalism.L2.DIV.VV K lam).subtype := by
      rintro ⟨y, hy, hyx⟩
      exact hnot (by rw [show Formalism.L2.DIV.rhoK lam g w = y from Subtype.ext hyx.symm]; exact hy)
    obtain ⟨ψ, hψx, hψW⟩ := Submodule.exists_le_ker_of_notMem hx
    obtain ⟨P, hP⟩ := GlobalTheory.T.weightAction_matrixCoeff_polynomial_in_entries K ι n lam (w : Formalism.L2.DIV.Pol K ι n) ψ
    let f : (ι ⊕ ι) × Fin n × Fin n → (L →+* K) × Fin n × Fin n :=
      fun v => (Sum.elim emb (fun τ => (emb τ).comp (IsCMField.complexConj L : L →+* L)) v.1, v.2)
    have hzero := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K (MvPolynomial.rename f P) ?_
    · obtain ⟨B, hBc, hBe⟩ := GlobalTheory.T.exists_unitary_extension_of_cmType_family L n ι K emb hCM g
      have h0 := hzero B hBc
      rw [MvPolynomial.eval_rename] at h0
      apply hψx
      have h1 : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) =
          Formalism.L2.DIV.actP lam g w := rfl
      rw [h1, hP g, ← h0]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, hBe]
      · simp only [f, Function.comp_apply, Sum.elim_inr]
        rw [hBc (emb τ), hBe τ]
        rfl
    · intro γ₀ hγ₀
      rw [MvPolynomial.eval_rename]
      have h2 := hrat γ₀ hγ₀ w hw
      have h3 : ψ (Formalism.L2.DIV.actP lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w) = 0 :=
        hψW ⟨_, h2, rfl⟩
      rw [hP] at h3
      rw [← h3]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, GlobalTheory.AlgWtF.embGLF]
      · have hinv : (((γ₀⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) =
            ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
          Units.inv_eq_of_mul_eq_one_right hγ₀
        simp only [f, Function.comp_apply, Sum.elim_inr, GlobalTheory.AlgWtF.embGLF, MonoidHom.pi_apply, ← map_inv,
          Matrix.GeneralLinearGroup.map_apply, hinv, ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply,
          RingHom.comp_apply]
  have hsimple : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    GlobalTheory.T.coefficientSpace_stable_eq_bot_or_top K ι n lam (fun τ => GlobalTheory.T.nablaSq_endomorphism_eq_sum_GL_operators K n (lam τ) (GlobalTheory.T.dualWeylModule_simple_charZero K n (lam τ)))
  haveI hnt : Nontrivial (Formalism.L2.DIV.VV K lam) := GlobalTheory.T.nontrivial_weylCoefficientSpace K ι n lam
  haveI : Nontrivial (Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, hx⟩ := exists_ne (0 : Formalism.L2.DIV.VV K lam)
    have hxt : x ∈ (⊤ : Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)).toSubmodule := trivial
    rw [← h'] at hxt
    exact hx hxt
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases hsimple W.toSubmodule (hstab W.toSubmodule (fun γ w hw => W.apply_mem_toSubmodule γ hw)) with h | h
  · left; exact Subrepresentation.ext h
  · right; exact Subrepresentation.ext h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducibleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtF.tenRepF_isIrreducible | exact GlobalTheory.AlgWtF.tenRepF_isIrreducible | (intros; apply GlobalTheory.AlgWtF.tenRepF_isIrreducible <;> assumption)
end
end
