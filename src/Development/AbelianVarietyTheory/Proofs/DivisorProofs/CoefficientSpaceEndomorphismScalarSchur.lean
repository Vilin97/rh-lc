module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZeroStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceCoefficientSpaceEqExtremalTensorLineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslates

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem sqAct_sqAct_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g h : GL (Fin n) K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n lam g (sqAct K n lam h f) = sqAct K n lam (g * h) f := by
  unfold sqAct
  have hm := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n
    ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))
  simp only [AlgHom.comp_apply] at hm
  rw [map_smul, hm, smul_smul, ← Matrix.transpose_mul]
  congr 1
  unfold detPow
  rw [map_mul, mul_zpow, Units.val_mul]

theorem sqAct_one_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam 1 f = f := by
  unfold sqAct detPow
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [h1]; rfl

theorem nablaSq_le_span_extremal : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n),
    nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  intro K _ _ n lam
  set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM
  have hanti : Antitone lam.natW := by
    intro i j hij
    have := lam.anti hij
    unfold DomWeight.natW
    omega
  have hext : extremal K n lam ∈ nablaSq K n lam :=
    Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti
  have hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam := by
    intro g f hf
    unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)
  have hle : M ≤ nablaSq K n lam := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hstab g _ hext
  have hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K),
      sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂ := by
    intro g c f₁ f₂
    unfold sqAct
    rw [map_add (f := _), map_smul, smul_add, smul_comm]
  have hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [sqAct_sqAct_nabla]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero =>
      have h0 : sqAct K n lam g 0 = 0 := by unfold sqAct; simp
      rw [h0]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have := hlin g 1 x y
      rw [one_smul, one_smul] at this
      rw [this]; exact M.add_mem hx hy
    | smul c x _ hx =>
      have hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x := by
        unfold sqAct; rw [map_smul, smul_comm]
      rw [hs]; exact M.smul_mem c hx
  rcases GlobalTheory.T.dualWeylModule_simple_charZero K n lam M hle hMstab with h0 | h1
  · exfalso
    have hmem : extremal K n lam ∈ M := by
      have : sqAct K n lam 1 (extremal K n lam) ∈ M := Submodule.subset_span ⟨1, rfl⟩
      rwa [sqAct_one_nabla] at this
    rw [h0, Submodule.mem_bot] at hmem
    exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem
  · rw [h1]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslatesStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeylModule_le_span_extremalTranslates : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n), nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  first | exact @GlobalTheory.nablaSq_le_span_extremal | exact GlobalTheory.nablaSq_le_span_extremal | (intros; apply GlobalTheory.nablaSq_le_span_extremal <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensors

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : (ι → M) →ₘₗ[K] N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : (ι → MvPolynomial (Fin n × Fin n) K) →ₘₗ[K]
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensorsStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchur

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoefSchur

theorem polyAction_ten (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    actP lam h (ten f) = ten fun τ => sqAct K n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).1
  simp only [actP, ten, detTwK, trAct, sqAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  omega

theorem ten_ext_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (ten fun τ => extremal K n (lam τ)) ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩

theorem endo_scalar : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  intro K _ _ ι _ n lam g hg
  set v0 : VV K lam := ⟨_, ten_ext_mem K lam⟩ with hv0
  have hw0 := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).1
  have hgw := GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight K lam g hg v0 hw0
  obtain ⟨a, ha⟩ := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).2 _ (g v0).2 hgw
  have ha' : g v0 = a • v0 := Subtype.ext ha
  refine ⟨a, ?_⟩
  let W : Submodule K (Pol K ι n) := Submodule.map (VV K lam).subtype (LinearMap.ker (g - a • LinearMap.id))
  have hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (Set.range fun x : GL (Fin n) K => sqAct K n (lam τ) x (extremal K n (lam τ))) :=
    fun τ => GlobalTheory.T.dualWeylModule_le_span_extremalTranslates K n (lam τ)
  have hle := GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors K lam _ hS
  have hW : VV K lam ≤ W := by
    refine hle.trans (Submodule.span_le.2 ?_)
    rintro P ⟨f, hf, rfl⟩
    choose h hh using hf
    have e : ten f = ten fun τ => sqAct K n (lam τ) (h τ) (extremal K n (lam τ)) := by
      congr 1; funext τ; exact (hh τ).symm
    refine ⟨rhoK lam h v0, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hg, ha', map_smul, sub_self]
    · rw [e, ← polyAction_ten]; rfl
  intro v
  obtain ⟨w, hw, hwv⟩ := hW v.2
  have : w = v := Subtype.ext hwv
  subst this
  simpa [sub_eq_zero] using hw

end GlobalTheory.CoefSchur
end
end
end
