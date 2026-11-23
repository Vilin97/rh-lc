module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxRationalBasisCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxOperatorsLeviAndDoubleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticMemClosureGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElementStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindexStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.darbouxChange_realised_comp_and_reindex : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' := by
  first | exact @GlobalTheory.TowU.RealComp.realised_comp_reix | exact GlobalTheory.TowU.RealComp.realised_comp_reix | (intros; apply GlobalTheory.TowU.RealComp.realised_comp_reix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxChangeOperatorWithDoubleLowerUnipot

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem star_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [show star (ψ t) = starRingEnd ℂ (ψ t) from rfl, Complex.conj_mul', GlobalTheory.StdCharFromIsStd.norm_psi hψ t]
  simp

theorem invOf_two_eq : (⅟(2 : AF F)) = algebraMap F (AF F) (2⁻¹) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero), map_one]

theorem quad_rat {κ : Type} [Fintype κ] (B : Matrix κ κ F) (ξ : κ → F) :
    quad (⅟(2 : AF F)) (B.map (algebraMap F (AF F))) (fun i => algebraMap F (AF F) (ξ i)) =
      algebraMap F (AF F) (quad (2⁻¹ : F) B ξ) := by
  rw [map_quad, invOf_two_eq]

theorem isOp_unip (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ F) (hC : Cᵀ = C) :
    IsOp ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1))
      (mulQ (F := F) ψ (⅟2) (C.map (algebraMap F (AF F)))) (mulQ (F := F) ψ (⅟2) (-(C.map (algebraMap F (AF F))))) := by
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  have hA : Aᵀ = A := by rw [hAdef, ← Matrix.transpose_map, hC]
  have inv : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) (-B) (mulQ ψ (⅟2) B φ) = φ := fun B φ => by
    funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have inv' : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) B (mulQ ψ (⅟2) (-B) φ) = φ := fun B φ => by
    have := inv (-B) φ
    rwa [neg_neg] at this
  have adm : ∀ B : Matrix κ κ (AF F), ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ mulQ ψ (⅟2) B ∈ (adeleClass F).adm κ := by
    intro B l hl g hg
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) B hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => by rw [LinearMap.comp_apply, hM f, hT]; rfl⟩
  have nrm : ∀ (B : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) x, ‖mulQ ψ (⅟2) B φ x‖ₑ = ‖φ x‖ₑ := by
    intro B φ x
    rw [mulQ_apply, enorm_mul, ← ofReal_norm (ψ _), GlobalTheory.StdCharFromIsStd.norm_psi hψ, ENNReal.ofReal_one, one_mul]
  refine ⟨mulQ_mem ψ hψ _ A, mulQ_mem ψ hψ _ (-A), fun φ _ => inv A φ, fun φ _ => inv' A φ, adm A, adm (-A),
    fun w φ _ => funext fun x => ?_, ⟨1, one_ne_zero, fun φ _ => ?_⟩, ?_⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]
  · rw [one_mul]
    unfold thetaSum
    congr 1
    funext ξ
    rw [mulQ_apply, hAdef, quad_rat, hψ.2.1, one_mul]
  · intro μ μ' hμ hμ'
    letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : SecondCountableTopology (κ → AF F) := inferInstance
    haveI := hμ
    haveI := hμ'
    have e := Measure.isAddLeftInvariant_eq_smul μ' μ
    have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ
    refine ⟨(μ'.addHaarScalarFactor μ : ℝ≥0∞), by exact_mod_cast hpos.ne', ENNReal.coe_ne_top, fun φ _ => ?_⟩
    simp_rw [nrm]
    conv_lhs => rw [e]
    rw [lintegral_smul_measure]
    rfl

end GlobalTheory.TowU.UnipOp

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dblAct_unip {κ : Type} [Fintype κ] [DecidableEq κ] (C : Matrix κ κ F) :
    dblAct (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) :
        (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) =
      GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-(Matrix.fromBlocks C 0 0 (-C))) 1) := by
  funext w
  rw [act_unip]
  simp only [dblAct, act_unip]
  refine Prod.ext ?_ ?_
  · funext a
    rcases a with a | a <;> rfl
  · funext a
    rcases a with a | a <;>
      simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec] <;> ring

theorem quad_dbl {κ : Type} [Fintype κ] (h : AF F) (A : Matrix κ κ (AF F)) (x : κ ⊕ κ → AF F) :
    quad h (Matrix.fromBlocks A 0 0 (-A)) x = quad h A (x ∘ Sum.inl) + -quad h A (x ∘ Sum.inr) := by
  simp only [quad, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  intro F _ _ ψ hψ κ _ _ C hC
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  let Cd : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks C 0 0 (-C)
  have hCd : Cdᵀ = Cd := by
    simp only [Cd, Matrix.fromBlocks_transpose, hC, Matrix.transpose_zero, Matrix.transpose_neg]
  have hn : (-C).map (algebraMap F (AF F)) = -C.map (algebraMap F (AF F)) := Matrix.map_neg _ (map_neg _) _
  have hCdA : Cd.map (algebraMap F (AF F)) = Matrix.fromBlocks A 0 0 (-A) := by
    simp only [Cd, Matrix.fromBlocks_map, hAdef, Matrix.map_zero _ (map_zero _), hn]
  refine ⟨_, _, isOp_unip ψ hψ C hC, mulQ ψ (⅟2) (Cd.map (algebraMap F (AF F))),
    mulQ ψ (⅟2) (-(Cd.map (algebraMap F (AF F)))), ?_, fun φ₁ _ φ₂ _ => funext fun x => ?_⟩
  · rw [dblAct_unip]
    exact isOp_unip ψ hψ Cd hCd
  · rw [mulQ_apply, hCdA, quad_dbl]
    simp only [boxFun, Pi.star_apply, mulQ_apply, star_mul', star_star, star_psi hψ]
    rw [AddChar.map_add_eq_mul, ← hAdef]
    ring

end GlobalTheory.TowU.UnipOp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDarbouxChangeOperatorWithDoubleLowerUnipotStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  first | exact @GlobalTheory.TowU.UnipOp.main | exact GlobalTheory.TowU.UnipOp.main | (intros; apply GlobalTheory.TowU.UnipOp.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransforms

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel


open GlobalTheory.TowU.WeylModel in
theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransformsStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.weylElement_realised_by_fourierTransforms : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  first | exact @GlobalTheory.TowU.realised_weyl2 | exact GlobalTheory.TowU.realised_weyl2 | (intros; apply GlobalTheory.TowU.realised_weyl2 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDouble

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU

theorem card_two_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    {B : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F} (d : Darboux B κ) :
    Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
  have h1 := d.e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_matrix,
    Module.finrank_baseChange] at h1
  omega

noncomputable def reidx {F : Type} [Field F] [NumberField F] {κ κ' : Type} (e : κ' ≃ κ) :
    ((κ' → AF F) × (κ' → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)) where
  toFun p := (p.1 ∘ e.symm, p.2 ∘ e.symm)
  invFun p := (p.1 ∘ e, p.2 ∘ e)
  map_add' p q := rfl
  map_smul' c p := rfl
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

noncomputable def reindexD {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) : Darboux B κ where
  e := d.e.trans (reidx e)
  form w w' := by
    rw [d.form]
    have h : ∀ u v : κ' → AF F, (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = u ⬝ᵥ v := fun u v => by
      simp only [dotProduct, Function.comp_apply]
      exact e.symm.sum_comp (fun j => u j * v j)
    simp only [LinearEquiv.trans_apply]
    exact (congrArg₂ (· - ·) (h _ _) (h _ _)).symm

theorem reindexD_e {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) (w : W) :
    (reindexD d e).e w = ((d.e w).1 ∘ e.symm, (d.e w).2 ∘ e.symm) := rfl

theorem realised_of_sp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act g) S S' := by
  have hcl := GlobalTheory.sympGen F κ g hg
  clear hg
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hx
    · exact GlobalTheory.T.exists_darbouxOperators_levi_and_double F ψ hψ κ A hA
    · exact GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent F ψ hψ κ C hC
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact GlobalTheory.T.weylElement_realised_by_fourierTransforms F ψ hψ κ
  | one =>
    obtain ⟨S, S', h⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ (Equiv.refl κ)
    refine ⟨S, S', ?_⟩
    have : GlobalTheory.AdelicSvN.act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) = fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ Equiv.refl κ, w.2 ∘ Equiv.refl κ) := by
      funext w; rw [GlobalTheory.AdelicSvN.act_one]; rfl
    rw [this]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨S, S', hS⟩ := hx
    obtain ⟨T, T', hT⟩ := hy
    have : GlobalTheory.AdelicSvN.act (x * y) = GlobalTheory.AdelicSvN.act x ∘ GlobalTheory.AdelicSvN.act (R := AF F) y := by
      funext w; exact GlobalTheory.AdelicSvN.act_mul x y w
    rw [this]
    exact ⟨S ∘ₗ T, T' ∘ₗ S', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ _ _ T T' S S' hT hS⟩

theorem darboux_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ (α β κ κ' : Type) [Fintype α] [Fintype β] [Fintype κ] [Fintype κ'] (B : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F) (d : Darboux B κ) (d' : Darboux B κ'), IsRat d → IsRat d' → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => d'.e (d.e.symm w)) S S' := by
  intro F E _ _ _ _ _ σ _ ψ hψ α β κ κ' _ _ _ _ B d d' hd hd'
  have hc := card_two_eq F E d
  have hc' := card_two_eq F E d'
  have hκ : Fintype.card κ' = Fintype.card κ := by omega
  let e : κ' ≃ κ := Fintype.equivOfCardEq hκ
  let d'' := reindexD d' e
  have hd'' : IsRat d'' := fun x => by
    obtain ⟨y, z, h⟩ := hd' x
    refine ⟨y ∘ e.symm, z ∘ e.symm, ?_⟩
    rw [reindexD_e, h]; rfl
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.RatDarboux.exists_rat_symplectic F E α β κ B d d'' hc hd hd''
  obtain ⟨S, S', hS⟩ := realised_of_sp ψ hψ g hg
  obtain ⟨T, T', hT⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ' e
  have hs : (fun w => d'.e (d.e.symm w)) = (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) ∘ GlobalTheory.AdelicSvN.act g := by
    funext w
    have := hgd (d.e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [Function.comp_apply, ← this, reindexD_e]
    ext i <;> simp
  rw [hs]
  exact ⟨T ∘ₗ S, S' ∘ₗ T', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ' _ _ S S' T T' hS hT⟩

end GlobalTheory.TowU
end
end
