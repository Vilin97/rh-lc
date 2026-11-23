module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaBox

theorem thetaSum_boxFun : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  have s₁ := (thetaSum_summable_linear F κ).2.1 φ₁ h₁
  have s₂ := (thetaSum_summable_linear F κ').2.1 φ₂ h₂
  unfold thetaSum
  rw [tsum_mul_tsum_of_summable_norm s₁ s₂]
  rw [← (Equiv.sumArrowEquivProdArrow κ κ' F).symm.tsum_eq]
  rfl

end GlobalTheory.ThetaBox
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunctionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicThetaDistributionSum_productFunction : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  first | exact @GlobalTheory.ThetaBox.thetaSum_boxFun | exact GlobalTheory.ThetaBox.thetaSum_boxFun | (intros; apply GlobalTheory.ThetaBox.thetaSum_boxFun <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariant

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaOppParab

variable {κ : Type}

def negSnd {M : Type} [Neg M] (x : κ ⊕ κ → M) : κ ⊕ κ → M := Sum.elim (fun i => x (Sum.inl i)) (fun i => -x (Sum.inr i))

theorem negSnd_negSnd {M : Type} [InvolutiveNeg M] (x : κ ⊕ κ → M) : negSnd (negSnd x) = x :=
  funext fun i => by cases i <;> simp [negSnd]

theorem negSnd_add {M : Type} [AddCommGroup M] (x y : κ ⊕ κ → M) : negSnd (x + y) = negSnd x + negSnd y :=
  funext fun i => by cases i <;> simp [negSnd, add_comm]

theorem negSnd_dot {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ y = x ⬝ᵥ negSnd y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

theorem negSnd_dot_negSnd {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ negSnd y = x ⬝ᵥ y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

def negSndL (R M : Type) [Semiring R] [AddCommGroup M] [Module R M] : (κ ⊕ κ → M) ≃ₗ[R] (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  map_add' := negSnd_add
  map_smul' c x := funext fun i => by cases i <;> simp [negSnd, Pi.smul_apply, smul_neg]
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd

def negSndH (M : Type) [TopologicalSpace M] [AddGroup M] [ContinuousNeg M] : (κ ⊕ κ → M) ≃ₜ (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd
  continuous_toFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg
  continuous_invFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg

theorem map_neg_one_mat {n R S G : Type} [DecidableEq n] [Ring R] [Ring S] [FunLike G R S] [RingHomClass G R S]
    (f : G) : (-1 : Matrix n n R).map f = -1 := by
  rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

variable (F : Type) [Field F] [NumberField F]
open scoped Classical

def negOp : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) := LinearMap.funLeft ℂ ℂ negSnd

theorem negOp_apply (φ : (κ ⊕ κ → AF F) → ℂ) (x) : negOp F φ x = φ (negSnd x) := rfl

theorem negOp_negOp (φ : (κ ⊕ κ → AF F) → ℂ) : negOp F (negOp F φ) = φ :=
  funext fun x => by simp [negOp_apply, negSnd_negSnd]

theorem negOp_schr [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) (φ : (κ ⊕ κ → AF F) → ℂ) :
    negOp F (schr ψ w φ) = schr ψ (negSnd w.1, negSnd w.2) (negOp F φ) := by
  funext x
  simp only [negOp_apply, schr, negSnd_dot, negSnd_add, negSnd_negSnd]

theorem pureA_negSnd [Fintype κ] (f : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    negOp F (pureA F f g) = pureA F (f ∘ negSnd) (g ∘ negSnd) := by
  funext x
  simp only [negOp_apply, pureA, Function.comp_apply]
  congr 2
  · funext i
    cases i with
    | inl i => rfl
    | inr i => exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x (Sum.inr i)).1
  · funext i
    cases i with
    | inl i => rfl
    | inr i => rfl

theorem comp_negOp_mem_adm [Fintype κ] {l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (κ ⊕ κ)) :
    l ∘ₗ negOp F ∈ (adeleClass F).adm (κ ⊕ κ) := by
  intro g hg
  let A : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    (negSndL ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearEquiv
  let B := negSndH (κ := κ) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨T, hT⟩ := hl (g ∘ B) ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩
  refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A), fun f => ?_⟩
  rw [LinearMap.comp_apply, pureA_negSnd, ContinuousLinearMap.comp_apply, ← hT]
  rfl

theorem thetaSum_negOp [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ) : thetaSum F (negOp F φ) = thetaSum F φ := by
  unfold thetaSum
  have e := Equiv.tsum_eq (negSndL (κ := κ) F F).toEquiv (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i))
  refine Eq.trans (tsum_congr fun ξ => ?_) e
  show φ (negSnd _) = φ (fun i => algebraMap F (AF F) (negSnd ξ i))
  congr 1
  funext i
  cases i <;> simp [negSnd]


open scoped Classical in
theorem thetaSum_omd_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (cA σ) (dbl (incM F JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ a b JA JB κ _ hcard d hd dd hdd χ hχ omd hS hR q q₀ hq s hqs φ hφ
  let M₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := Matrix.fromBlocks 1 0 0 (-1)
  let M₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E) := Matrix.fromBlocks 1 0 0 (-1)
  have hM₀sq : M₀ * M₀ = 1 := by simp [M₀, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hM₀' : incM F M₀' = M₀ := by
    simp only [M₀, M₀', incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
  let w₀g : GL (Fin b ⊕ Fin b) (AE F E) := ⟨M₀, M₀, hM₀sq, hM₀sq⟩
  have hw₀mem : w₀g ∈ UG (cA σ) (dbl (incM F JB)) := by
    show M₀ᵀ * dbl (incM F JB) * M₀.map (cA σ) = dbl (incM F JB)
    simp only [M₀, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Matrix.fromBlocks_multiply]
  let w₀ : UG (cA σ) (dbl (incM F JB)) := ⟨w₀g, hw₀mem⟩
  have hw₀v : ((w₀ : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = M₀ := rfl
  have hw₀w₀ : w₀ * w₀ = 1 := Subtype.ext (Units.ext hM₀sq)
  let p : UG (cA σ) (dbl (incM F JB)) := w₀ * q * w₀
  have hpv : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      M₀ * ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * M₀ := rfl
  have hp₀ : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      incM F (M₀' * q₀ * M₀') := by
    rw [hpv, hq, ← hM₀']
    simp only [incM, Matrix.map_mul]
  have hMd : M₀ * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hMa : M₀ * (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hqs' : ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) *
        (s : Matrix (Fin b) (Fin b) (AE F E)) := hqs
  have hps : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) * (s : Matrix (Fin b) (Fin b) (AE F E)) := by
    rw [hpv]
    simp only [Matrix.mul_assoc]
    rw [hMd, hqs', ← Matrix.mul_assoc, hMa]
  have hsieg := GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hcard d hd dd hdd χ hχ omd hS hR p (M₀' * q₀ * M₀') hp₀ s hps
  have hrel : ∀ v, dd.e (actB (cA σ) w₀ v) = (negSnd (dd.e v).1, negSnd (dd.e v).2) := by
    intro v
    have hv : actB (cA σ) w₀ v = Matrix.fromCols v.toCols₁ (-v.toCols₂) := by
      rw [actB, hw₀v]
      conv_lhs => rw [← Matrix.fromCols_toCols v]
      rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp
    conv_rhs => rw [← Matrix.fromCols_toCols v]
    rw [hv, hdd, hdd, map_neg]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp [negSnd]
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute ψ hψ (negOp F * omd w₀)
    (fun l hl => by
      rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact hS.adm w₀ _ (comp_negOp_mem_adm F hl))
    (fun w φ hφ => by
      obtain ⟨v, rfl⟩ := dd.e.surjective w
      have e1 : schr ψ (dd.e v) = dd.rho ψ v := rfl
      rw [e1, mul_apply_eq_comp, mul_apply_eq_comp, hS.impl w₀ v φ hφ, Darboux.rho, hrel, negOp_schr]
      simp only [negSnd_negSnd]
      rfl)
  have hsm : ∀ (c : ℂ) (f : (κ ⊕ κ → AF F) → ℂ), thetaSum F (c • f) = c * thetaSum F f := fun c f => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  have hΘw : ∀ X ∈ schA F (κ ⊕ κ), thetaSum F (omd w₀ X) = c * thetaSum F X := fun X hX => by
    have h1 := congrArg (negOp F) (hc X hX)
    rw [mul_apply_eq_comp, negOp_negOp, map_smul] at h1
    rw [h1, hsm, thetaSum_negOp]
  have hq' : q = w₀ * p * w₀ := by
    show q = w₀ * (w₀ * q * w₀) * w₀
    rw [show w₀ * (w₀ * q * w₀) * w₀ = (w₀ * w₀) * q * (w₀ * w₀) by group, hw₀w₀, one_mul, mul_one]
  calc thetaSum F (omd q φ) = thetaSum F (omd w₀ (omd p (omd w₀ φ))) := by
        rw [hq', map_mul, map_mul]; rfl
    _ = c * thetaSum F (omd p (omd w₀ φ)) := hΘw _ (hS.pres _ _ (hS.pres _ _ hφ))
    _ = c * thetaSum F (omd w₀ φ) :=
      congrArg (fun z => c * z) (hsieg (omd w₀ φ) (hS.pres w₀ φ hφ))
    _ = thetaSum F (omd w₀ (omd w₀ φ)) := (hΘw _ (hS.pres _ _ hφ)).symm
    _ = thetaSum F φ := by rw [← mul_apply_eq_comp, ← map_mul, hw₀w₀, map_one, one_apply_eq_self]

end GlobalTheory.ThetaOppParab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariantStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | exact GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | (intros; apply GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZeroStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  first | exact @GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | exact GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | (intros; apply GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilThetaRat

theorem dbl_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (χ : Chr F E) (hχ : IsHecke F E χ)
    (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd g φ) = thetaSum F φ := by
  intro φ hφ
  obtain ⟨p, q, p', p₀, q₀, p₀', t, s, t', hp, hq, hp', ht, hs, ht', rfl⟩ :=
    GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product F E σ hσ b JB ε hJ hdet g g₀ hg
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc
    _ = thetaSum F (omd q (omd p' φ)) :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p p₀ hp t ht (omd q (omd p' φ)) (hS.pres q _ (hS.pres p' _ hφ))
    _ = thetaSum F (omd p' φ) :=
      GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR q q₀ hq s hs (omd p' φ) (hS.pres p' _ hφ)
    _ = thetaSum F φ :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p' p₀' hp' t' ht' φ hφ

theorem member_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (χ : Chr F E) (hχ : IsHecke F E χ) (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (γ : UG (cA σ) (incM F JB)) (γ₀ : Matrix (Fin b) (Fin b) E)
    (hγ : ((γ : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀) :
    ∀ Φ ∈ schA F κ, thetaSum F (om γ Φ) = thetaSum F Φ := by
  intro Φ hΦ
  obtain ⟨hom, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ) (Fin b) (incM F JB) γ
  have hgd0 : ((gd : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F (Matrix.fromBlocks γ₀ 0 0 1) := by
    rw [hgd, hγ]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨φ₂, hφ₂, hθ⟩ := GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero F κ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e1 := dbl_rat σ hσ ψ hψ JA JB ε hJ hdet hκ d hd dd hdd χ hχ omd hS.toIsSplitting hR gd _ hgd0 _ hb
  rw [hres γ gd hgd Φ hΦ φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ _ (hom.pres γ Φ hΦ) φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ Φ hΦ φ₂ hφ₂] at e1
  exact mul_right_cancel₀ hθ e1

theorem rat_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, ((γ.1 : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨(g₀ : Matrix (Fin n) (Fin n) E), ?_⟩
  rw [← hg₀]
  ext i j
  rfl

theorem thetaSum_om_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ :=
  PositivityTheory.ThKF0.darboux_coordinates_rational_exist

end GlobalTheory.WeilThetaRat
end
end
end
