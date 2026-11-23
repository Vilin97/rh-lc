module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceEqRangeFockMapVariableSignatuStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureOrthonormalFrameEigenOfCartanInvo

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.FrameCartan

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frame_of_cartan : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 →
    IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  intro n M θ hM _ hC
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite]
  have Gherm : Gᴴ = G := by
    ext i j
    simp only [hGdef, conjTranspose_apply, map_apply, star_star]
    rw [← hM i j, star_star]
  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, _, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  refine ⟨p, q, B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.HoweD.FrameCartan

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureOrthonormalFrameEigenOfCartanInvoStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 → IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  first | exact @GlobalTheory.HoweD.FrameCartan.frame_of_cartan | exact GlobalTheory.HoweD.FrameCartan.frame_of_cartan | (intros; apply GlobalTheory.HoweD.FrameCartan.frame_of_cartan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTrace

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MeasureTheory MvPolynomial Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.RealLift GlobalTheory.HoweD

namespace GlobalTheory.HoweD.LieFirstD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

def swapTD (P Q R S : ι → ℕ) :
    (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) ≃ₗ[ℂ] ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) :=
  PiTensorProduct.congr fun w => GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w)

theorem swapTD_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' f) =
      L (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (atPl w L' T) = atPl w L (swapTD P Q R S T) := by
  have e : (swapTD P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapTD P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapTD,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapTD_sumPl (L' : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ w f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' w f) =
      L w (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (sumPl L' T) = sumPl L (swapTD P Q R S T) := by

  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapTD_atPl w (L' w) (L w) (h w) T

end Tensor

theorem lieFirstD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om →
    ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om hCM hψ hfr hΦ hdd hW
  have hfr' : FramedD τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMapD ψ τ d' C A (Φ ∘ₗ (swapTD P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapTD P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapTD P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapTD_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ)
      (fun w f => GlobalTheory.RealLift.LieFirstPf.swapE_heisOp (c w) f)]
  obtain ⟨c, hA⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om hCM hψ hfr' hΦ' hW
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  have key := hA γ hγ Y hY ((swapTD P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapTD_sumPl (fun w => fockAct2 (R w) (S w) (P w) (Q w) (Y w) + (c w * (Y w).trace) • 1)
    (fun w => fockAct1 (P w) (Q w) (R w) (S w) (Y w) + (c w * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul,
        GlobalTheory.RealLift.LieFirstPf.swapE_apply, (GlobalTheory.FockSwap.swap_symmetry (R w) (S w) (P w) (Q w)).2.1]),
    LinearEquiv.apply_symm_apply] at key

end GlobalTheory.HoweD.LieFirstD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTraceStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.firstMember_lieAction_fock_plus_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → (∀ x : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om → ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  exact @GlobalTheory.HoweD.LieFirstD.lieFirstD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActions

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.FockData

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem det_map_ne_zero {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (h : J.det ≠ 0) :
    (J.map τ).det ≠ 0 := by
  rw [show J.map τ = τ.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero τ).2 h

theorem exists_fock_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hXh hXd hWs hWd hW τ hXc hWc

  have hX : ∀ w, ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ),
      IsFrame (X.J.map (τ w).1) A ∧ X.θ w * A = A * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution n _ _ ?_ (det_map_ne_zero _ _ hXd) (hXc w)
    intro i j
    simp only [Matrix.map_apply]
    rw [← hCM.2.2.2 (τ w).1, hXh]
  have hW' : ∀ w, ∃ (r s : ℕ) (C : Matrix (Fin d) (Ix r s) ℂ),
      IsFrame (Complex.I • W.J.map (τ w).1) C ∧ W.θ w * C = C * Jm r s := by
    intro w
    refine GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution d _ _ ?_ ?_ (hWc w)
    · intro i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
      rw [← hCM.2.2.2 (τ w).1, hWs, map_neg, show star Complex.I = -Complex.I from Complex.conj_I]
      ring
    · rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (det_map_ne_zero _ _ hWd)
  choose P Q A hA hθA using hX
  choose R S C hC hθC using hW'

  have hF : FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [one_smul, incM_map_piInf]
      exact hA w
    · rw [incM_map_piInf]
      exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_fockMap_signatures_depend_on_place F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C
    hCM hψ hF

  obtain ⟨hB, ⟨d', hd', hA'⟩, -⟩ := hW
  obtain ⟨c, hc⟩ := GlobalTheory.T.firstMember_lieAction_fock_plus_trace F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co d' 1 Complex.I A C Φ
    (om.comp (MonoidHom.inl _ _)) hCM hψ hF hΦ hd' hA'.1
  obtain ⟨c', hc'⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C Φ
    (om.comp (MonoidHom.inr _ _)) hCM hψ hF hΦ hB.1
  exact ⟨P, Q, R, S, A, C, Φ, c, c', hF, hΦ.1,
    GlobalTheory.T.polynomialFockSpace_eq_range_fockMap_variable_signature F E σ n d P Q R S X W M ψ τ A C Φ hCM hψ hF hθA hθC hΦ, hc, hc'⟩

end GlobalTheory.HoweD.FockData

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActionsStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  first | exact @GlobalTheory.HoweD.FockData.exists_fock_data | exact GlobalTheory.HoweD.FockData.exists_fock_data | (intros; apply GlobalTheory.HoweD.FockData.exists_fock_data <;> assumption)
end
end
