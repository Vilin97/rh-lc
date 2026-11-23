module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsThetaFunctionalSplitIdempotent
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFDblGDeltaTK
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsThetaFunOFNeZeroK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaNonzeroF
theorem exists_isThetaFunOF_ne_zero_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  have hstd := _root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
  let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
  have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
  have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
  have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
    simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]
    ring
  have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
  have hB' : JB.det ≠ 0 := by
    simp only [JB, Matrix.det_neg, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
      (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
  let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
      co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hco
  have hJA : JA = JTᵀ := rfl
  have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by
    ext i j
    simp [JB, incM]
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩
  · rw [GlobalTheory.TransportF.thetaTr_eqF co' τ]
    exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  · intro h
    have h0 := congrFun h 0
    apply hne
    have hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
      funext x
      simp [GlobalTheory.WeilM.schr]
    simpa [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs] using h0
end GlobalTheory.ThetaNonzeroF
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNonzeroThetaFunction

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_nonzero_theta_function : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  first | exact @_root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k | exact _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k | (intros; apply _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsInvFormDblK

section

@[expose] public section



section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblSplitForm
section Abstract
variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}
end Abstract
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
end GlobalTheory.DblSplitForm
namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
theorem exists_invForm_dbl_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    _root_.GlobalTheory.T.exists_nonzero_theta_function F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := _root_.GlobalTheory.T.exists_theta_functional_split_idempotent F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)
end GlobalTheory.DblSplitForm
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsSplitFunctionalDoubled

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_split_functional_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  first | exact @_root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | exact _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | (intros; apply _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k <;> assumption)
end
end
end
