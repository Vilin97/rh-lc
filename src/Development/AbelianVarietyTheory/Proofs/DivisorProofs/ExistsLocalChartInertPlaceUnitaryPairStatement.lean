module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalFieldDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceOrthonormalSelfDualFrameStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceUnitaryAdelicHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHermitianFormInertPointEqLocalFormStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrameStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin (a + a')) (w.adicCompletion E)), Valued.v δ = 1 ∧ σL δ = -δ ∧
      IsFrameAt w G.W.L Bm ∧
      (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E))ᵀ * G.W.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)).map σL = δ • 1 := by
  first | exact @GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | exact GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | (intros; apply GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoords

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {ι : Type} (s : Finset ι) (f : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoordsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_action_on_tensorCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  first | exact @GlobalTheory.InertCoordAct.act_kap | exact GlobalTheory.InertCoordAct.act_kap | (intros; apply GlobalTheory.InertCoordAct.act_kap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacePointSupportedAndSurjective

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacePointSupportedAndSurjectiveStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlacePoint_supported_and_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  first | exact @GlobalTheory.InertCoord.kap_at_and_onto | exact GlobalTheory.InertCoord.kap_at_and_onto | (intros; apply GlobalTheory.InertCoord.kap_at_and_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPair

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

open GlobalTheory.InertCoord

theorem exists_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw _
  have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨ϖ, σL, q, ψL, hc, hU, hodd, hpi, hpn, hψ⟩ := GlobalTheory.T.exists_inertPlace_localField_data F E σ B hTr.base v w hw h
  obtain ⟨A, hAf, hA⟩ := GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  obtain ⟨δ, Bm, hδ1, hδ2, hBf, hB⟩ := GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  have hσσ : ∀ x, σL (σL x) = x := hU.1
  have hmapσσ : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)), (M.map σL).map σL = M := fun M =>
    Matrix.ext fun i j => hσσ _
  have hS : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      (((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL)ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 := fun {k} g => by
    have := g.2
    change Formalism.UG.cT σL ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
      (1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) * ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 at this
    rwa [Matrix.mul_one] at this
  have hS' : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL = 1 := fun g => by
    have h2 := congrArg (fun M => M.map σL) (hS g)
    simp only [Matrix.map_mul (f := σL), Matrix.transpose_map, hmapσσ] at h2
    rw [Matrix.map_one _ (map_zero σL) (map_one σL)] at h2
    exact h2
  let φS : Formalism.UG.UJ σL ((1 : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →*
      GL (Fin a') (w.adicCompletion E) := (Formalism.UG.bc σL).comp (Subgroup.subtype _)
  have hφS : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) =
      ((g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL := fun g => rfl
  have hφSu : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ *
      ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := fun g => by
    rw [hφS, hmapσσ]; exact hS g
  obtain ⟨ιS, hSat, hSmat, hSK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.V' A 1 (by rw [hA, one_smul]) φS hφSu
  obtain ⟨ιT, hTat, hTmat, hTK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.W Bm δ hB (Subgroup.subtype _) (fun g => hS' g)
  have hgrp : ∀ {k : ℕ} (P M : GL (Fin k) (w.adicCompletion E)),
      ((P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        ((P * M * P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        (P : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)) := fun P M => by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  refine ⟨ϖ, σL, q, δ, 1, 1, ψL, kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))
    (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)), ιS, ιT, hU, hodd, one_mem _, one_mem _, ?_, ?_,
    ⟨hδ1, hδ2⟩, hpi, hpn, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).1, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).2,
    GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords F E v w hw h G.V' G.W A Bm hAf hBf, ?_, ?_, fun g => hSat g, fun g => hTat g, ?_, ?_⟩
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro x y
    show _ = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * hTens (cA σ) (incM F G.V'.J) (incM F G.W.J) _ _))
    rw [GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm F E σ v w hw h σL hc G.V'.J G.W.J _ _ δ hA hB x y]
    exact hψ _
  · intro g k x
    change actAB (cA σ) (ιS g, ιT k) (kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)) (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) x) = _
    rw [GlobalTheory.T.inertPlace_action_on_tensorCoords F E σ v w hw h G.V' G.W A Bm (ιS g) (ιT k) (hSat g) (hTat k) x, hSmat, hTmat, hgrp, hgrp, hφS]
    congr 1
    have key : ∀ M : GL (Fin a') (w.adicCompletion E),
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ * (M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) = 1 →
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ = ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) := by
      intro M e
      calc _ = ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ *
            ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) * ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
    rw [key _ (hS g)]
    rfl
  · intro g hg
    refine hSK hAf g ?_
    obtain ⟨k, hk⟩ := hg
    let σO : Formalism.UG.intL (w.adicCompletion E) →+* Formalism.UG.intL (w.adicCompletion E) :=
      σL.restrict _ _ fun x hx => by
        change Valued.v (σL x) ≤ 1
        rw [hU.2.1 x]; exact hx
    refine ⟨Formalism.UG.bc σO k, Units.ext (Matrix.ext fun i j => ?_)⟩
    rw [hφS, ← hk]
    rfl
  · intro g hg
    exact hTK hBf g hg

end GlobalTheory.InertBridge

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPairStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_localChart_inertPlace_unitaryPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  first | exact @GlobalTheory.InertBridge.exists_chart | exact GlobalTheory.InertBridge.exists_chart | (intros; apply GlobalTheory.InertBridge.exists_chart <;> assumption)
end
end
