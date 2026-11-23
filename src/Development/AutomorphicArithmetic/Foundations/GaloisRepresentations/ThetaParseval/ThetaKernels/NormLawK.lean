module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CoefK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MfacInvMul

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ChangeK

section

@[expose] public section



section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}
end
theorem change_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FinjK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianProjectionFormula
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianProjectionFormula
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z :=
    GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    first
      | exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
      | fun_prop
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  haveI := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitCoefK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
theorem unit_coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormLawK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.NormModulusHeisenberg
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.NormModulusHeisenberg
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ, hcoef⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL, eL⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.change_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 t _ c0 i0
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) = dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1
    funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
end
end
end
