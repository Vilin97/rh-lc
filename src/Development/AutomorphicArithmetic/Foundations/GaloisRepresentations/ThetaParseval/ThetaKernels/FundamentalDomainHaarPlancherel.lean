module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsCoordK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LeviGLInvVal
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormLawK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralCompAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LeviK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LeviParabolicGL
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}
end PositivityTheory.ThKW.LeviParabolicGL

open PositivityTheory.ThKW.LeviParabolicGL in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
    ∃ m : GL (Fin nT) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), Continuous m ∧
      (∀ t, mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (m t) * PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT =
        PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT * t.1) ∧
      ∀ a : GL (Fin nT) E, m (Matrix.GeneralLinearGroup.map (incAF F E) a) ∈
        GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
  intro F E _ _ _ _ _ σ B hB n JT hT
  classical
  have hc : IsCMExt F E σ := hB.cm
  have hcc := GlobalTheory.SplitLagrF.cAF_invol hc
  have hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SplitDetCharF.sig_invol hc x
  set rE : E := (2 : E)⁻¹ with hrE
  have hrE2 : 2 * rE = 1 := mul_inv_cancel₀ two_ne_zero
  have hr : 2 * (inclR (F := F) (AF F)) rE = 1 := by
    have := congrArg (inclR (F := F) (AF F)) hrE2
    rwa [map_mul, map_ofNat, map_one] at this
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hJE : (JT.map (σ : E →+* E))ᵀ = JT := by
    ext i j
    exact hT.1 i j
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have huE : IsUnit JT.det := Ne.isUnit hT.2
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  have eJE : GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT =
      (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  let mG := leviGL (cAF σ) hr hu
  have hmem : ∀ t, mG t ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    intro t
    have h := leviGL_mem (cAF σ) hcc hr hJ hu t
    rw [← eJ] at h
    exact h
  let m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := mG.codRestrict _ hmem
  let m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) :=
    { toFun := fun t => m₀ t
      map_one' := m₀.map_one
      map_mul' := m₀.map_mul }
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hcont_c : Continuous (cAF (F := F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF
  have hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g →
      Continuous fun t => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro f g hf hg
    refine Continuous.matrix_submatrix ?_ _ _
    simp only [L, sM]
    refine ((continuous_const.matrix_mul ?_).matrix_mul continuous_const)
    refine Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_
    exact (continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const
  have hmG : Continuous mG := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_val Units.continuous_coe_inv
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_coe_inv Units.continuous_val
  have hm : Continuous m := by
    have : Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) :=
      hmG.subtype_mk _
    exact this
  refine ⟨m, hm, ?_, ?_⟩
  · intro t
    exact leviGL_col (cAF σ) hr hu t
  · intro a
    let a' : GL (Fin n) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (incAF F E) a
    show ((m₀ a' : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈
      HFin (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    refine ⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩
    · have h := leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a
      rw [← eJE] at h
      exact h
    · exact leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RatK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition
theorem rat_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ γ ∈ GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) γ * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, γ) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 χS ωd hω γ hγ t ht f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h0 : ∀ y : WOF F E nS (nT + nT), symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ 0 y = 0 := fun y => by
    simp [symplOHF, symplOF, hOF]
  have h1 : ∀ w : WOF F E nS nT, ωd (1, γ) f (dC (AF F ⊗[F] E) nT * w) = f (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) := by
    intro w
    have hact : actOF σ JS _ 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) = dC (AF F ⊗[F] E) nT * w := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
        ← Matrix.mul_assoc t.1, Units.mul_inv, Matrix.one_mul]
    have h2 := congrFun (hω.om_heis 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) f hf) 0
    rw [hω.om_aut 1 (one_mem _) γ hγ _ (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ _ f hf), hact] at h2
    simp only [heisOF, h0, AddChar.map_zero_eq_one, one_mul, zero_add] at h2
    exact h2.symm
  obtain ⟨g₀, -, hg⟩ := hγ
  have hg' : mtF σ _ γ = g₀.1.map (incAF F E) := (congrArg Units.val hg).symm
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin nT) (Fin nT) E, t.1 = incM F s₀ := by
    refine ⟨(g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).submatrix (fun p => finSumFinEquiv (Sum.inl p)) id, ?_⟩
    have e : (g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).map (incAF F E) = dC (AF F ⊗[F] E) nT * t.1 := by
      rw [Matrix.map_mul, ← hg', ← ht]
      congr 1
      have := GlobalTheory.LagrThetaInv.dC_mul_rat (F := F) (1 : Matrix (Fin nT) (Fin nT) E)
      rw [Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      exact this.symm
    ext i j
    rw [← GlobalTheory.LagrThetaInv.dC_mul_inl t.1, ← e]
    rfl
  have hd := GlobalTheory.DiagThetaRatF.det_ne_zero_of_unit t s₀ hs₀
  have hs₁ : (t⁻¹).1 = incM F s₀⁻¹ := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hs₀]
    show s₀.map (inclR (F := F) (AF F)) * s₀⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hm : ∀ (s : Matrix (Fin nT) (Fin nT) E) (x : WOF F E nS nT), x ∈ ratLF F E nS nT →
      (incM F s * x : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) ∈ ratLF F E nS nT := by
    rintro s _ ⟨y, rfl⟩
    refine ⟨s * y, ?_⟩
    show (s * y).map (incAF F E) = s.map (incAF F E) * y.map (incAF F E)
    exact Matrix.map_mul
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => (t⁻¹).1 * w
      invFun := fun w => t.1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  unfold GlobalTheory.LagrTheta.lagrInt
  simp only [h1]
  exact GlobalTheory.DiagThetaRatF.setIntegral_comp_aut (ratLF F E nS nT) hK hKc ν h𝓕 e
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id)
    (fun x hx => by
      show (t⁻¹).1 * x ∈ _
      rw [hs₁]
      exact hm _ x hx)
    (fun x hx => by
      show t.1 * x ∈ _
      rw [hs₀]
      exact hm _ x hx)
    (fun w => f (dC (AF F ⊗[F] E) nT * w)) (periodic hf)
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FundamentalDomainPlancherelGlobal

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation
open PositivityTheory.ThKW.ModulusFactorDefinition
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianIntegralFactorisation
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.LagrangianIntegralFactorisation in
theorem PositivityTheory.ThKW.fundamental_domain_plancherel_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨m, hmc, hmC, hmr⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k F E σ B hB nT JT hT
  obtain ⟨α, hαc, hαq, hlaw⟩ := core (V := WOF F E nS (nT + nT) → ℂ)
    (IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ)
    (fun a b f g hf hg => GlobalTheory.WeilPartsF.theta_add (GlobalTheory.WeilPartsF.theta_smul a hf) (GlobalTheory.WeilPartsF.theta_smul b hg))
    (ωd.comp (MonoidHom.inr _ _)) (fun h f hf => hωd.om_pres _ f hf)
    (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT))
    (fun a b f g hf hg => lagrInt_lin ν 𝓕 f g a b
      (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 f hf) (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 g hg))
    (fun h t => mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1)
    (fun a b s u ha hb => by
      show mtF σ _ (a * b) * _ = _ * (s * u).1
      rw [mtF_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul])
    (fun a s ha => by
      show mtF σ _ a⁻¹ * _ = _ * (s⁻¹).1
      have e : dC (AF F ⊗[F] E) nT = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) := by
        rw [← ha, ← Matrix.mul_assoc, mtF_inv_mul, Matrix.one_mul]
      calc mtF σ _ a⁻¹ * dC (AF F ⊗[F] E) nT
          = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * (s.1 * (s⁻¹).1)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) * (s⁻¹).1 := by
            simp only [Matrix.mul_assoc]
        _ = dC (AF F ⊗[F] E) nT * (s⁻¹).1 := by rw [← e])
    (mfac F E nS) (mfac_one nS) (mfac_pos nS) (mfac_mul nS)
    (fun h t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hr f hf)
    m hmc hmC
    (fun f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.cont_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd f hf)
    (GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) : Set _)
    (fun γ hγ t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.rat_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd γ hγ t hr f hf)
    (fun k hk => by
      obtain ⟨M, t, h1, h2⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.conj_pow F E σ nT JT hT k hk
      exact ⟨M, t, h1, fun n hn => h2 n (by rw [Units.val_one, Matrix.mul_one] at hn; exact hn)⟩)
  exact ⟨α, hαc, fun a => hαq _ (hmr a), fun h t hr f hf => hlaw h t hr f hf⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FundamentalDomainHaarPlancherel

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.fundamental_domain_haar_plancherel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  first | exact @_root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global | exact _root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global | (intros; apply _root_.PositivityTheory.ThKW.fundamental_domain_plancherel_global <;> assumption)
end
end
end
