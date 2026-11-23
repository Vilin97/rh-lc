module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierIndicatorHermitianIntegralLatticeStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLattice
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeIsOpenIsCompactTest

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeIsOpenIsCompactTestStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianLattice_isOpen_isCompact_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  first | exact @GlobalTheory.JR.LatTop.lattice_isTest | exact GlobalTheory.JR.LatTop.lattice_isTest | (intros; apply GlobalTheory.JR.LatTop.lattice_isTest <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerLEqTraceDotProductOfIsIsom

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.kerL_eq_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  intro F E _ _ _ _ _ A ψ x r j hj y' y
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  haveI : Module.Finite E A.L := Module.Finite.equiv j.symm
  haveI : Module.Free E A.L := Module.Free.of_equiv j.symm
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv
  rw [hj y' y]
  unfold Et.kerL Et.psiK
  congr 1
  rw [← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul,
    ← LinearMap.map_smul, Algebra.trace_trace]
end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerLEqTraceDotProductOfIsIsomStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  first | exact @GlobalTheory.JR.Et.kerL_eq_of_isIsom | exact GlobalTheory.JR.Et.kerL_eq_of_isIsom | (intros; apply GlobalTheory.JR.Et.kerL_eq_of_isIsom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLatticeStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  first | exact @GlobalTheory.JR.NormInt.main | exact GlobalTheory.JR.NormInt.main | (intros; apply GlobalTheory.JR.NormInt.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.GammaOneProof

theorem wS_pow_four (k : Type) [CommRing k] : wS k ^ 4 = 1 := by
  have h : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two]

theorem wn_pow_three (k : Type) [CommRing k] : (wS k * nS 1) ^ 3 = 1 := by
  have h : ((wS k * nS 1 : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, 1; -1, 0] * !![1, 1; 0, 1] := rfl
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two]

theorem rep_smul {G X : Type} [Group G] [TopologicalSpace X] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W)
    (g : G) (c : ℂ) {f : X → ℂ} (hf : IsTest f) : W g (c • f) = c • W g f := by
  have h0 : IsTest (0 : X → ℂ) := ⟨IsLocallyConstant.const (0 : ℂ), HasCompactSupport.zero⟩
  have hz : W g 0 = 0 := by
    have := hW.2.2.2 g 1 0 0 h0 h0
    simpa using this
  have := hW.2.2.2 g c f 0 hf h0
  simpa [hz] using this

end GlobalTheory.GammaOneProof


open GlobalTheory.GammaOneProof in
theorem GlobalTheory.JR.gammaOne_holds : GammaOne := by
  intro F E _ _ _ _ _ A ψ hψ x μ hsd ω γ W hW r j hj
  obtain ⟨hΛo, hΛc, hT⟩ := GlobalTheory.T.hermitianLattice_isOpen_isCompact_test F E A r j
  have hN := GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice F E A ψ hψ (x : A.K) r j hj
  have hFour := GlobalTheory.T.fourier_indicator_hermitianIntegralLattice F E A ψ hψ r j (A.kerL ψ x) (GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom F E A ψ (x : A.K) r j hj) hΛo hΛc μ hsd.1
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  set φ0 : A.L → ℂ := Set.indicator Λ 1 with hφ0
  have h0 : (0 : A.L) ∈ Λ := by simp [hΛ]
  have hφ00 : φ0 0 = 1 := by simp [hφ0, Set.indicator_of_mem h0]
  have hc : (((μ Λ).toReal : ℝ) : ℂ) = 1 := by
    have h2 := hsd.2 φ0 hT 0
    have hfe : fourB μ (A.kerL ψ x) φ0 = fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y := funext hFour
    rw [hfe] at h2
    have hl : fourB μ (A.kerL ψ x) (fun y => (((μ Λ).toReal : ℝ) : ℂ) * φ0 y) 0
        = (((μ Λ).toReal : ℝ) : ℂ) * fourB μ (A.kerL ψ x) φ0 0 := by
      simp only [fourB, mul_assoc]; exact integral_const_mul _ _
    rw [hl, hFour, neg_zero, hφ00, mul_one] at h2
    have hr : (μ Λ).toReal * (μ Λ).toReal = 1 := by exact_mod_cast h2
    have hnn : 0 ≤ (μ Λ).toReal := ENNReal.toReal_nonneg
    have : (μ Λ).toReal = 1 := by nlinarith
    rw [this]; simp
  obtain ⟨hrep, hrel⟩ := hW
  obtain ⟨hn, -, hw⟩ := hrel φ0 hT
  have hWw : W (wS A.K) φ0 = γ • φ0 := by
    funext y; rw [hw y, hFour y, hc]; simp
  have hWn : W (nS 1) φ0 = φ0 := by
    funext y; rw [hn 1 y]
    by_cases hy : y ∈ Λ
    · rw [one_mul, hN y hy, one_mul]
    · simp [hφ0, Set.indicator_of_notMem hy]
  have hWwn : W (wS A.K * nS 1) φ0 = γ • φ0 := by rw [hrep.2.2.1 _ _ _ hT, hWn, hWw]
  have hpow : ∀ (g : SpecialLinearGroup (Fin 2) A.K) (c : ℂ), W g φ0 = c • φ0 → ∀ k : ℕ, W (g ^ k) φ0 = c ^ k • φ0 := by
    intro g c hg k
    induction k with
    | zero => simp [hrep.2.1 φ0 hT]
    | succ k ih => rw [pow_succ', hrep.2.2.1 _ _ _ hT, ih, rep_smul hrep _ _ hT, hg, smul_smul, pow_succ]
  have e4 := congrFun (hpow _ _ hWw 4) 0
  rw [wS_pow_four, hrep.2.1 φ0 hT] at e4
  have e3 := congrFun (hpow _ _ hWwn 3) 0
  rw [wn_pow_three, hrep.2.1 φ0 hT] at e3
  simp only [Pi.smul_apply, smul_eq_mul, hφ00, mul_one] at e4 e3
  have : γ ^ 4 = γ ^ 3 * γ := pow_succ _ _
  rw [← e4, ← e3, one_mul] at this
  exact this.symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOneStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  first | exact @GlobalTheory.JR.gammaOne_holds | exact GlobalTheory.JR.gammaOne_holds | (intros; apply GlobalTheory.JR.gammaOne_holds <;> assumption)
end
end
