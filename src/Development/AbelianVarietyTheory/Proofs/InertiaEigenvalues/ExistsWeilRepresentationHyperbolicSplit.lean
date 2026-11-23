module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiKStatement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusActionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflectionStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructureStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperatiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureEtaleHermitianEqCoordsStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsField

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsFieldStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  first | exact @GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | exact GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | (intros; apply GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTest

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring

end GlobalTheory.JR.Hyp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTestStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_linear_on_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  first | exact @GlobalTheory.JR.Hyp.pt_linear | exact GlobalTheory.JR.Hyp.pt_linear | (intros; apply GlobalTheory.JR.Hyp.pt_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem wHyp_wS_eq_fourB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  intro F E _ _ _ _ _ A ψ x e ν μ hpt hinv hrg hcc hci hker hlc hint φ hφ y
  set p := ci A e y with hp
  have hy : y = cc A e p := (hci y).symm
  have hG : IsTest (rg A (wS A.K) (pt A ν ψ x (fun q => φ (cc A e q)))) := hrg _ (hpt _ (hcc φ hφ))
  have hh : IsTest (fun y' => φ y' * A.kerL ψ x y' (cc A e p)) :=
    ⟨hφ.1.mul (hlc _), hφ.2.mul_right⟩
  unfold wHyp
  rw [hinv _ hG]
  rw [← hp]
  conv_rhs => rw [hy]
  unfold fourB
  rw [hint _ hh]
  simp only [pt, fourB, rg, wS, hker]
  simp
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  ring

end GlobalTheory.JR.Hyp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleLStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  first | exact @GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | exact GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | (intros; apply GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem weilHyp_rg : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ Φ : A.K × A.K → ℂ, Hyp.rg A 1 Φ = Φ) ∧ ∀ (g h : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), Hyp.rg A g (Hyp.rg A h Φ) = Hyp.rg A (g * h) Φ := by
  intro F E _ _ _ _ _ A
  refine ⟨fun Φ => ?_, fun g h Φ => ?_⟩
  · funext p
    simp [Hyp.rg]
  · funext p
    have hm : ((g * h : Matrix.SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) =
        (g : Matrix (Fin 2) (Fin 2) A.K) * (h : Matrix (Fin 2) (Fin 2) A.K) := Matrix.SpecialLinearGroup.coe_mul g h
    unfold Hyp.rg
    rw [hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    congr 1
    ext <;> ring

theorem weilHyp_nS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x z : A.K) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => A.psiK ψ (z * x * (p.1 * p.2)) * Φ p) = Hyp.rg A (nS z) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν ψ x z Φ
  funext p
  simp only [Hyp.pt, Hyp.rg, nS, fourB, Hyp.kx, Et.psiK]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add]
  congr 1
  funext b
  rw [show x * b * (p.1 * z + p.2) = z * x * (p.1 * b) + x * b * p.2 by ring, map_add (f := _), AddChar.map_add_eq_mul]
  ring

theorem weil_hyperbolic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  intro F E _ _ _ _ _ A ψ hψ hK hL x μ hμ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField F E A hK hL
  obtain ⟨hci, hcc, hN, hker, hsm, hunit⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK F E A ψ hψ x
  have hνH : ν.IsAddHaarMeasure := hν.1
  have hT := GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hνH
  have hDD := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ (x : A.K) ν hν
  obtain ⟨hTcc, hTci⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e hci hcc
  obtain ⟨hTrg, hTneg, hTsc, hTmul, hTlin⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations F E A
  obtain ⟨hpsi, hkerlc⟩ := GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ
  obtain ⟨hrg1, hrgm⟩ := weilHyp_rg F E A
  have hlin := GlobalTheory.T.hyperbolicPartialFourier_linear_on_test F E A ψ hψ (x : A.K) ν hνH
  set P := Hyp.pt A ν ψ (x : A.K) with hP
  have h4 : ∀ Φ, IsTest Φ → P (P (P (P Φ))) = Φ := by
    intro Φ hΦ
    rw [hDD Φ hΦ, hDD _ (hTneg Φ hΦ)]
    funext p
    simp
  have hW : ∀ g φ, Hyp.wHyp A e ν ψ x g φ = fun y => P (P (P (Hyp.rg A g (P (fun p => φ (Hyp.cc A e p)))))) (Hyp.ci A e y) :=
    fun _ _ => rfl

  have hkey : ∀ g φ (Φ' : A.K × A.K → ℂ), IsTest Φ' → Hyp.rg A g (P (fun p => φ (Hyp.cc A e p))) = P Φ' →
      Hyp.wHyp A e ν ψ x g φ = fun y => Φ' (Hyp.ci A e y) := by
    intro g φ Φ' hΦ' h
    rw [hW, h, h4 Φ' hΦ']
  have hetaK : ∀ s : A.Kˣ, A.etaK s = 1 := by
    intro s
    have h1 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.1 (Hyp.cc A e ((s : A.K), 1)) (hunit s)
    rwa [hN, mul_one] at h1
  refine ⟨Hyp.wHyp A e ν ψ x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g φ hφ
    rw [hW]
    exact hTci _ (hT _ (hT _ (hT _ (hTrg g _ (hT _ (hTcc φ hφ))))))
  · intro φ hφ
    rw [hW, hrg1, h4 _ (hTcc φ hφ)]
    funext y
    show φ (Hyp.cc A e (Hyp.ci A e y)) = φ y
    rw [hcc]
  · intro g h φ hφ
    have hin : (fun p => Hyp.wHyp A e ν ψ x h φ (Hyp.cc A e p)) = P (P (P (Hyp.rg A h (P (fun p => φ (Hyp.cc A e p)))))) := by
      funext p
      rw [hW]
      simp only [hci]
    rw [hW (g * h) φ, hW g (Hyp.wHyp A e ν ψ x h φ), hin, h4 _ (hTrg h _ (hT _ (hTcc φ hφ))), hrgm]
  · intro g c φ φ' hφ hφ'
    have hc1 : (fun p => (c • φ + φ') (Hyp.cc A e p)) = c • (fun p => φ (Hyp.cc A e p)) + (fun p => φ' (Hyp.cc A e p)) := rfl
    have t1 := hTcc φ hφ
    have t2 := hTcc φ' hφ'
    have hrl : ∀ (Φ Φ' : A.K × A.K → ℂ), Hyp.rg A g (c • Φ + Φ') = c • Hyp.rg A g Φ + Hyp.rg A g Φ' := fun _ _ => rfl
    rw [hW, hW, hW, hc1, hlin c _ _ t1 t2, hrl, hlin c _ _ (hTrg g _ (hT _ t1)) (hTrg g _ (hT _ t2)),
      hlin c _ _ (hT _ (hTrg g _ (hT _ t1))) (hT _ (hTrg g _ (hT _ t2))),
      hlin c _ _ (hT _ (hT _ (hTrg g _ (hT _ t1)))) (hT _ (hT _ (hTrg g _ (hT _ t2))))]
    rfl
  · intro φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro z y
      have hΦ : IsTest (fun p : A.K × A.K => A.psiK ψ (z * (x : A.K) * (p.1 * p.2)) * φ (Hyp.cc A e p)) :=
        hTmul _ _ (hpsi.comp_continuous (by fun_prop)) (hTcc φ hφ)
      rw [hkey (nS z) φ _ hΦ (weilHyp_nS F E A ν ψ (x : A.K) z _).symm]
      simp only
      rw [← hN, hcc]
    · intro s y
      have hΦ : IsTest (fun p : A.K × A.K => (A.absK (s : A.K) : ℂ) * φ (Hyp.cc A e ((s : A.K) * p.1, (s : A.K) * p.2))) :=
        hTmul _ _ (IsLocallyConstant.const _) (hTsc s _ (hTcc φ hφ))
      rw [hkey (mS s) φ _ hΦ (GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction F E A ν hνH ψ (x : A.K) s (fun p => φ (Hyp.cc A e p))).symm]
      simp only
      rw [hetaK, one_mul, ← hsm, hcc]
    · intro y
      rw [one_mul]
      exact GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL F E A ψ (x : A.K) e ν μ hT hDD (fun Φ hΦ => hTrg _ Φ hΦ) hTcc hcc (hker ψ (x : A.K))
        (hkerlc (x : A.K)) (GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords F E A ψ hψ x e he hse ν μ hν hμ) φ hφ y

end GlobalTheory.JR
end
end
