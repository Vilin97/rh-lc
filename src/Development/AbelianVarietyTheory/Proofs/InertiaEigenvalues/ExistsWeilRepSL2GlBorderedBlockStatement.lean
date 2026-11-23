module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartialStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumnStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem integrable_mixedModel_partialFourier_integrand {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] {r : ℕ} (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : IsLocallyConstant (fun x => ψ x))
    (f : Gl r F → ℂ) (hf : IsTest f) (Y : Gl r F) :
    Integrable (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1))
      (Measure.pi fun _ : Fin r => μ) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : Continuous (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1)) := by
    refine Continuous.mul ?_ ?_
    · exact hf.1.continuous.comp (by fun_prop)
    · exact hψ.continuous.comp (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun Z : Gl r F => Z.2.1) '' tsupport f) := hf.2.isCompact.image (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro b hb
  have : (Y.1, b, Y.2.2.1, Y.2.2.2) ∉ tsupport f := fun h => hb ⟨_, h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.ptrB_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinearStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourier

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hψc : Continuous (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1.continuous
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  have hw : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  simp only [WeilMix.negB, WeilMix.ptrB, WeilMix.rowAct, WeilMix.rowMap, fourG, hw]
  simp
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set G : (Fin r → F) → ℂ := fun x => (∫ b', f (A, b', x, l) * ψ (b' ⬝ᵥ c) ∂μ) * ψ (x ⬝ᵥ b) with hG
  set H : (Fin r → F) → (Fin r → F) → ℂ := fun x b' => f (A, b', x, l) * ψ (b' ⬝ᵥ c) * ψ (x ⬝ᵥ b) with hH
  have hHc : Continuous (Function.uncurry H) := by
    have h1 : Continuous (fun p : (Fin r → F) × (Fin r → F) => f (A, p.2, p.1, l)) :=
      hf.1.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.2 ⬝ᵥ c)) :=
      hψc.comp (continuous_snd.dotProduct continuous_const)
    have h3 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.1 ⬝ᵥ b)) :=
      hψc.comp (continuous_fst.dotProduct continuous_const)
    exact (h1.mul h2).mul h3
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro ((hf.2.isCompact).image
      (show Continuous (fun Y : Gl r F => (Y.2.2.1, Y.2.1)) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨(A, p.2, p.1, l), subset_tsupport _ ?_, rfl⟩
    intro h0
    apply hne
    simp [Function.uncurry, H, h0]
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := hHc.integrable_of_hasCompactSupport hHs
  calc _ = ∫ x, G (-x) ∂μ := by
        congr 1; funext x; simp only [G, neg_dotProduct, neg_neg]; rfl
    _ = ∫ x, G x ∂μ := integral_neg_eq_self G μ
    _ = ∫ x, ∫ b', H x b' ∂μ ∂μ := by
        congr 1; funext x; simp only [G, H]; rw [integral_mul_const]
    _ = ∫ b', ∫ x, H x b' ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        congr 1; funext b'; congr 1; funext x
        simp only [H]
        rw [mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_comm b' c, add_comm]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourierStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mixedModel_weylElement_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  first | exact @GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | exact GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | (intros; apply GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlock

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem rowMap_mul (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring

theorem rowMap_one (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]

theorem continuous_rowMap (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop

theorem isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by
  let e : Gl r F ≃ₜ Gl r F :=
    { toFun := rowMap g, invFun := rowMap g⁻¹
      left_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      right_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }
  exact ⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩

end GlobalTheory.JR.WeilMix

open GlobalTheory.JR.WeilMix in
theorem GlobalTheory.JR.weil_repG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ
  have hW := GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        change f (A, b, (fun i => c i * 1 + u i * 0), l) *
          ψ (b ⬝ᵥ (fun i => c i * t + u i * 1)) = _
        simp only [mul_one, mul_zero, add_zero, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlockStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_weilRepSL2_glBorderedBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  first | exact @GlobalTheory.JR.weil_repG | exact GlobalTheory.JR.weil_repG | (intros; apply GlobalTheory.JR.weil_repG <;> assumption)
end
end
