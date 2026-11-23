module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMatrixCoeffIsotropicEqMulMean
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | (intros; apply GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_isotropicSandwichMean_translation : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  first | exact @GlobalTheory.IsoMean.continuous_meanX | exact GlobalTheory.IsoMean.continuous_meanX | (intros; apply GlobalTheory.IsoMean.continuous_meanX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwichStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_complement_isotropic_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  first | exact @GlobalTheory.IsoCompl.ratCompl | exact GlobalTheory.IsoCompl.ratCompl | (intros; apply GlobalTheory.IsoCompl.ratCompl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRationalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  first | exact @GlobalTheory.IsoMean.integrable_coef | exact GlobalTheory.IsoMean.integrable_coef | (intros; apply GlobalTheory.IsoMean.integrable_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMatrixCoeffIsotropicEqMulMeanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_matrixCoeff_isotropic_eq_mul_mean : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → (∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∫ y, (∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ = κ * ∫ z in 𝓩, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (GlobalTheory.IsoMean.cplx V W B z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (GlobalTheory.IsoMean.cplx V W B z)) ∂η := by
  first | exact @GlobalTheory.IsoMean.integral_coef_eq_mul_meanX | exact GlobalTheory.IsoMean.integral_coef_eq_mul_meanX | (intros; apply GlobalTheory.IsoMean.integral_coef_eq_mul_meanX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProducts

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem meanX_prod_zero_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  intro D V W a b P Q hP hQ hiso ψ hψ μ 𝓨 hμ F₁ F₁' F₂ F₂' h₁ h₁' h₂ h₂' H
  obtain ⟨k, B, horth, hdec, huniq, hrat, hsep⟩ := GlobalTheory.T.exists_rational_complement_isotropic_sandwich D V W a b P Q hP hQ hiso ψ hψ
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  obtain ⟨η, 𝓩, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 k
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 := hμ
  have hν2 : IsAddFundamentalDomain (ratL W V) 𝓕 ν := hν.2.1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.integral_matrixCoeff_isotropic_eq_mul_mean D V W a b P Q hP hQ hiso k B horth hdec huniq hrat ψ hψ μ 𝓨 hμ' η 𝓩 hη.1 hη.2.1 ν 𝓕
    hν.1 hν2 (GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational D V W a b P Q hP hQ hiso ψ hψ μ hμ.1 ν 𝓕 hν.1 hν2)
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set ι := GlobalTheory.IsoMean.cplx V W B with hι
  have hιrat : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ι c ∈ ratL W V := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ V W

  have hcomp : ∀ (w ξ : WO V W), symplOH V W ξ w = 0 → ∀ G : WO V W → ℂ,
      heisO ψ V W (w + ξ) G = heisO ψ V W ξ (heisO ψ V W w G) := by
    intro w ξ h G
    funext u
    simp only [heisO]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, l2, l1, h, add_zero, add_comm (symplOH V W u w),
      show u + ξ + w = u + (w + ξ) by abel]

  have hcoef : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∫ y, (∫ u in 𝓕, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplO V W (ι z) (ι c)) *
          (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have e1 : ∀ y, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G =
        heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) (heisO ψ V W (ι c) G) := fun y =>
      hcomp _ _ (by rw [skew, hH0 _ _ (horth c y), neg_zero]) G
    simp only [e1]
    rw [hU _ G' (hT hG (ι c)) hG']
    congr 1
    congr 1
    funext z
    rw [GlobalTheory.IsoMean.meanX_heisO_rat V W P Q μ 𝓨 ψ G hG (ι c) (hιrat c hc) (horth c) (ι z) (horth z)]
    ring
  set g : (WO V W → ℂ) → (WO V W → ℂ) → Mx D 1 k → ℂ := fun G G' z =>
    GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z)) with hg
  have hιc : Continuous ι := GlobalTheory.IsoMean.continuous_cplx V W B
  have hgc : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (g G G') :=
    fun G G' hG hG' => ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G hG).comp hιc).mul
      ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G' hG').comp hιc).star
  have hgp : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ z, g G G' (γ + z) = g G G' z := by
    intro G G' hG hG' γ hγ z
    simp only [hg]
    rw [show ι (γ + z) = ι γ + ι z from GlobalTheory.IsoMean.cplx_add V W B γ z]
    exact GlobalTheory.IsoMean.meanX_mul_star_rat V W P Q μ 𝓨 ψ hψ G G' hG hG' (ι γ) (hιrat γ hγ) (horth γ) (ι z)
  have hχ1 : ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (ι γ) (ι c)) = 1 :=
    fun γ hγ => (hsep γ).2 hγ
  have hchar : ∀ c z z', ψ (symplO V W (ι (z + z')) (ι c)) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z') (ι c)) := by
    intro c z z'
    rw [show ι (z + z') = ι z + ι z' from GlobalTheory.IsoMean.cplx_add V W B z z', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l1, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hchar2 : ∀ c c' z, ψ (symplO V W (ι z) (ι (c + c'))) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z) (ι c')) := by
    intro c c' z
    rw [show ι (c + c') = ι c + ι c' from GlobalTheory.IsoMean.cplx_add V W B c c', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l2, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hχc : ∀ c, Continuous fun z => ψ (symplO V W (ι z) (ι c)) := by
    intro c
    have h := (GlobalTheory.FinTranslate.continuous_symplOH V W (ι c)).comp hιc
    have e : (fun z => ψ (symplO V W (ι z) (ι c))) = fun z => ψ (symplOH V W (ι z) (ι c) + symplOH V W (ι z) (ι c)) := by
      funext z; rw [GlobalTheory.IsoMean.symplO_eq_add]
    rw [e]
    exact hψ.1.1.comp (h.add h)
  have hint : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      IntegrableOn (fun z => ψ (symplO V W (ι z) (ι c)) * g G G' z) 𝓩 η := by
    intro c hc G G' hG hG'
    refine GlobalTheory.MixModel.covolOne_integrableOn hη _ ((hχc c).mul (hgc G G' hG hG')) fun γ hγ z => ?_
    rw [hchar, hχ1 γ hγ c hc, one_mul, hgp G G' hG hG' γ hγ z]
  have key := GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero (Mx D 1 k) (GlobalTheory.MixModel.ratMx D 1 k) K hK hKc (GlobalTheory.MixModel.ratMx D 1 k)
    (fun c z => ψ (symplO V W (ι z) (ι c))) (fun c => hχc c) (fun c z z' => hchar c z z')
    (fun c c' z => by exact hchar2 c c' z)
    (fun z => by
      show ψ (symplO V W (ι z) (ι 0)) = 1
      have h0 : symplOH V W (ι z) 0 = 0 := by
        have h := l2 (ι z) 0 0
        rw [add_zero] at h
        linear_combination -h
      rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B, GlobalTheory.IsoMean.symplO_eq_add, h0, add_zero,
        AddChar.map_zero_eq_one])
    (fun c z => hψ.1.2.1 _)
    (fun z => by rw [← hsep z]; exact Subtype.forall)
    η 𝓩 hη.1 hη.2.1 (fun z => g F₁ F₁' z - g F₂ F₂' z) ((hgc F₁ F₁' h₁ h₁').sub (hgc F₂ F₂' h₂ h₂'))
    (fun γ hγ z => by simp only [hgp F₁ F₁' h₁ h₁' γ hγ z, hgp F₂ F₂' h₂ h₂' γ hγ z])
    (fun c => by
      have e1 := hcoef c c.2 F₁ F₁' h₁ h₁'
      have e2 := hcoef c c.2 F₂ F₂' h₂ h₂'
      have e3 := H ν 𝓕 hν.1 hν2 (ι c) (horth c)
      rw [e1, e2] at e3
      have e4 := mul_left_cancel₀ hκ e3
      simp only [mul_sub]
      rw [integral_sub (hint c c.2 F₁ F₁' h₁ h₁') (hint c c.2 F₂ F₂' h₂ h₂')]
      exact sub_eq_zero.2 e4)
  have e := congrFun key 0
  simp only [Pi.zero_apply, hg] at e
  rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B] at e
  exact sub_eq_zero.1 e

end GlobalTheory.IsoMean

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProductsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  first | exact @GlobalTheory.IsoMean.meanX_prod_zero_eq | exact GlobalTheory.IsoMean.meanX_prod_zero_eq | (intros; apply GlobalTheory.IsoMean.meanX_prod_zero_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialAction

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IsoMean

theorem GlobalTheory.IsoMean.meanX_prod_zero : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f) 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 (ω (g, h) f') 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 f' 0) := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip f f' hf hf'
  exact GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products D V W a b P Q hP hQ hiso ψ hω.std μ 𝓨 hμ _ _ _ _ (hω.om_pres _ f hf) (hω.om_pres _ f' hf') hf hf'
    (fun ν 𝓕 hν h𝓕 w hw => GlobalTheory.IsoMean.coef_integral_eq D V W a b P Q ψ χS χT ω hω μ hμ.1 g h hfix hunip ν 𝓕 hν h𝓕 f f'
      hf hf' w hw)

namespace GlobalTheory.IsoMean

theorem mean_scalar : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (HMul.hMul (HMul.hMul (P.map (incA D)) (y' : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (ratMx D a b) μ 𝓨 → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∃ y : Mx D a b, actO V W g h x = x + (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D))) → ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) = 0) → ∫ y in 𝓨, heisO ψ V W x (ω (g, h) f) (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = (c : ℂ) * ∫ y in 𝓨, heisO ψ V W x f (HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
  change ∀ y y' : Mx D a b, symplO V W (emb V W P Q y) (emb V W P Q y') = 0 at hiso
  change ∀ y : Mx D a b, actO V W g h (emb V W P Q y) = emb V W P Q y at hfix
  change ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (emb V W P Q y) = 0) →
    ∃ y : Mx D a b, actO V W g h x = x + emb V W P Q y at hunip
  have hψ := hω.std
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  have phase : ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀ y,
      symplOH V W (emb V W P Q y) (x + emb V W P Q y₀) = 0 := fun x hx y₀ y => by
    rw [l2, skew, hH _ _ (hx y), hH _ _ (hiso y y₀), neg_zero, add_zero]

  have hint : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      ∫ y in 𝓨, heisO ψ V W x F (emb V W P Q y) ∂μ = meanX V W P Q μ 𝓨 F x := fun F x hx => by
    unfold meanX heisO
    congr 1; funext y
    have := phase x hx 0 y
    rw [show emb V W P Q (0 : Mx D a b) = 0 by simp [emb], add_zero] at this
    rw [this, AddChar.map_zero_eq_one, one_mul]
  have hmean : ∀ (F : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) → ∀ y₀,
      meanX V W P Q μ 𝓨 (heisO ψ V W (x + emb V W P Q y₀) F) 0 = meanX V W P Q μ 𝓨 F (x + emb V W P Q y₀) :=
    fun F x hx y₀ => by
      unfold meanX heisO
      congr 1; funext y
      rw [add_zero, phase x hx y₀ y, AddChar.map_zero_eq_one, one_mul]
  have hz : emb V W P Q (0 : Mx D a b) = 0 := by simp [emb]

  have hωx : ∀ f, IsThetaFunO ψ V W f → ∀ x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (ω (g, h) (heisO ψ V W x f)) 0 = meanX V W P Q μ 𝓨 (ω (g, h) f) x := fun f hf x hx => by
    obtain ⟨y₀, hy₀⟩ := hunip x hx
    rw [hω.om_heis g h x f hf, hy₀, hmean _ x hx y₀, add_comm,
      GlobalTheory.IsoMean.meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ _ (hω.om_pres _ f hf) x hx y₀]
  have hfx : ∀ (f : WO V W → ℂ) x, (∀ y, symplO V W x (emb V W P Q y) = 0) →
      meanX V W P Q μ 𝓨 (heisO ψ V W x f) 0 = meanX V W P Q μ 𝓨 f x := fun f x hx => by
    have := hmean f x hx 0
    rwa [hz, add_zero] at this
  let Ix := {p : (WO V W → ℂ) × WO V W // IsThetaFunO ψ V W p.1 ∧ ∀ y, symplO V W p.2 (emb V W P Q y) = 0}
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul (X := Ix)
    (fun p => meanX V W P Q μ 𝓨 p.1.1 p.1.2) (fun p => meanX V W P Q μ 𝓨 (ω (g, h) p.1.1) p.1.2)
    (fun p q => by
      have e := meanX_prod_zero D V W a b P Q hP hQ hiso ψ χS χT ω hω μ 𝓨 hμ g h hfix hunip
        (heisO ψ V W q.1.2 q.1.1) (heisO ψ V W p.1.2 p.1.1)
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ q.2.1 _) (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ p.2.1 _)
      rwa [hωx _ q.2.1 _ q.2.2, hωx _ p.2.1 _ p.2.2, hfx _ _ q.2.2, hfx _ _ p.2.2] at e)
  refine ⟨⟨c, ?_⟩, fun f hf x hx => ?_⟩
  · show c ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.2 hc
  · have e := congrFun hcf ⟨(f, x), hf, hx⟩
    simp only [Pi.smul_apply, smul_eq_mul] at e
    exact (hint (ω (g, h) f) x hx).trans (e.trans (congrArg _ (hint f x hx).symm))

end GlobalTheory.IsoMean

end
end
end
