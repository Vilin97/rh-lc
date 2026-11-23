module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamiliesStatement
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.DataParams
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrimeStatement

section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.signs_and_jump_sets_at_type_prime : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  first | exact @GlobalTheory.HostJumpSets.main | exact GlobalTheory.HostJumpSets.main | (intros; apply GlobalTheory.HostJumpSets.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant

section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HubXTypePrimeConditions

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace UpperTheory.GalS
theorem noLgc_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial
theorem hubX_typePrime_conditions_alt : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.ConclusionG5 D → _root_.UpperTheory.GalS.NoCondition D → GlobalTheory.HubX.DepthZeroG D → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro D L HW R X hX P hJ hadm hG5 hLgc hDZ CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hadm' : L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := hadm
  have hb : 1 ≤ L.sc.b := by linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.b := by linarith
  obtain ⟨hnum1, hnum2, hnum3⟩ := GlobalTheory.typePrime_exceeds_constant D L P (by linarith) hb CT hCT
  obtain ⟨hJa, hJb, hJc, -, hJe, -, -⟩ := hJ
  have hJaAt : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D (GlobalTheory.HubX.epJ D) := by
    rw [GlobalTheory.HubX.epJ_eq hJa]; exact hJa.choose_spec
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hX.fam.good
  have hpt := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hX.fam
  rw [hX.eta]
  refine ⟨fun i k _ hk hHG => ⟨hgood i, fun π hπ => ⟨(hpt i π hπ).1, (hpt i π hπ).2.1⟩, ?_⟩, hnum2⟩
  obtain ⟨sg, U, hsg, hU⟩ := GlobalTheory.T.signs_and_jump_sets_at_type_prime D L (GlobalTheory.HubX.epJ D) hJaAt hJb hJc hJe ht i k (X.r i) hk (hgood i)
  refine ⟨⌊3 * L.sc.b⌋₊ + 2, 0, sg, U, hnum1, hnum3 k, hsg, hU⟩
end UpperTheory.GalS
end
end
end
