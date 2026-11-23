module

public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ArchimedeanHypothesisLowerBoundCmPointStatement
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaLineDegreeAndHeightLowerBoundStatement
public import ReciprocityTheory.SemistableReduction.LemmaH
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrame
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis

section

@[expose] public section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder

theorem dot_basis_vector_diag {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (j : Fin k) :
    star ((1 : Matrix (Fin k) (Fin k) ℂ) j) ⬝ᵥ (M *ᵥ (1 : Matrix (Fin k) (Fin k) ℂ) j) = M j j := by
  simp [dotProduct, mulVec, Matrix.one_apply]

section Gram

variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}

theorem gramBlock_eq (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) :
    gramBlock e U H σ b = (((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ)ᴴ * H *
      ((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ := by
  rw [Matrix.mul_assoc]
  ext j j'
  simp [gramBlock, Matrix.mul_apply, dotProduct, mulVec, ReciprocityTheory.MultiplicativeHeights.embVec]

theorem gramBlock_posDef (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K)
    (H : Matrix (Fin g) (Fin g) ℂ) (σ : K →+* ℂ) (b : B) (hH : H.PosDef) (hU : U.det ≠ 0) :
    (gramBlock e U H σ b).PosDef := by
  classical
  rw [gramBlock_eq]
  refine hH.conjTranspose_mul_mul_same ?_
  rw [Matrix.mulVec_injective_iff]
  have hdet : (U.map σ).det ≠ 0 := by
    rw [show U.map σ = σ.mapMatrix U from rfl, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hU
  have hli : LinearIndependent ℂ (U.map σ).row :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hinj : Function.Injective (fun j : Fin (m b) => e ⟨b, j⟩) := fun j j' h =>
    eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2
  exact hli.comp _ hinj

theorem hermitian_form_gramBlock_basis (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) (j : Fin (m b)) :
    ReciprocityTheory.MultiplicativeHeights.hq (gramBlock e U H σ b) ((1 : Matrix (Fin (m b)) (Fin (m b)) ℂ) j) =
      ReciprocityTheory.MultiplicativeHeights.hq H (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j⟩))) := by
  simp only [ReciprocityTheory.MultiplicativeHeights.hq, dot_basis_vector_diag]
  rfl

end Gram

end Formalism.L2.LamCM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundOfCoefficientBound

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmLowerBound_of_coeffBound :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hLK hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundOfCoefficientBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

theorem _root_.GlobalTheory.T.cmPoint_lower_bound_of_coefficient_bound : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.cmLowerBound_of_coeffBound | exact GlobalTheory.cmLowerBound_of_coeffBound | (intros; apply GlobalTheory.cmLowerBound_of_coeffBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundFree

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmPoint_lowerBound_free :
    ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) :=
  GlobalTheory.T.cmPoint_lower_bound_of_coefficient_bound GlobalTheory.T.thetaLine_degree_and_heightLowerBound.2 ReciprocityTheory.MultiplicativeHeights.lemmaH_holds

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_good_cmPoint_at_cmBasis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ (z : CMPt Xo c) (σ₁ : z.K →ₐ[c.F] CAt c.F.val.toRingHom), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ₁.toRingHom ≫ z.y.x = (U.un k x₀).x := by
  first | exact @GlobalTheory.LamT.exists_good_cmPt_at_frame | exact GlobalTheory.LamT.exists_good_cmPt_at_frame | (intros; apply GlobalTheory.LamT.exists_good_cmPt_at_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.localLowerBound_cmPoint_framePolynomial_every_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  first | exact @GlobalTheory.LamT.LocClause.step5Loc_cmPt | exact GlobalTheory.LamT.LocClause.step5Loc_cmPt | (intros; apply GlobalTheory.LamT.LocClause.step5Loc_cmPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem letters_lines {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
    {c : Coeff l} {nΨ n' f : ℕ} {o : LamF.LamObj c nΨ n'} {La t : ℝ} (hG : LamF.LamObjGood o f La)
    (L : LamF.LamLetters o) (hL : L.IsGood)
    (hdeg : (∀ k, (o.ℓΨ k).ndeg = t / 2) ∧ ∀ k, (o.ℓ' k).ndeg = t / 2) :
    (∀ k, (L.ℓ k).Good) ∧ ∀ k, (L.ℓ k).ndeg = t / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  · have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2

theorem meanLogSup_lowerBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → (∀ σ, 0 < supC Xo c U ξ (goodOf c σ) a n F) → ∀ (k : (U c.F.val.toRingHom).Comp) (x₀ : ((U c.F.val.toRingHom).X k).dom) (Xx : FD.DataX E r) (hX : Xx.toData = (U c.F.val.toRingHom).X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), 1 ≤ La → FD.LamBasis Xx La (hX ▸ x₀.1) lam → rdU (U c.F.val.toRingHom) F k x₀.1 ≠ 0 → -((pDeg (logOm E χ).re + (1 / 2) * Real.log La) * (((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * r : ℕ) : ℝ) * n)) - ((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U ξ (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq _ χ hχ a n hd F hF hint hpos k x₀ Xx hX 𝔄 h𝔄 hΛ La lam hLa hB hne
  classical
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hgood : GoodEmb c c.F.val.toRingHom := rfl
  have hU0 := hU _ hgood
  have hr : r = Dw.p + Dw.q := hU0.1
  have hFs : F ∈ sec Xo c a n := cusp_le_sec Xo c U a n hF
  obtain ⟨z, σ₁, hz, hx⟩ := GlobalTheory.T.exists_good_cmPoint_at_cmBasis_frame E H Dw l Xo c hstar r _ hU0 (by omega) k x₀ Xx hX 𝔄 h𝔄 hΛ La lam hB
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_isFramePolynomialOfRule_numberField E H Dw l Xo c z.K z.y a n F hFs
  have hev : evR Xo c F ((U c.F.val.toRingHom).un k x₀) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x₀.1 ∈ ((U c.F.val.toRingHom).X k).dom then
      toC (evR Xo c F ((U c.F.val.toRingHom).un k ⟨x₀.1, h⟩)) else 0) = 0
    rw [dite_eq_left x₀.2]
    exact h0
  have hG0 : G ≠ 0 := (GlobalTheory.T.framePolynomial_equivariant_and_ne_zero E H Dw l Xo c z.K z.y a n F hFs G hG).2 _ σ₁ _ hx hev
  have hloc := GlobalTheory.T.localLowerBound_cmPoint_framePolynomial_every_prime E H Dw l Xo c z _ La hz a n F hFs hint G hG
  have harch := GlobalTheory.T.archimedeanHypothesis_lowerBound_cmPoint E H Dw l Xo c r U ξ hU hξ hpq z _ La hz a n hd F hF G hG
  obtain ⟨hGood, hL, -⟩ := hz
  have hdeg := LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H χ hχ l c hstar _ _ _ z.obj La hGood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ z.obj La hGood z.letters hL
  obtain ⟨hlg, hnd⟩ := letters_lines hGood z.letters hL hdeg
  obtain ⟨-, -, -, -, -, -, -, -, hgB, -, -, -, -, -, -, -, -, -, hTg, hLg, hkl, hka, -⟩ := hGood
  have hmr : ∀ b, Dw.mult b ≤ r := by
    intro b
    unfold Datum.mult
    split_ifs <;> omega
  have h5 := GlobalTheory.cmPoint_lowerBound_free z.K z.Φ.key z.Tl z.LamL (E →+* ℂ) Dw.mult z.e z.ℓ z.U G
    (fun b i => a (b, i)) n r La (logOm E χ).re
    (fun σ => supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F) hTg hLg hkl hka hlg hnd hdet hG0 hLa
    (by omega) hmr (fun σ => hpos _) hloc harch
  have h2 := Formalism.L2.Pj.abelian₂.mean_restrict (K := c.F) (L := z.K)
    (fun τ => Real.log (supC Xo c U ξ (goodOf c τ) a n F))
  beta_reduce at h5 h2
  rw [h2] at h5
  have hg : z.Φ.key.P.g = Module.finrank ℚ E / 2 * r := by rw [hr]; exact hgB
  rw [hg] at h5
  exact h5

end GlobalTheory.LamT
end
end
