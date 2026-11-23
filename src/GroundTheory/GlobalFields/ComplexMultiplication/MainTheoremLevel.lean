module

public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
public import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleActionQuotient
public import GroundTheory.GlobalFields.GlobalArtinMap.ArtinMap
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformizationClassification
import GroundTheory.GlobalFields.ComplexMultiplication.BadPrimesFinite
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesIsogeny
import GroundTheory.GlobalFields.ComplexMultiplication.GoodReductionAlmostAll
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremAssembly
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFields
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFrobenius
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremIdeles
public import GroundTheory.GlobalFields.ComplexMultiplication.Algebraicity
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionRespectsAdd
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
public import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldModels
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

-- Source module: GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremModels

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian

section ShortModel

variable {F F' : Type*} [Field F] [Field F']

theorem ofJ_map [DecidableEq F] [DecidableEq F'] (f : F →+* F') (j : F) :
    (ofJ j).map f = ofJ (f j) := by
  have h3 : (3 : F) = 0 ↔ (3 : F') = 0 := by
    rw [← map_ofNat f 3, map_eq_zero_iff f f.injective]
  have hj0 : j = 0 ↔ f j = 0 := (map_eq_zero_iff f f.injective).symm
  have hj1728 : j = 1728 ↔ f j = 1728 := by
    rw [← map_ofNat f 1728]
    exact f.injective.eq_iff.symm
  unfold ofJ
  by_cases a : j = 0
  · rw [if_pos a, if_pos (hj0.1 a)]
    by_cases b : (3 : F) = 0
    · rw [if_pos b, if_pos (h3.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt h3.2 b)]
      ext <;> simp [ofJ0]
  · rw [if_neg a, if_neg (mt hj0.2 a)]
    by_cases b : j = 1728
    · rw [if_pos b, if_pos (hj1728.1 b)]
      ext <;> simp [ofJ1728]
    · rw [if_neg b, if_neg (mt hj1728.2 b)]
      ext <;> simp [ofJNe0Or1728, map_ofNat]

theorem toShortNF_map (W : WeierstrassCurve F) [Invertible (2 : F)] [Invertible (3 : F)]
    [Invertible (2 : F')] [Invertible (3 : F')] (f : F →+* F') :
    W.toShortNF.map f = (W.map f).toShortNF := by
  ext <;> simp [toShortNF, toCharNeTwoNF, VariableChange.map, variableChange_a₂,
    VariableChange.mul_def, map_ofNat]

variable [CharZero F]

def shortModel (j : F) : WeierstrassCurve F :=
  letI : DecidableEq F := Classical.decEq F
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  (ofJ j).toShortNF • ofJ j

instance (j : F) : (shortModel j).IsElliptic := by
  unfold shortModel
  infer_instance

instance (j : F) : (shortModel j).IsShortNF := by
  unfold shortModel
  infer_instance

theorem shortModel_j (j : F) : (shortModel j).j = j := by
  unfold shortModel
  rw [variableChange_j, ofJ_j]

variable [CharZero F']

theorem shortModel_map (f : F →+* F') (j : F) : (shortModel j).map f = shortModel (f j) := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F) := invertibleOfNonzero three_ne_zero
  let _ : Invertible (2 : F') := invertibleOfNonzero two_ne_zero
  let _ : Invertible (3 : F') := invertibleOfNonzero three_ne_zero
  have e1 : shortModel j = (ofJ j).toShortNF • ofJ j := by
    unfold shortModel
    congr
  have e2 : shortModel (f j) = (ofJ (f j)).toShortNF • ofJ (f j) := by
    unfold shortModel
    congr
  rw [e1, e2, ← map_variableChange, toShortNF_map, ofJ_map]

end ShortModel

section Models

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]


include hK in
theorem exists_shortModels_isogenous (M : IntermediateField K ℂ) [FiniteDimensional K M] :
    ∃ L : IntermediateField K ℂ, M ≤ L ∧ FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ hL : ∀ x : ELL K, ELL.j x ∈ L,
        (∀ x, ∃ h : Nonempty (isogEnd ((shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ) ≃+* 𝓞 K),
          (⟨(shortModel (⟨ELL.j x, hL x⟩ : L)).baseChange ℂ, h⟩ : CMCurve K).toEll = x) ∧
        ∀ x y, Nonempty (Isogeny (shortModel (⟨ELL.j x, hL x⟩ : L))
          (shortModel (⟨ELL.j y, hL y⟩ : L))) := by
  classical
  have := finite_ell hK
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  set J : IntermediateField K ℂ := K⟮ELL.j x₀⟯
  have hJ : ∀ y, ELL.j y ∈ J := fun y ↦ ELL.j_mem_adjoin hK x₀ y
  have : FiniteDimensional K J :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  have : NumberField J := NumberField.of_module_finite K J
  set E₀ : ELL K → WeierstrassCurve J := fun y ↦ shortModel (⟨ELL.j y, hJ y⟩ : J)
  have hE₀j : ∀ y, algebraMap J ℂ (E₀ y).j = ELL.j y := fun y ↦ by
    simp only [E₀, shortModel_j]
    rfl
  have hE₀ : ∀ y, ∃ h : Nonempty (isogEnd ((E₀ y).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E₀ y).baseChange ℂ, h⟩ : CMCurve K).toEll = y := fun y ↦
    exists_cmCurve_toEll_of_j_eq y _ (by
      show ((E₀ y).map (algebraMap J ℂ)).j = _
      rw [map_j, hE₀j])
  have hF : ∀ p : ELL K × ELL K, ∃ F₁ : IntermediateField J ℂ, NumberField F₁ ∧
      Nonempty (Isogeny ((E₀ p.1).baseChange F₁) ((E₀ p.2).baseChange F₁)) := by
    rintro ⟨y, z⟩
    obtain ⟨hy, -⟩ := hE₀ y
    obtain ⟨hz, -⟩ := hE₀ z
    obtain ⟨ψ⟩ := nonempty_isogeny_of_cmCurve hK ⟨_, hy⟩ ⟨_, hz⟩
    obtain ⟨F₁, hF₁, φ, -⟩ := Isogeny.exists_numberField_mapOf_eq ψ
    exact ⟨F₁, hF₁, ⟨φ⟩⟩
  choose F hFnum hFiso using hF
  have hFfin : ∀ p, FiniteDimensional K ((F p).restrictScalars K) := fun p ↦ by
    have := hFnum p
    have : FiniteDimensional ℚ ((F p).restrictScalars K) := (inferInstance : FiniteDimensional ℚ (F p))
    exact Module.Finite.of_restrictScalars_finite ℚ K ((F p).restrictScalars K)
  set M' : IntermediateField K ℂ := M ⊔ J ⊔ ⨆ p, (F p).restrictScalars K
  have : FiniteDimensional K M' := by
    have := hFfin
    infer_instance
  obtain ⟨L, hM'L, hLfin, hLgal⟩ := exists_isGalois_le M'
  have hJL : J ≤ L := le_trans (le_trans le_sup_right le_sup_left) hM'L
  have hFL : ∀ p, (F p).restrictScalars K ≤ L := fun p ↦
    le_trans (le_trans (le_iSup (fun p ↦ (F p).restrictScalars K) p) le_sup_right) hM'L
  set ι : J →+* L := (inclusion hJL).toRingHom
  have hmodel : ∀ y, (E₀ y).map ι = shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L) := fun y ↦ by
    rw [shortModel_map]
    rfl
  refine ⟨L, le_trans (le_trans le_sup_left le_sup_left) hM'L, hLfin, hLgal, fun y ↦ hJL (hJ y),
    fun y ↦ ?_, fun y z ↦ ?_⟩
  · refine exists_cmCurve_toEll_of_j_eq y _ ?_
    show ((shortModel (⟨ELL.j y, hJL (hJ y)⟩ : L)).map (algebraMap L ℂ)).j = _
    rw [map_j, shortModel_j]
    rfl
  · obtain ⟨φ⟩ := hFiso (y, z)
    let κ : F (y, z) →+* L := (inclusion (hFL (y, z))).toRingHom
    have hκ : κ.comp (algebraMap J (F (y, z))) = ι := by
      ext a
      rfl
    have e : ∀ w, ((E₀ w).baseChange (F (y, z))).map κ = shortModel (⟨ELL.j w, hJL (hJ w)⟩ : L) :=
      fun w ↦ by
        show ((E₀ w).map (algebraMap J (F (y, z)))).map κ = _
        rw [WeierstrassCurve.map_map, hκ, hmodel]
    exact ⟨(φ.map κ).congr (e y) (e z)⟩

end Models

end

end Elliptic
end GroundTheory.Global
end
end

-- Source module: GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremLevel

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
  IntermediateField
open GroundTheory.LocalField (maximalAbelianExtension)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] in
theorem exists_isogeny_homConstSet_congr {L : Type} [Field L] [Algebra L ℂ]
    {A A' B B' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic] [B.IsElliptic] [B'.IsElliptic]
    (eA : A = A') (eB : B = B') {S : Set ℂ}
    (h : ∃ φ : Isogeny A B, (homConstSet (A.baseChange ℂ) (B.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S) :
    ∃ φ : Isogeny A' B', (homConstSet (A'.baseChange ℂ) (B'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S := by
  subst eA eB
  exact h

omit [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra K ℂ] in
theorem nonempty_isogEnd_congr {L : Type} [Field L] [Algebra L ℂ] {B B' : WeierstrassCurve L}
    [B.IsElliptic] [B'.IsElliptic] (e : B = B') (h : Nonempty (isogEnd (B.baseChange ℂ) ≃+* 𝓞 K)) :
    Nonempty (isogEnd (B'.baseChange ℂ) ≃+* 𝓞 K) := by
  subst e
  exact h


include hK in
theorem exists_uniformization_level (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical

  have hL₁ := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hL₁end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hf₁ := hf
  rw [← hL₁] at hf₁
  obtain ⟨C₁, hC₁, -⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  have hEend : Nonempty (isogEnd E ≃+* 𝓞 K) :=
    ⟨(vcEndEquiv C₁ hC₁).symm.trans (CMCurve.ofLattice (algebraMap K ℂ) _ hL₁end).endIso.some⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ELL K, x₀ = (⟨E, hEend⟩ : CMCurve K).toEll := ⟨_, rfl⟩
  have hx₀ell : x₀ = ellOf (algebraMap K ℂ) _ hL₁end := by
    rw [hx₀]
    exact (CMCurve.toEll_eq_iff _ _).2 ⟨C₁⁻¹, inv_smul_eq_of_smul_eq C₁ hC₁⟩
  have hjE : ELL.j x₀ = E.j := by
    rw [hx₀]
    exact ELL.j_toEll _

  have hJfin : FiniteDimensional K K⟮ELL.j x₀⟯ :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  set aJ : K⟮ELL.j x₀⟯ := ⟨ELL.j x₀, mem_adjoin_simple_self K _⟩
  obtain ⟨M₁, hM₁fin, -, htorsJ⟩ := exists_le_forall_torsion_mem K⟮ELL.j x₀⟯ (shortModel aJ) hm

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ))
  have hζ : IsPrimitiveRoot ζ 12 := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  have hM₃fin : FiniteDimensional K K⟮ζ⟯ :=
    adjoin.finiteDimensional ((hζ.isIntegral (by norm_num)).tower_top)

  obtain ⟨L, hML, hLfin, hLgal, hL, hE, hiso⟩ := exists_shortModels_isogenous hK
    (M₁ ⊔ (Modulus.ofNat (K := K) m hm).rayClassField ℂ ⊔ K⟮ζ⟯)
  have : NumberField L := NumberField.of_module_finite K L
  have hM₁L : M₁ ≤ L := le_trans (le_trans le_sup_left le_sup_left) hML
  have hM₂L : (Modulus.ofNat (K := K) m hm).rayClassField ℂ ≤ L :=
    le_trans (le_trans le_sup_right le_sup_left) hML
  have hζL : ζ ∈ L := hML (le_sup_right (a := M₁ ⊔ _) (mem_adjoin_simple_self K ζ))
  have hζL' : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) 12 :=
    (IsPrimitiveRoot.map_iff_of_injective (algebraMap L ℂ).injective).1 hζ

  obtain ⟨A, hAdef⟩ : ∃ A : WeierstrassCurve L, A = shortModel (⟨ELL.j x₀, hL x₀⟩ : L) := ⟨_, rfl⟩
  have : A.IsElliptic := by rw [hAdef]; infer_instance
  have : A.IsShortNF := by rw [hAdef]; infer_instance
  have hAℂ : A.baseChange ℂ = (shortModel aJ).baseChange ℂ := by
    rw [hAdef, WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, shortModel_map, shortModel_map]
    rfl
  obtain ⟨V₀, hV₀⟩ := exists_variableChange_of_j_eq E (A.baseChange ℂ) (by
    rw [j_congr hAℂ]
    show E.j = ((shortModel aJ).map (algebraMap _ ℂ)).j
    rw [map_j, shortModel_j, ← hjE]
    rfl)
  have htors : ∀ (a b : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular a b),
      m • (Point.some a b h : (A.baseChange ℂ).toAffine.Point) = 0 →
        a ∈ (algebraMap L ℂ).range ∧ b ∈ (algebraMap L ℂ).range := by
    intro a b h hP
    have h' : ((shortModel aJ).baseChange ℂ).toAffine.Nonsingular a b := hAℂ ▸ h
    have hP' : m • (Point.some a b h' : ((shortModel aJ).baseChange ℂ).toAffine.Point) = 0 :=
      nsmul_some_congr hAℂ h h' hP
    obtain ⟨ha, hb⟩ := htorsJ a b h' hP'
    exact ⟨⟨⟨a, hM₁L ha⟩, rfl⟩, ⟨⟨b, hM₁L hb⟩, rfl⟩⟩

  have hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (σ.restrictNormal L a) :=
    fun a ↦ (AlgEquiv.restrictNormal_commutes σ L a).symm

  obtain ⟨S₀, hS₀, hS₀p⟩ := frobenius_at_primes_of_degree_one hK hL
    (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L)) hE hiso
  have hgood : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L w), W.IsElliptic ∧
        W.map (algebraMap (localizationAt L w) L) = A ∧ (W.a₄ = 0 ∨ IsUnit W.a₄) ∧
          (W.a₆ = 0 ∨ IsUnit W.a₆) := by
    have h4 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₄ = 0 ∨ ∃ h : A.a₄ ∈ localizationAt L w, IsUnit (⟨A.a₄, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₄ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    have h6 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₆ = 0 ∨ ∃ h : A.a₆ ∈ localizationAt L w, IsUnit (⟨A.a₆, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₆ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    filter_upwards [eventually_exists_model A, h4, h6] with w ⟨W, hW, hWA⟩ h4w h6w
    have e4 : algebraMap (localizationAt L w) L W.a₄ = A.a₄ := by rw [← hWA]; rfl
    have e6 : algebraMap (localizationAt L w) L W.a₆ = A.a₆ := by rw [← hWA]; rfl
    refine ⟨W, hW, hWA, ?_, ?_⟩
    · rcases h4w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e4.trans h0)
      · right
        have : W.a₄ = ⟨A.a₄, h⟩ := Subtype.ext e4
        rwa [this]
    · rcases h6w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e6.trans h0)
      · right
        have : W.a₆ = ⟨A.a₆, h⟩ := Subtype.ext e6
        rwa [this]
  obtain ⟨S₁, hS₁, hS₁p⟩ := exists_finite_forall_liesOver (K := K) hgood
  have h6m : ((6 * m : ℕ) : 𝓞 K) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    omega
  have hS : (S₀ ∪ S₁ ∪ {v : HeightOneSpectrum (𝓞 K) | ((6 * m : ℕ) : 𝓞 K) ∈ v.asIdeal}).Finite :=
    (hS₀.union hS₁).union (finite_setOf_mem_asIdeal h6m)

  obtain ⟨𝔭, h𝔭S, h𝔭1, 𝔓, hlies, -, hfrob⟩ := exists_isArithFrobAt L (σ.restrictNormal L) hS
  have : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hlies
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at h𝔭S
  obtain ⟨⟨h𝔭S₀, h𝔭S₁⟩, h𝔭6m⟩ := h𝔭S
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun h ↦ h𝔭6m (by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  have hnorm : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.absNorm_mem _
  have h5 : 5 ≤ Ideal.absNorm 𝔭.asIdeal := by
    refine hv.five_le_of_ne_two_of_ne_three (fun h2 ↦ h𝔭6m ?_) (fun h3 ↦ h𝔭6m ?_)
    · rw [h2] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) * ((3 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm
    · rw [h3] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((3 : ℕ) : 𝓞 K) * ((2 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm

  obtain ⟨-, hcls, -⟩ := hS₀p 𝔭 h𝔭S₀ h𝔭1 𝔓
  obtain ⟨-, hτj⟩ := hcls (σ.restrictNormal L) hfrob
  have hAτ : A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L) = shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L) := by
    rw [hAdef, shortModel_map]
    congr 1
    exact hτj x₀

  have hφex : ∃ φ : Isogeny A (A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)),
      (homConstSet (A.baseChange ℂ) ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) :
        Set ℂ) = (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L))
      hE hiso 𝔭 x₀
    exact exists_isogeny_homConstSet_congr hAdef.symm hAτ.symm ⟨φ, hφ⟩
  obtain ⟨φ, hφ⟩ := hφex
  have hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K) :=
    nonempty_isogEnd_congr hAdef.symm (hE x₀).1
  have hEA' : Nonempty (isogEnd ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) ≃+*
      𝓞 K) :=
    nonempty_isogEnd_congr hAτ.symm (hE _).1

  obtain ⟨W, hW, hWA, ha₄, ha₆⟩ := hS₁p 𝔭 h𝔭S₁ 𝔓 hlies
  have : W.IsShortNF := by
    have hinj : Function.Injective (algebraMap (localizationAt L 𝔓) L) := Subtype.val_injective
    refine ⟨hinj ?_, hinj ?_, hinj ?_⟩ <;> rw [map_zero]
    · rw [← a₁_of_isShortNF A, ← hWA]; rfl
    · rw [← a₂_of_isShortNF A, ← hWA]; rfl
    · rw [← a₃_of_isShortNF A, ← hWA]; rfl

  obtain ⟨D, hD, hDφ⟩ := exists_vcPoint_pointHomOver_eq hK 𝔭 hv h5 𝔓 hfrob hEA hEA' φ hφ hWA ha₄ ha₆
    hζL' hm𝔭

  obtain ⟨x, hx⟩ := exists_diagonal_of_isArithFrobAt m hm σ s hs 𝔭 hm𝔭 L hM₂L 𝔓 hfrob

  have hL₂ := lattice_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hL₂end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hsmul := classGroup_smul_ellOf (algebraMap K ℂ) hK _ _ hL₁end hL₂end (primeIdealUnit 𝔭)
    (by rw [hL₂, hL₁, Units.val_mul, idealLattice_mul])
  have hcl : primeClass 𝔭 = ClassGroup.mk K (primeIdealUnit 𝔭) := by
    rw [primeClass, ← classGroup_mk_primeUnit]
    rfl
  have hyL₂ : (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀ =
      ellOf (algebraMap K ℂ) _ hL₂end := by
    rw [hcl, hx₀ell, hsmul]
  have hjV' : (weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞))).j =
      ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ).j := by
    rw [j_congr (congrArg (fun B : WeierstrassCurve L ↦ B.baseChange ℂ) hAτ)]
    show _ = ((shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L)).map (algebraMap L ℂ)).j
    rw [map_j, shortModel_j]
    show _ = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀)
    set_option backward.isDefEq.respectTransparency false in
      rw [hyL₂, ellOf, ELL.j_toEll]
    exact j_congr rfl
  obtain ⟨V', hV'⟩ := exists_variableChange_of_j_eq _ _ hjV'
  exact exists_uniformization_of_data hK σ s 𝔞 hf (σ.restrictNormal L) hτσ V₀ hV₀ htors 𝔭 x
    (hx 𝔞).1 (hx 𝔞).2 φ hφ D hD hDφ V' hV'

end

end Elliptic
end GroundTheory.Global
end
end
