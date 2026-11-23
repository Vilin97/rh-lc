module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAvgLinear
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfPartEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTranslate

section

namespace I195MixedCoordinates_35474aefd184915ecb24a8bf

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_35474aefd184915ecb24a8bf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfInvariance

theorem integral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] (F : G → ℂ) (a : G) :
    ∫ x, F (x + a) ∂ν = ∫ x, F x ∂ν := by
  simp_rw [add_comm _ a]
  exact integral_add_left_eq_self (μ := ν) F a



theorem half_avg_heis_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1) ∂ν = ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hℓ₀ H hH _ _ ν _ u hu f hf
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have horth : ∀ {x y : WO S T}, IsHalf (cA D e) x → IsHalf (cA D e) y → symplO S T x y = 0 :=
    fun hx hy => GlobalTheory.SplitScalar.symplO_eq_zero S T hee hx hy
  have hhalfR : ∀ {m n k : ℕ} {t : Mx D m n} (M : Matrix (Fin n) (Fin k) (AE D)), IsHalf (cA D e) t →
      IsHalf (cA D e) (HMul.hMul t M : Mx D m k) := fun M ht i j => by
    simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

  set a : Mx D T.rank ρ := (d.coordS T u).1 with ha_def
  set w : WO S₀ T := (d.coordS T u).2.1 with hw_def
  set b : Mx D T.rank ρ := (d.coordS T u).2.2 with hb_def
  have hu_eq : u = d.extX T a + d.ext0 T w + d.extY T b := ((d.coordS T).symm_apply_apply u).symm
  have ha : IsHalf (cA D e) a := hhalfR _ hu
  have hw : IsHalf (cA D e) w := hhalfR _ hu
  have hb : IsHalf (cA D e) b := hhalfR _ hu
  have hXa : IsHalf (cA D e) (d.extX T a) := hhalfR _ ha
  have hYb : IsHalf (cA D e) (d.extY T b) := hhalfR _ hb
  have h0w : IsHalf (cA D e) (d.ext0 T w) := hhalfR _ hw
  have hth : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → ∀ v, IsThetaFunO ψ S T (heisO ψ S T v g) :=
    fun hg v => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg v
  set g₂ := heisO ψ S T (d.extY T b) f with hg₂
  set g₁ := heisO ψ S T (d.ext0 T w) g₂ with hg₁
  have hg₂t : IsThetaFunO ψ S T g₂ := hth hf _
  have hg₁t : IsThetaFunO ψ S T g₁ := hth hg₂t _
  have hsplit : heisO ψ S T u f = heisO ψ S T (d.extX T a) g₁ := by
    have hsum : IsHalf (cA D e) (d.ext0 T w + d.extY T b) := fun i j => by
      simp only [Matrix.add_apply, mul_add, h0w i j, hYb i j]
    rw [hu_eq, add_assoc, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth hXa hsum),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth h0w hYb)]
  let v : VolM D T.rank ρ := ⟨μ, 𝓕, hμ⟩
  have key : ∀ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1) = ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x + ⟨a, (hH a).2 ha⟩).1) := by
    intro x
    have hx : IsHalf (cA D e) x.1 := (hH x.1).1 x.2
    have hxa : IsHalf (cA D e) (x.1 + a) := fun i j => by
      simp only [Matrix.add_apply, mul_add, hx i j, ha i j]
    obtain ⟨c1, -, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₁ hg₁t
    obtain ⟨-, -, c3, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₂ hg₂t
    obtain ⟨-, c2, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf
    have e1 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1 = (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₁ (x.1 + a) := by
      rw [hsplit]; exact c1 x.1 a
    have e2 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₁ (x.1 + a) = heisO ψ S₀ T w ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a)) := c3 (x.1 + a) w
    have e3 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a) = (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x.1 + a) := by
      have hc2 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T (d.extY T b) f) (x.1 + a) = ψ (symplO S T (d.extX T (x.1 + a)) (d.extY T b)) • (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x.1 + a) := c2 (x.1 + a) b
      rw [hg₂, hc2, horth (show IsHalf (cA D e) (d.extX T (x.1 + a)) from hhalfR _ hxa) hYb,
        AddChar.map_zero_eq_one, one_smul]
    have hmt : IsThetaFunO ψ S₀ T ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a)) :=
      GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ g₂ hg₂t (x.1 + a)
    rw [e1, e2, hℓ₀ w hw _ hmt, e3]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_translate ν (fun x : H => ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f x.1)) _

end GlobalTheory.HalfInvariance
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOExtXExtY

section

namespace I195MixedCoordinates_0e01515b61ee225766e35969

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_0e01515b61ee225766e35969

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfNonvan

open GlobalTheory.HalfAverage

variable {D : D7}

theorem symplO_extX_extY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x a : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T a) = halfSympl T a x := by
  have h := d.hO_ext T x 0 0 a 0 0
  simp only [map_zero, add_zero, zero_add] at h
  have h0 : hO S₀ T (0 : WO S₀ T) 0 = 0 := by simp [hO]
  have hp : pairS T (0 : Mx D T.rank ρ) 0 = 0 := by simp [pairS, adj]
  rw [h0, hp, add_zero, add_zero] at h
  unfold symplO halfSympl
  rw [h]
  congr 2
  simp only [pairS, halfPair, Matrix.trace, Matrix.diag, Matrix.mul_apply, adj, gA, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc, rat]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem exists_mixS_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f₀ : WO S₀ T → ℂ} (hf₀ : IsThetaFunO ψ S₀ T f₀) :
    ∃ f, IsThetaFunO ψ S T f ∧ (_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f 0 = f₀ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨-, hb, hth, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hψ
    have hc : (fun w => (f₀ ∘ (Equiv.ofBijective _ hb).symm) (d.ext0 T w)) = f₀ := by
      funext w
      exact congrArg f₀ ((Equiv.ofBijective _ hb).symm_apply_apply w)
    refine ⟨f₀ ∘ (Equiv.ofBijective _ hb).symm, (hth _).1 (by rw [hc]; exact hf₀), ?_⟩
    change I195MixedCoordinates_7149a82cc25e6f9e668c8c61.source d T ψ μ 𝓕 _ 0 = f₀
    rw [(GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d μ 𝓕 hμ, hc]
  · obtain ⟨h1, h2, -, -, -, h6, -⟩ := GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    obtain ⟨f, hf, hff⟩ := GlobalTheory.TowerSurj.res_surjective D S S₀ T ρ d.e d.i₀ (h1 hρ) ψ hψ μ 𝓕 (h2 ▸ hμ) f₀ hf₀
    refine ⟨f, hf, ?_⟩
    change I195MixedCoordinates_16b53debd46a2c18720dfcab.source d T ψ μ 𝓕 f 0 = f₀
    rw [h6, map_zero, heisO_zero', hff]



theorem avg_mixS_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ f, IsThetaFunO ψ S T f ∧ ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f x.1) ∂ν ≠ 0 := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ ⟨f₀, hf₀, hℓ⟩ H hH mH bH ν hν
  obtain rfl : H = halfMx (cA D e) T.rank ρ := AddSubgroup.ext fun x => hH x
  obtain ⟨f, hf, hmix⟩ := exists_mixS_zero hψ d hμ hf₀
  by_contra hall
  push_neg at hall
  obtain ⟨-, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨⟨U, hU, hUinv⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨L, hL, hLU, hsep⟩ := GlobalTheory.HalfSeparate.exists_open_separated D ψ hψ T ρ e he
    (U.comap (halfMx (cA D e) T.rank ρ).subtype) (hU.preimage continuous_subtype_val)
  have hφ := @GlobalTheory.fourier_uniqueness_of_openSubgroup (halfMx (cA D e) T.rank ρ) (halfMx e T.rank ρ) _ _ _ mH bH ν hν _
    (fun a t => ψ (halfSympl T (a : Mx D T.rank ρ) (t : Mx D T.rank ρ)))
    (fun a s t => by simp only [AddSubgroup.coe_add, halfSympl_add_right, AddChar.map_add_eq_mul])
    (fun a => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_right, AddChar.map_zero_eq_one])
    (fun t => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_left, AddChar.map_zero_eq_one])
    (fun a b t => by simp only [AddSubgroup.coe_add, halfSympl_add_left, AddChar.map_add_eq_mul])
    L hL hsep (fun t => ℓ₀ ((_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f t.1))
    (Subtype.val ⁻¹' K) ((isClosed_halfMx _ _ _).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
    (fun t ht => by
      have : (_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f t.1 = 0 := by
        by_contra h
        exact ht (hKs t.1 t.2 h)
      simp only [this, map_zero])
    (fun t l hl => by
      simp only [AddSubgroup.coe_add]
      change ℓ₀ (I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f (t.1 + l.1)) =
        ℓ₀ (I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f t.1)
      rw [hUinv l.1 (hLU hl) l.2])
    (fun a _ => by
      rw [← hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T a.1))]
      refine congrArg (fun g => @integral _ ℂ _ _ mH ν g) (funext fun t => ?_)
      have := hY t.1 a.1
      simp only at this
      change ψ (halfSympl T a.1 t.1) * ℓ₀ (I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ μ 𝓕 f t.1) =
        ℓ₀ (I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ μ 𝓕 (heisO ψ S T (d.extY T a.1) f) t.1)
      rw [this, map_smul, smul_eq_mul, symplO_extX_extY])
  apply hℓ
  have := congrFun hφ 0
  simpa [hmix] using this

end GlobalTheory.HalfNonvan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCore

section

namespace I195MixedCoordinates_b25480cef10b1759a6cbdced

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_b25480cef10b1759a6cbdced

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitPlaceForm



theorem exists_form_of_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f') x) = k * ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 hne
  letI : MeasurableSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.measHalf _ _ _
  haveI : BorelSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.borelHalf _ _ _
  have hH : ∀ x, x ∈ GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ ↔ ∀ i j, cA D e * x i j = x i j := fun x => Iff.rfl
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.HalfLinForm.halfAvg_linear D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun h a => ?_⟩
  · rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u), hℓ f hf]
    exact GlobalTheory.HalfInvariance.half_avg_heis_inv D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 _ hH _ u hu f hf
  · obtain ⟨f, hf, hn⟩ := GlobalTheory.HalfNonvan.avg_mixS_ne_zero D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hne _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
    exact ⟨f, hf, by rw [hℓ f hf]; exact hn⟩
  · obtain ⟨r, hr, hm⟩ := GlobalTheory.HalfTwist.integral_twist_fix_eq_smul D T.rank ρ (cA D e) _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ) h a
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    have e1 := hm fun x => ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 f x)
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← e1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitPlaceForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCoreStatement

section

namespace I195MixedCoordinates_6fe4275e00e1b6fee4b47128

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_6fe4275e00e1b6fee4b47128

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_splitPlace_invariantForm_of_wittCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ ((_root_.I195MixedCoordinates_6fe4275e00e1b6fee4b47128.source d) T ψ μ 𝓕 (f') x) = k * ℓ₀ ((_root_.I195MixedCoordinates_6fe4275e00e1b6fee4b47128.source d) T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  first | exact @GlobalTheory.SplitPlaceForm.exists_form_of_core | exact GlobalTheory.SplitPlaceForm.exists_form_of_core | (intros; apply GlobalTheory.SplitPlaceForm.exists_form_of_core <;> assumption)
end
end
