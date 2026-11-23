module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PWeylAt

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit

section

@[expose] public section

open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq

section

@[expose] public section

open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits

section

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalThetaTopology

theorem locallyCompact_units {M : Type} [Ring M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
    [LocallyCompactSpace M] : LocallyCompactSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_units {M : Type} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_units {M : Type} [Monoid M] [TopologicalSpace M] [T2Space M] : T2Space Mˣ :=
  Units.isEmbedding_embedProduct.t2Space

theorem top_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact ⟨locallyCompact_units, secondCountable_units, t2Space_units⟩

theorem continuous_thetaR {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (σ : A →+* A)
    (hσ : Continuous σ) (n : ℕ) : Continuous (thetaR σ n) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E := by
  let b := Module.finBasis ℚ E
  exact Function.Injective.countable b.equivFun.injective

theorem countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

theorem continuous_thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g =>
      PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹ :=
    funext fun g => thetaGL_eq n (Af E) _ g
  rw [h]
  exact (continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const

theorem topo : Topo := by
  intro E _ _ _ n
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨c1, c2, -⟩ := top_GL (R := ℂ) n
  exact ⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n,
    continuous_thetaR _ Complex.continuous_conj n⟩

end GlobalTheory.CompanionTheory.LocalThetaTopology
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem mul_finsum_eq {α : Type*} (r : ℂ) (f : α → ℂ) : ∑ᶠ i, r * f i = r * ∑ᶠ i, f i := by
  have h := smul_finsum (R := ℂ) (M := ℂ) r f
  simpa only [smul_eq_mul] using h.symm

theorem global_character_of_holds : GlobalCharacterOfInputs := by
  intro hT hO hA hC hP E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨c, hc0, hc⟩ := hT E hU a b μ₁ μ₂ ν₁ ν₂
  refine ⟨c, hc0, ?_⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂
  obtain ⟨e₁, he₁⟩ := hC E a u₁ hu₁
  obtain ⟨e₂, he₂⟩ := hC E b u₂ hu₂
  have hψ : ∀ v, Continuous (ψ v) := fun v => (hL v).1
  unfold ellSum2 geomRat2
  rw [← finsum_comp_equiv (e₁.prodCongr e₂), ← mul_finsum_eq]
  refine finsum_congr fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  obtain ⟨g₁, hg₁, hr₁⟩ := he₁ x₁
  obtain ⟨g₂, hg₂, hr₂⟩ := he₂ x₂
  have hiff : (IsRegEll (Quot.out (e₁ x₁)) ∧ IsRegEll (Quot.out (e₂ x₂))) ↔ (pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b) := by
    rw [hr₁, hr₂, (hP E a u₁ hu₁ _).1, (hP E b u₂ hu₂ _).1, mul_inv_cancel_right, mul_inv_cancel_right]
    exact Iff.rfl
  have horb : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (Quot.out (e₁ x₁)) (Quot.out (e₂ x₂)) =
      orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (x₁.rep * u₁) (x₂.rep * u₂) := by
    rw [hg₁, hg₂, hO E a b μ₁ μ₂ _ _ g₁ _ g₂ (hA E hU a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ hψ hφ₁ hφ₂ _ _)]
  rw [finsum_eq_if]
  by_cases h : pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b
  · rw [if_pos (hiff.2 h), if_pos h, horb]
    have ht := hc S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂ (x₁.rep * u₁) (x₂.rep * u₂)
      (hr₁.1 (hiff.2 h).1) (hr₂.1 (hiff.2 h).2)
    simp only [mul_inv_cancel_right] at ht
    exact ht
  · rw [if_neg (mt hiff.1 h), if_neg h, mul_zero]

end PositivityTheory.Rg.BcB.G8

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
end
end
