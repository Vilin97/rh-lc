module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOne
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharactersStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle), Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  first | exact @GlobalTheory.glChar_eq_one_of_det_eq_one | exact GlobalTheory.glChar_eq_one_of_det_eq_one | (intros; apply GlobalTheory.glChar_eq_one_of_det_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlaceStatement

section

namespace I195MixedCoordinates_3f9f8d8466fd251acacc5207

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

end I195MixedCoordinates_3f9f8d8466fd251acacc5207

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.leviFactor_characters_splitPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), (∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_3f9f8d8466fd251acacc5207.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_3f9f8d8466fd251acacc5207.source d) T ψ μ 𝓕 (f) 0)) → ∀ e, IsSplitIdem D e → (∀ g, SuppAt e S₀ g → ξ g = 1) ∧ ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  first | exact @GlobalTheory.LeviSplitChar.levi_chars_split | exact GlobalTheory.LeviSplitChar.levi_chars_split | (intros; apply GlobalTheory.LeviSplitChar.levi_chars_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalar

section

namespace I195MixedCoordinates_29b19643a6a40f518f292300

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

end I195MixedCoordinates_29b19643a6a40f518f292300

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem halfMod_eq_detPow {D : D7} {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := rfl

theorem halfMod_rank_zero {D : D7} (n : ℕ) (a : GL (Fin 0) (AE D)) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, Subsingleton.elim a 1, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem wittDecomposition_levi_emb_acts_isotropic {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.e.map (incA D) = d.e.map (incA D) ⬝ a.1 := by
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]

theorem wittDecomposition_levi_emb_acts_anisotropicCore {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.i₀.map (incA D) = d.i₀.map (incA D) ⬝ mt S₀ g := by
  have e2 : d.i₀.map (incA D) = d.j0 := rfl
  rw [e2, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]

theorem heisO_extX_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ)
    (f : WO S T → ℂ) : heisO ψ S T (d.extX T 0) f = f := by
  funext w
  simp only [heisO, map_zero, add_zero, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem levi_origin_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_29b19643a6a40f518f292300.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_29b19643a6a40f518f292300.source d) T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨hz, -, hl⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, -, -, hiso⟩ := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hom.std
    refine ⟨1, 1, continuous_const, fun _ => rfl, continuous_const, fun _ _ => rfl, fun a g f hf => ?_⟩
    change I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 _ 0 = _ • om₀ (g, 1) (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f 0)
    rw [hz S S₀ T d μ 𝓕 hμ, hz S S₀ T d μ 𝓕 hμ, (hl S S₀ d).1, one_mul, hiso χS χT om om₀ hom hom₀ g 1 f hf,
      halfMod_rank_zero]
    simp
  · obtain ⟨hsp, hr, -, -, -, hm, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    obtain ⟨α, ξ, hα, hξ, h⟩ := GlobalTheory.T.leviFactor_scalars_automorphicCharacters D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT om hom χS χT om₀ hom₀
    refine ⟨α, ξ, hα.1, hα.2, hξ.1, hξ.2, fun a g f hf => ?_⟩
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hr]; exact hμ
    change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 _ 0 = _ • om₀ (g, 1) (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0)
    rw [hm, hm, heisO_extX_zero, heisO_extX_zero, halfMod_eq_detPow]
    exact h μ 𝓕 hμ' a g (d.levi a * d.emb0 g) (wittDecomposition_levi_emb_acts_isotropic d a g) (wittDecomposition_levi_emb_acts_anisotropicCore d a g) f hf

end GlobalTheory.Unf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalarStatement

section

namespace I195MixedCoordinates_34172b91c8e709398ceb2b5d

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

end I195MixedCoordinates_34172b91c8e709398ceb2b5d

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilAction_levi_origin_eq_charScalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_34172b91c8e709398ceb2b5d.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_34172b91c8e709398ceb2b5d.source d) T ψ μ 𝓕 (f) 0) := by
  first | exact @GlobalTheory.Unf.levi_origin_scalar | exact GlobalTheory.Unf.levi_origin_scalar | (intros; apply GlobalTheory.Unf.levi_origin_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor

section

namespace I195MixedCoordinates_020c054dc3163dabb7fb929c

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

end I195MixedCoordinates_020c054dc3163dabb7fb929c

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.LeviOrigin

def diagAt {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : R →* Matrix (Fin ρ) (Fin ρ) R where
  toFun t := Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  map_one' := by
    have h1 : Function.update (1 : Fin ρ → R) i 1 = 1 := by
      funext j; by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    show Matrix.diagonal (Function.update (1 : Fin ρ → R) i 1) = 1
    rw [h1]; exact Matrix.diagonal_one
  map_mul' s t := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

def dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : Rˣ →* GL (Fin ρ) R := Units.map (diagAt ρ i)

theorem det_dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (dgU ρ i t) = t := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (t : R))).det = t
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem continuous_dgU {R : Type*} [CommRing R] [TopologicalSpace R] (ρ : ℕ) (i : Fin ρ) :
    Continuous (dgU (R := R) ρ i) := by
  apply Continuous.units_map
  show Continuous fun t : R => Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  exact Continuous.matrix_diagonal (continuous_const.update i continuous_id)

theorem dgU_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (ρ : ℕ) (i : Fin ρ) (x : Rˣ) :
    dgU ρ i (Units.map f.toMonoidHom x) = Matrix.GeneralLinearGroup.map f (dgU ρ i x) := by
  ext k l
  show Matrix.diagonal (Function.update (1 : Fin ρ → S) i (f x)) k l =
    f (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l)
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h']
  · simp

theorem dgU_sub_one {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (x : Rˣ) (k l : Fin ρ) :
    ((dgU ρ i x).1 - 1) k l = if k = i ∧ l = i then (x : R) - 1 else 0 := by
  show Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l - (1 : Matrix (Fin ρ) (Fin ρ) R) k l = _
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : k = l
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h', h']
  · simp [h]
    intro hk hl; exact absurd (hk.trans hl.symm) h

end GlobalTheory.LeviOrigin

theorem GlobalTheory.LeviOrigin.alpha_eq (D : D7) (ρ : ℕ) (α : GL (Fin ρ) (AE D) →* Circle) (χT : (AE D)ˣ →* Circle)
    (hαc : Continuous α) (hαr : ∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1)
    (hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1)
    (hχ : IsHeckeChar D χT)
    (hs : ∀ e, IsSplitIdem D e → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) →
      α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹) :
    ∀ a : GL (Fin ρ) (AE D), α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · intro a
    have hd : Matrix.GeneralLinearGroup.det a = 1 := by
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst h0; simp
    rw [hα1 a hd, hd, map_one, inv_one]
  obtain ⟨i0⟩ : Nonempty (Fin ρ) := ⟨⟨0, hpos⟩⟩
  have hhec : IsHeckeChar D (α.comp (GlobalTheory.LeviOrigin.dgU ρ i0) * χT) := by
    refine ⟨?_, ?_⟩
    · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU ρ i0)).mul hχ.1
    · intro x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ.2 x, mul_one, GlobalTheory.LeviOrigin.dgU_map (incA D) ρ i0 x]
      exact hαr _
  have hν := GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces D _ hhec (by
    intro e he x hx
    have h2 := hs e he (GlobalTheory.LeviOrigin.dgU ρ i0 x) (by
      intro k l
      rw [GlobalTheory.LeviOrigin.dgU_sub_one]
      split_ifs
      · exact hx
      · exact mul_zero _)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, inv_mul_cancel])
  have hdg : ∀ t, α (GlobalTheory.LeviOrigin.dgU ρ i0 t) = (χT t)⁻¹ := by
    intro t
    have := hν t
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply] at this
    exact eq_inv_of_mul_eq_one_left this
  intro a
  have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
  have h1 := hα1 _ hb
  have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
      α (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a)) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h3, h1, one_mul]
  exact hdg _

theorem GlobalTheory.LeviOrigin.value_at_origin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) ((_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ f hf
  obtain ⟨α, ξ, hαc, hαr, hξc, hξr, hmain⟩ := GlobalTheory.T.weilAction_levi_origin_eq_charScalar D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ
  have hsp := GlobalTheory.T.leviFactor_characters_splitPlace D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ α ξ hmain

  have hξ : ∀ g, ξ g = 1 :=
    GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S₀ ξ hξc hξr (fun e he => (hsp e he).1)

  have hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1 :=
    GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one D ρ α hαc
  have hα := GlobalTheory.LeviOrigin.alpha_eq D ρ α χT hαc hαr hα1 hW.hecT (fun e he => (hsp e he).2)
  have hhalf : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a = 1 := by
    intro a ha
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
    rw [ha, MonoidHom.map_one (GlobalTheory.Doubling.absE D.host.F D.host.E)]
    simp
  have hom₀ : ∀ x, om₀ (1, 1) x = x := by
    intro x; rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have key : ∀ a, (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_020c054dc3163dabb7fb929c.source d) T ψ μ 𝓕 (f) 0 := by
    intro a
    have := hmain a 1 f hf
    rw [map_one, mul_one, hξ 1, hom₀, hα a] at this
    simpa using this
  refine ⟨?_, ?_, key⟩
  · intro g
    have := hmain 1 g f hf
    rw [map_one, one_mul, hξ g, map_one, hhalf 1 (map_one _)] at this
    simpa using this
  · intro a ha
    rw [key a, ha, map_one, inv_one, hhalf a ha]
    simp
end
end
end
