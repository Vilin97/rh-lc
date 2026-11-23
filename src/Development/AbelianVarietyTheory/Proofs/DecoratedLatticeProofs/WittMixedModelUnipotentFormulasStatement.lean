module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginUnipotentRadicalInvariant

section

namespace I195MixedCoordinates_069c5864e5661f762e792771

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

end I195MixedCoordinates_069c5864e5661f762e792771

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnipZero

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    first | exact symplOH_zero_right .. | simp [symplOH] | (rw [symplOH]; simp)
  simp [heisO, h]

theorem mixS_zero_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ b, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ c, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hW μ 𝓕 hμ f hf
  rcases Nat.eq_zero_or_pos ρ with hρ | hρ
  · subst hρ
    obtain ⟨-, -, h0⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, hB, hC⟩ := h0 S S₀ d
    refine ⟨fun b => ?_, fun c => ?_⟩
    · rw [hB b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
    · rw [hC c, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
  · obtain ⟨hiso, hrat, -, -, -, hres, -, hnB, hnC⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have key : ∀ n : NI S d.e, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 f 0 := by
      intro n
      change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0
      rw [hres, hres, map_zero, heisO_zero, heisO_zero]
      exact GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ χS χT om hW μ 𝓕 hμ' n f hf
    exact ⟨fun b => key ⟨_, hnB b⟩, fun c => key ⟨_, hnC c⟩⟩

end GlobalTheory.UnipZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginUnipotentRadicalInvariantStatement

section

namespace I195MixedCoordinates_46859e632a5b1b7714de2075

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

end I195MixedCoordinates_46859e632a5b1b7714de2075

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.mixedCoordinate_origin_unipotentRadical_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ b, (_root_.I195MixedCoordinates_46859e632a5b1b7714de2075.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) 0 = (_root_.I195MixedCoordinates_46859e632a5b1b7714de2075.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ c, (_root_.I195MixedCoordinates_46859e632a5b1b7714de2075.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) 0 = (_root_.I195MixedCoordinates_46859e632a5b1b7714de2075.source d) T ψ μ 𝓕 (f) 0 := by
  first | exact @GlobalTheory.UnipZero.mixS_zero_unip | exact GlobalTheory.UnipZero.mixS_zero_unip | (intros; apply GlobalTheory.UnipZero.mixS_zero_unip <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulas

section

namespace I195MixedCoordinates_c87fda97bbaf39bed14145da

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

end I195MixedCoordinates_c87fda97bbaf39bed14145da

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixUnip

variable {D : D7}

theorem symplOH_antisymm {S T : HSp D} (a b : WO S T) : symplOH S T b a = -symplOH S T a b := by
  have h := GlobalTheory.OrientedHeis.symplOH_self (S := S) (T := T) (a + b)
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, GlobalTheory.OrientedHeis.symplOH_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem symplO_zero_left' {S T : HSp D} (y : WO S T) : symplO S T 0 y = 0 := by
  simp [symplO, hO]

theorem symplO_eq_two {S T : HSp D} (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext v
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixS_smul (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (c • f) x = c • (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 f x := by
  funext w
  simp only [_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source, heisO_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]

theorem mixS_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ b, (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) x = heisO ψ S₀ T (x ⬝ b) ((_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (f) x)) ∧ ∀ c, (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) x = ψ (d.qS T c x) • (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (f) x := by
  intro D ψ S S₀ T ρ d χS χT om hom μ 𝓕 hμ f hf x
  have hstd := hom.std
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T
  obtain ⟨-, -, hmove⟩ := GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om hom μ 𝓕 hμ f hf x
  have hzB := fun g (hg : IsThetaFunO ψ S T g) => (GlobalTheory.T.mixedCoordinate_origin_unipotentRadical_invariant D ψ S S₀ T ρ d χS χT om hom μ 𝓕 hμ g hg).1
  have hzC := fun g (hg : IsThetaFunO ψ S T g) => (GlobalTheory.T.mixedCoordinate_origin_unipotentRadical_invariant D ψ S S₀ T ρ d χS χT om hom μ 𝓕 hμ g hg).2

  change ∀ n : GA D S,
    (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (om (n, 1) f) x =
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕
        (om (n, 1) (heisO ψ S T (d.extX T x ⬝ mt S n) f)) 0 at hmove
  change ∀ g, IsThetaFunO ψ S T g → ∀ b,
    (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (om (d.nB b, 1) g) 0 =
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g 0 at hzB
  change ∀ g, IsThetaFunO ψ S T g → ∀ c,
    (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (om (d.nC c, 1) g) 0 =
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g 0 at hzC

  have eX : ∀ (a : Mx D T.rank ρ) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T a) g) 0 = (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g a := fun a g hg => by
    have := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ g hg).1 0 a
    simpa only [zero_add] using this
  have eY : ∀ (a : Mx D T.rank ρ) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (heisO ψ S T (d.extY T a) g) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g x :=
    fun a g hg => (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ g hg).2.1 x a
  have jointCmpEmbeddingY : ∀ (a : Mx D T.rank ρ) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (heisO ψ S T (d.extY T a) g) 0 = (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g 0 := fun a g hg => by
    have := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ g hg).2.1 0 a
    rw [map_zero, GlobalTheory.MixUnip.symplO_zero_left', AddChar.map_zero_eq_one, one_smul] at this
    exact this
  refine ⟨fun b => ?_, fun c => ?_⟩
  · set X := d.extX T x
    set Z := d.ext0 T (x ⬝ b)
    set a := x ⬝ (half D • (b ⬝ plus S₀ b))
    have hXY : symplOH S T X (d.extY T a) = 0 := by
      have e : pairS T x a = half D * hO S₀ T (x ⬝ b) (x ⬝ b) := by
        rw [← pairS_plus]
        simp only [a, pairS, Matrix.mul_smul, adj_smul, cA_half, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      refine eq_of_add_self (F := D.host.F) ?_
      rw [HypDec.symplOH_extX_extY, e, trHalf_half, ← symplOH_eq, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
    have hXY' : symplOH S T X (d.extY T (-a)) = 0 := by
      have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) X (d.extY T a) (d.extY T (-a))
      rw [← map_add (f := _), add_neg_cancel, map_zero, symplOH_zero_right, hXY, zero_add] at h
      exact h.symm
    have hkey : heisO ψ S T (X ⬝ mt S (d.nB b)) f =
        heisO ψ S T (d.extY T (-a)) (heisO ψ S T X (heisO ψ S T Z f)) := by
      rw [hcomp X Z f, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, AddChar.map_zero_eq_one, one_smul, hcomp,
        GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extDual_extAnisotropic, add_zero, GlobalTheory.MixUnip.symplOH_antisymm, hXY',
        neg_zero, AddChar.map_zero_eq_one, one_smul, HypDec.extX_nB, map_neg]
      congr 1
      abel
    rw [hmove (d.nB b), hzB _ (hth _ _ hf), hkey, jointCmpEmbeddingY _ _ (hth _ _ (hth _ _ hf)), eX _ _ (hth _ _ hf)]
    exact (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf).2.2.1 x (x ⬝ b)
  · have hq : d.qS T c x = symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) := rfl
    have hL : (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 (heisO ψ S T (d.extX T x) (heisO ψ S T (d.extY T (x ⬝ c.1)) f)) 0 =
        ψ (d.qS T c x) • ψ (d.qS T c x) • (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 f x := by
      have h2 := eY (x ⬝ c.1) f hf
      have h3 := eX x (heisO ψ S T (d.extY T (x ⬝ c.1)) f) (hth _ _ hf)
      rw [h3, h2, GlobalTheory.MixUnip.symplO_eq_two, AddChar.map_add_eq_mul, ← hq, mul_smul]
    have hc' : heisO ψ S T (d.extX T x) (heisO ψ S T (d.extY T (x ⬝ c.1)) f) =
        ψ (d.qS T c x) • heisO ψ S T (d.extX T x + d.extY T (x ⬝ c.1)) f := hcomp _ _ _
    have h1 := congrArg (fun g => (_root_.I195MixedCoordinates_c87fda97bbaf39bed14145da.source d) T ψ μ 𝓕 g 0) hc'
    rw [hL, GlobalTheory.MixUnip.mixS_smul] at h1
    have hne : ψ (d.qS T c x) ≠ 0 := by
      have h := AddChar.map_add_eq_mul ψ (d.qS T c x) (-d.qS T c x)
      rw [add_neg_cancel, AddChar.map_zero_eq_one] at h
      exact left_ne_zero_of_mul_eq_one h.symm
    rw [hmove (d.nC c), hzC _ (hth _ _ hf), HypDec.extX_nC]
    exact (smul_right_injective _ hne h1).symm

end GlobalTheory.MixUnip

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulasStatement

section

namespace I195MixedCoordinates_fc0f2fb3767bfc57c3512e89

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

end I195MixedCoordinates_fc0f2fb3767bfc57c3512e89

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.wittMixedModel_unipotent_formulas : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ b, (_root_.I195MixedCoordinates_fc0f2fb3767bfc57c3512e89.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) x = heisO ψ S₀ T (x ⬝ b) ((_root_.I195MixedCoordinates_fc0f2fb3767bfc57c3512e89.source d) T ψ μ 𝓕 (f) x)) ∧ ∀ c, (_root_.I195MixedCoordinates_fc0f2fb3767bfc57c3512e89.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) x = ψ (d.qS T c x) • (_root_.I195MixedCoordinates_fc0f2fb3767bfc57c3512e89.source d) T ψ μ 𝓕 (f) x := by
  first | exact @GlobalTheory.MixUnip.mixS_unip | exact GlobalTheory.MixUnip.mixS_unip | (intros; apply GlobalTheory.MixUnip.mixS_unip <;> assumption)
end
end
