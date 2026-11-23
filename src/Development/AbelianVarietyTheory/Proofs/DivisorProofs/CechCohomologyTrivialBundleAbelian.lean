module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupSchemeStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOrigin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElementsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolutionStatement
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRing
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocalStatement
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOriginStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), L.IsLB → IsProjBy A.hom → (∃ t : LB.Gen (Theta A L), t.IsGen) → IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → (∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∃ (J : Ideal (A.left.presheaf.stalk x₀)) (C : CochainComplex (ModuleCat.{0} (A.left.presheaf.stalk x₀)) ℕ) (φ : A.left.presheaf.stalk x₀ →+* K), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) ∧ RingHom.ker φ = IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∧ (∀ i, Module.Free (A.left.presheaf.stalk x₀) (C.X i) ∧ Module.Finite (A.left.presheaf.stalk x₀) (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual (A.left.presheaf.stalk x₀) (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A.left.presheaf.stalk x₀] (A.left.presheaf.stalk x₀ ⧸ J)) ∧ (∀ p : PrimeSpectrum (A.left.presheaf.stalk x₀), ∃ (K' : Type) (_ : Field K') (φ' : A.left.presheaf.stalk x₀ →+* K'), RingHom.ker φ' = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∨ g < i) → (((ModuleCat.extendScalars φ').mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty (((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i) ≃ₗ[K] (cechLB A.hom (LB.triv A.left) D).homology i) := by
  first | exact @GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin | exact GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin | (intros; apply GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

theorem _root_.GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  first | exact @GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | exact GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | (intros; apply GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.FDim

theorem fromSpecStalk_comp_spec {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isClosed_origin (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (p : Sp K) :
    IsClosed ({(η[A]).left.base p} : Set A.left) := by
  have hr : Set.range (η[A]).left.base = {(η[A]).left.base p} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hs : Subsingleton (Sp K) := inferInstance
      obtain rfl : q = p := hs.elim q p
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rw [← hr]
  exact (η[A]).left.isClosedEmbedding.isClosed_range

theorem cechLB_triv_finrank_one_two : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  intro K _ _ A _ g hA hsm κ _ _ D hD hcov
  obtain ⟨L, H, _, j, hL, hproj, hgen, hj, hci, hfin, hK⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hx₀ : (η[A]).left.base p ∈ Set.range (η[A]).left.base := ⟨p, rfl⟩
  obtain ⟨J, C, φ, hJ, hφ, hfree, hbdd, hcok, hfib, hiso⟩ :=
    GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin K A g hA hsm L H j hL hproj hgen hj hci hfin hK _ hx₀
  obtain ⟨f, hf⟩ := GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements K A g hA hsm H j hj hci hfin _ hx₀ J hJ
  obtain ⟨hJt, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin _ hx₀ J hJ
  subst hf
  let σ : K →+* A.left.presheaf.stalk ((η[A]).left.base p) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.hom.appTop ≫
      A.left.presheaf.germ ⊤ ((η[A]).left.base p) trivial).hom
  have hσ : A.left.fromSpecStalk ((η[A]).left.base p) ≫ A.hom = Spec.map (CommRingCat.ofHom σ) := by
    rw [fromSpecStalk_comp_spec]
    rfl
  have hloc : IsLocalHom σ := ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩
  obtain ⟨-, -, hreg, hdim⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth K A.left A.hom g hsm _ (isClosed_origin K A p) σ hσ hloc
  have hbot : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot (A.left.presheaf.stalk ((η[A]).left.base p)))
  haveI : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left.base p)) :=
    IsRegularLocalRing.of_ringEquiv e
  have hdim' : ringKrullDim (A.left.presheaf.stalk ((η[A]).left.base p)) = g := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  have hex := GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres _ g hdim' C hfree hbdd hfib
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_homology_one_two_dualResolution _ g hdim' f hJt hart C hfree hex hcok K φ hφ
  haveI := hA.proper
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K A.left A.hom (LB.triv A.left) κ D
      (LB.isLB_triv _) inferInstance hproj hD hcov i
  · obtain ⟨e1⟩ := hiso κ D hD hcov 1
    rw [← e1.finrank_eq]
    exact h1
  · obtain ⟨e2⟩ := hiso κ D hD hcov 2
    rw [← e2.finrank_eq]
    exact h2

end GlobalTheory.AbCoh.FDim
end
end
