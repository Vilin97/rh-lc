module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsOrbitSubsetNonzeroLocus

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem exists_forms_forall_mem_basicOpen {Γ : Type} [Finite Γ] {R : Type} [CommRing R] {N : ℕ}
    {X : Scheme.{0}} [CompactSpace X] (φ : Γ → (X ⟶ PSpace R N)) :
    ∃ (d n : ℕ) (F : Fin n → MvPolynomial (Fin (N + 1)) R), 0 < d ∧ (∀ i, (F i).IsHomogeneous d) ∧
      ∀ x : X, ∃ i, ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (F i) := by
  classical

  have orbit : ∀ x : X, ∃ e : ℕ, 0 < e ∧ ∃ f ∈ ProjSpace.grading R N e,
      Set.range (fun g => φ g x) ⊆ Proj.basicOpen (ProjSpace.grading R N) f := fun x =>
    FiniteSubsetsInAffineOpens.exists_proj_basicOpen (ProjSpace.grading R N) (Set.finite_range _)
  choose e he f hf hsub using orbit

  let U : X → Set X := fun x => {z | ∀ g, φ g z ∈ Proj.basicOpen (ProjSpace.grading R N) (f x)}
  have hU : ∀ x, U x ∈ nhds x := fun x => by
    refine IsOpen.mem_nhds ?_ fun g => hsub x ⟨g, rfl⟩
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun g =>
      (φ g).continuous.isOpen_preimage _ (Proj.basicOpen (ProjSpace.grading R N) (f x)).isOpen

  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  have hD : 0 < ∏ x ∈ t, e x := Finset.prod_pos fun x _ => he x
  have hdvd : ∀ x ∈ t, e x ∣ ∏ y ∈ t, e y := fun x hx => Finset.dvd_prod_of_mem e hx
  refine ⟨∏ x ∈ t, e x, t.card,
    fun i => f (t.equivFin.symm i) ^ ((∏ x ∈ t, e x) / e (t.equivFin.symm i)), hD, fun i => ?_, fun x => ?_⟩
  · have h1 : (f (t.equivFin.symm i)).IsHomogeneous (e (t.equivFin.symm i)) := hf _
    have h2 := h1.pow ((∏ x ∈ t, e x) / e (t.equivFin.symm i))
    rwa [Nat.mul_div_cancel' (hdvd _ (t.equivFin.symm i).2)] at h2
  · have hx : x ∈ ⋃ y ∈ t, U y := by rw [ht]; exact Set.mem_univ x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
    have hxy' : ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (f y) := hxy
    refine ⟨t.equivFin ⟨y, hy⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [Proj.basicOpen_pow]
    · exact hxy' g
    · exact Nat.div_pos (Nat.le_of_dvd hD (hdvd y hy)) (he y)

theorem exists_sections_orbit_subset_nonzeroLocus : ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ρ : Γ →* Aut X), IsProjOver s → ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
  intro Γ _ _ R _ X s ρ hs
  obtain ⟨N, j, hj, -⟩ := hs

  haveI : CompactSpace (PSpace R N) := by
    refine ⟨?_⟩
    have hcov : (Set.univ : Set (PSpace R N)) = ⋃ i, (ProjSpace.chart R N i : Set (PSpace R N)) := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact ProjSpace.exists_mem_chart R N y
    rw [hcov]
    exact isCompact_iUnion fun i => (ProjSpace.isAffineOpen_chart R N i).isCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j

  obtain ⟨d, n, F, hd, hF, hcov⟩ := exists_forms_forall_mem_basicOpen (fun g => (ρ g).asIso.hom ≫ j)
  refine ⟨(lbPow (ProjSpace.O1 R N) d).pull j, n, fun i => secPull (ProjSpace.formSec d (F i) (hF i)) j,
    pull_isLB (isLB_lbPow (ProjSpace.O1_isLB R N) d) j, fun i => ?_, fun x => ?_⟩
  · rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact (Proj.isAffineOpen_basicOpen (ProjSpace.grading R N) (F i) (hF i) hd).preimage j
  · obtain ⟨i, hi⟩ := hcov x
    refine ⟨i, fun g => ?_⟩
    rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact hi g

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_of_isProper_of_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsProper s]
    {L : LB X} (hL : L.IsLB) {n : ℕ} (σ : Fin n → LB.Sec L) (ha : ∀ i, IsAffineOpen (Out.nonzeroLocus (σ i)))
    (hc : ⨆ i, Out.nonzeroLocus (σ i) = ⊤) : IsProjOver s := by
  have hA : IsAmpleLB L := by
    refine ⟨hL, ⟨?_⟩, ?_⟩
    · have hu : (Set.univ : Set X) = ⋃ i, (Out.nonzeroLocus (σ i) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup, hc]
        rfl
      rw [hu]
      exact isCompact_iUnion fun i => (ha i).isCompact
    · intro x
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      refine ⟨1, le_rfl, secToPow (σ i) 1, ?_, ?_⟩
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact hi
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact ha i
  exact hA.isProjOver s

theorem isProjOver_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  intro Γ _ _ X X' ρ π hq R _ _ s' hX
  have hQ : IsAffineQuotient ρ π :=
    ⟨hq.2.1, hq.1, fun W => (hq.2.2 W).1, fun W f hf => (hq.2.2 W).2 f (by
      unfold IsInvariantSection at hf
      exact fun g _ => (hf g).2)⟩
  have hP : IsProper (π ≫ s') := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX).1
  have hs' : IsProper s' := hQ.isProper s'
  have hXs : X.IsSeparated := by
    constructor
    rw [show terminal.from X = (π ≫ s') ≫ terminal.from (Sp R) from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨L, n, σ, hL, ha, ho⟩ := exists_sections_orbit_subset_nonzeroLocus Γ R X (π ≫ s') ρ hX
  obtain ⟨L', n', σ', hL', ha', hc'⟩ :=
    QuotientNorm.exists_affine_cover_of_quotient Γ X X' ρ π hq hXs L n σ hL ha ho
  exact isProjOver_of_isProper_of_affine_cover s' hL' σ' ha' hc'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.isProjOver_finite_group_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  first | exact @GlobalTheory.isProjOver_quotient | exact GlobalTheory.isProjOver_quotient | (intros; apply GlobalTheory.isProjOver_quotient <;> assumption)
end
end
