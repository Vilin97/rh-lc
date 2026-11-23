module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGeneratoStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by

        simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _

  simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient : ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L), ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) → (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_sum_nonzero | exact GlobalTheory.exists_sec_sum_nonzero | (intros; apply GlobalTheory.exists_sec_sum_nonzero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctions

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.exists_separating_basicOpen_functions' : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  first | exact @GlobalTheory.exists_separating_basicOpen_functions | exact GlobalTheory.exists_separating_basicOpen_functions | (intros; apply GlobalTheory.exists_separating_basicOpen_functions <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFiniteStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  first | exact @GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | exact GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | (intros; apply GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem exists_sec_nonzero_on_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  intro Y Y' Z' k hk p' hpc hps V hV y hy _ M hM hloc
  classical
  obtain ⟨hfin, hdisc⟩ := GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' Y Y' k hk y
  have hU : IsAffineOpen (k ⁻¹ᵁ V) := hV.preimage k
  let F : Finset Y' := hfin.toFinset
  have hF : ∀ a, a ∈ F ↔ k a = y := fun a => by simp [F]
  have hW : ∀ a : Y', ∃ W : Y'.Opens, (k a = y → a ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) := by
    intro a
    by_cases h : k a = y
    · obtain ⟨W, hW, t, ht⟩ := hloc a h
      exact ⟨W, fun _ => ⟨hW, t, ht⟩⟩
    · exact ⟨⊤, fun h' => absurd h' h⟩
  choose W hW using hW
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_separating_basicOpen_functions' Y' (k ⁻¹ᵁ V) hU F (fun a ha => by
      show k a ∈ V
      rw [(hF a).1 ha]; exact hy) (fun a ha b hb hab => hdisc a b ((hF a).1 ha) ((hF b).1 hb) hab)
    W (fun a ha => ((hW a) ((hF a).1 ha)).1)
  let q : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme ⟶ Y' := (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι ≫ p'
  have hq : (⊤ : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.Opens) ≤ q ⁻¹ᵁ (k ⁻¹ᵁ V) := by
    intro z _
    show p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z) ∈ k ⁻¹ᵁ V
    have h : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z ∈ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := (Scheme.Opens.range_ι (p' ⁻¹ᵁ (k ⁻¹ᵁ V))).subset ⟨z, rfl⟩
    exact h
  let r : Y' → Γ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, ⊤) := fun a => (q.appLE (k ⁻¹ᵁ V) ⊤ hq).hom (f a)
  have hr : ∀ a (z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme), z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ↔ q z ∈ Y'.basicOpen (f a) := by
    intro a z
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  haveI : CompactSpace (k ⁻¹ᵁ V).toScheme := isCompact_iff_compactSpace.1 hU.isCompact
  haveI : CompactSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := by
    have := hpc.isCompact_preimage _ (k ⁻¹ᵁ V).isOpen hU.isCompact
    exact isCompact_iff_compactSpace.1 this
  haveI : IsAffine (k ⁻¹ᵁ V).toScheme := hU
  haveI : QuasiSeparatedSpace (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme := quasiSeparatedSpace_of_quasiSeparated (p' ∣_ (k ⁻¹ᵁ V))
  have hσ : ∀ a : F, ∃ σ : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r a) ≤ nonzeroLocus σ := by
    rintro ⟨a, ha⟩
    obtain ⟨-, t, ht⟩ := hW a ((hF a).1 ha)
    exact GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator Z' _ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι inferInstance ‹_› ‹_› M hM (r a) (p' ⁻¹ᵁ W a)
      (fun x hx => (hf a ha).2.1 ((hr a x).1 hx)) t ht
  choose σ hσ using hσ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient _ (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι) F (fun a => r a) σ
  refine ⟨s, fun z hz => ?_⟩
  have ha : q z ∈ F := (hF _).2 hz
  have h1 : z ∈ (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme.basicOpen (r (q z)) := (hr _ z).2 (hf _ ha).1
  refine hs z ⟨q z, ha⟩ h1 (hσ _ h1) (fun j hj => ?_)
  rw [hr]
  exact (hf j.1 j.2).2.2 (q z) ha (fun h => hj (Subtype.ext h.symm))

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.Mum.exists_sec_nonzero_on_fibre | exact GlobalTheory.Mum.exists_sec_nonzero_on_fibre | (intros; apply GlobalTheory.Mum.exists_sec_nonzero_on_fibre <;> assumption)
end
end
