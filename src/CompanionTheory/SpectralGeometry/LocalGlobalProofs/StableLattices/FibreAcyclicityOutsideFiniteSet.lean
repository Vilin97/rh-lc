module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibres
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechAcyclicityOverAffineBaseStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechSliceAcyclicOfTruncation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibresStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.affine_cover_of_product_fibres : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | exact GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverSeparatingFiniteClosedPoints

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.CoverPoints

theorem exists_affine_cover_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  intro X _ F hF hc
  have hcl : ∀ G : Set X, G ⊆ F → IsClosed G := fun G hG => by
    have h := (hF.subset hG).isClosed_biUnion (fun x hx => hc x (hG hx))
    simpa using h

  have hW : ∀ x : F, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ ∀ y ∈ F, y ∈ W → y = x.1 := by
    intro x
    have hx : x.1 ∈ (F \ {x.1})ᶜ := fun h => h.2 rfl
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx
      (hcl _ Set.diff_subset).isOpen_compl
    refine ⟨W, hW, hxW, fun y hy hyW => ?_⟩
    by_contra hne
    exact hWo hyW ⟨hy, hne⟩
  choose W hWa hWx hWF using hW

  have hC : IsCompact ((⨆ x, W x : X.Opens) : Set X)ᶜ :=
    (⨆ x, W x : X.Opens).isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun U : {U : X.Opens // IsAffineOpen U ∧ ∀ x ∈ F, x ∉ U} => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro y hy
      have hy' : y ∈ Fᶜ := fun h => hy (by
        exact (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, h⟩, hWx ⟨y, h⟩⟩ : y ∈ (⨆ x, W x : X.Opens)))
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy'
        (hcl F subset_rfl).isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨U, hU, fun x hx hxU => hUo hxU hx⟩, hyU⟩)
  haveI : Fintype F := hF.fintype

  let V' : Option (F ⊕ s) → X.Opens := fun a => match a with
    | none => ⊥
    | some (Sum.inl x) => W x
    | some (Sum.inr U) => U.1.1
  have hV'a : ∀ a, IsAffineOpen (V' a) := by
    rintro (_ | x | U)
    · exact isAffineOpen_bot X
    · exact hWa x
    · exact U.1.2.1
  have hV'F : ∀ x (hx : x ∈ F) a, x ∈ V' a → a = some (Sum.inl ⟨x, hx⟩) := by
    rintro x hx (_ | y | U) h
    · exact absurd h (by simp [V'])
    · have : x = y.1 := hWF y x hx h
      subst this
      rfl
    · exact absurd h (U.1.2.2 x hx)
  let e : Option (F ⊕ s) ≃ Fin (Fintype.card (F ⊕ s) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨Fintype.card (F ⊕ s), fun j => V' (e.symm j), fun j => hV'a _, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hy : y ∈ (⨆ x, W x : X.Opens)
    · obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨e (some (Sum.inl x)), by simpa [V'] using hx⟩
    · obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs hy)
      exact ⟨e (some (Sum.inr ⟨U, hU⟩)), by simpa [V'] using hyU⟩
  · intro x hx i j hi hj
    exact e.symm.injective ((hV'F x hx _ hi).trans (hV'F x hx _ hj).symm)

end GlobalTheory.CompanionTheory.CoverPoints
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverSeparatingFiniteClosedPointsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.affine_cover_separating_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  first | exact @GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points | exact GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points | (intros; apply GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechSliceAcyclicOfTruncationStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.cech_slice_acyclic_of_truncation : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | exact GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.fibrewise_acyclicity_base_change : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | exact GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSet

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem exists_acyclic_cechLB_fibre : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG F hF hfib htot y₀ σ₀ hy h₁ h₂
  have hsepa : IsSeparated a := inferInstance
  have hsepb : IsSeparated b := inferInstance
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have hT' : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have hcX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have hcT : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  have hpp : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H.flip inferInstance
  have hcZ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ a)
  have hsepZ : IsSeparated (p ≫ a) := inferInstance
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have huniv : ({q₀} : Set (Sp k)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have hclosed (y : Sp k ⟶ T) (hy : y ≫ b = 𝟙 _) : IsClosed ({y q₀} : Set T) := by
    have : IsClosedImmersion (y ≫ b) := by rw [hy]; infer_instance
    have : IsClosedImmersion y := IsClosedImmersion.of_comp y b
    rw [← Set.image_singleton]
    refine y.isClosedEmbedding.isClosedMap _ ?_
    rw [huniv]
    exact isClosed_univ
  let F₁ : Set T := (fun y : Sp k ⟶ T => y q₀) '' ({y ∈ F | y ≫ b = 𝟙 _} ∪ {y₀})
  have hF₁ : F₁.Finite := (((hF.subset (Set.sep_subset _ _))).union (Set.finite_singleton _)).image _
  have hF₁c : ∀ x ∈ F₁, IsClosed ({x} : Set T) := by
    rintro _ ⟨y, hyF | rfl, rfl⟩
    · exact hclosed y hyF.2
    · exact hclosed _ hy
  obtain ⟨r, V, hV, hVc, hV₁⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points T F₁ hF₁ hF₁c
  obtain ⟨m', B, hB, hBc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points X ∅ Set.finite_empty (by simp)
  obtain ⟨d, D, hD, hDc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points Z ∅ Set.finite_empty (by simp)
  let U : Fin (m' + 1) → Z.Opens := fun i => p ⁻¹ᵁ B i
  let W : Fin (r + 1) → Z.Opens := fun j => q ⁻¹ᵁ V j
  have hT : ∀ n, Limits.IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G _ D _ U _ W hG hsepZ hD hDc
      (by simp only [U]; rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by simp only [W]; rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
      (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
      (fun i j => (GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j) B hB hBc G hG).1 i) n
    have hz := ((htot _ D hD hDc) n).isZero_homology
    have := ModuleCat.subsingleton_of_isZero hz
    have := e.symm.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hA : ∀ t : Finset (Fin (r + 1)), 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)) t)).Acyclic := by
    intro t ht
    have hne : t.Nonempty := Finset.card_pos.1 (by omega)
    have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
      IsAffineOpen.biInf _ t.finite_toSet hne fun j _ => hV j
    obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H hVt B hB hBc G hG
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W t _
      (preimage_biInf V q t)
    obtain ⟨j₁, hj₁, j₂, hj₂, hne'⟩ := Finset.one_lt_card.1 ht
    have hfac := GlobalTheory.T.fibrewise_acyclicity_base_change a b p q H ha G hG Γ(T, ⨅ j ∈ t, V j) hVt.fromSpec Y π f Hy
      (fun s σ hs hσ₁ hσ₂ => hfib (s ≫ hVt.fromSpec) σ (by simpa using hs) hσ₁ hσ₂ (by
        intro hmem
        have hp : hVt.fromSpec (s q₀) ∈ (⨅ j ∈ t, V j : T.Opens) :=
          hVt.range_fromSpec.le ⟨_, rfl⟩
        have hx : (s ≫ hVt.fromSpec) q₀ ∈ F₁ :=
          ⟨_, Or.inl ⟨hmem, by simpa using hs⟩, rfl⟩
        have hp' : (s ≫ hVt.fromSpec) q₀ ∈ (⨅ j ∈ t, V j : T.Opens) := by simpa using hp
        exact hne' (hV₁ _ hx j₁ j₂ (biInf_le V hj₁ hp') (biInf_le V hj₂ hp'))))
    have h := hfac _ E hE hEc
    exact fun n => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h n).of_iso (i₁ ≪≫ i₂)
  obtain ⟨j₀, hj₀⟩ : ∃ j, y₀ q₀ ∈ V j := by
    have : y₀ q₀ ∈ (⨆ j, V j : T.Opens) := hVc ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcol := GlobalTheory.T.cech_slice_acyclic_of_truncation _ hA hT j₀
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j₀) B hB hBc G hG
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W {j₀} (q ⁻¹ᵁ V j₀)
    (by simp [W])
  have hac₁ : (cechLB (f ≫ (hV j₀).fromSpec ≫ b) (G.pull π) E).Acyclic :=
    fun n => (hcol n).of_iso (i₁ ≪≫ i₂).symm
  have hac : (cechLB f (G.pull π) E).Acyclic :=
    GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic _ f _ E hac₁
  have hrange : Set.range y₀ ⊆ Set.range (hV j₀).fromSpec := by
    rw [(hV j₀).range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = q₀ := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hj₀
  let s : Sp k ⟶ Spec Γ(T, V j₀) := IsOpenImmersion.lift (hV j₀).fromSpec y₀ hrange
  have hs : s ≫ (hV j₀).fromSpec = y₀ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨D', hD', hD'c, hD'a⟩ := GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic a b p q H G hG Γ(T, V j₀) (hV j₀).fromSpec Y π f Hy E hE hEc hac
    s σ₀ (by rw [← Category.assoc, hs]; exact hy) h₁ (by rw [hs]; exact h₂)
  exact ⟨m' + 1, D', hD', hD'c, hD'a⟩

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end
end
