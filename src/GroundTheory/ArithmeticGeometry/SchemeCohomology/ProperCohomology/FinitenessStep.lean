module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ExistsGeneratingSectionsTwist
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Immersion
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ExistsChow
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
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
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackUnit
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelativeSerre
public import Mathlib.AlgebraicGeometry.Restrict
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionBasis
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionTensor
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SupportMore
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.IrreducibleImage

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

lemma isIso_opens_ι_restrict {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩

theorem exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hC := irreducibleComponent_mem_irreducibleComponents z
  set C := irreducibleComponent z
  set O := Z.irreducibleComponentOpen C
  refine ⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance,
    inferInstance, ?_, ?_⟩
  · obtain ⟨o, ho, hne, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC

    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
    have : (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := rfl
    rw [this, Set.compl_empty_iff] at h
    rw [h, Set.compl_univ, closure_empty] at hcl
    exact hC.1.nonempty.ne_empty hcl.symm
  · have hI := Z.irreducibleComponentIdeal_def C hC
    have : IsIso (O.ι ∣_ O) := isIso_opens_ι_restrict O
    have key := SchemeImage.imageRestrictLift_fac O.ι O
    change IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)
    rw [hI]
    change IsIso (O.ι.imageι ∣_ O)
    rw [← key]
    infer_instance

end

end GroundTheory.Arith.SchemeCoh
end
end

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictIso

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma isIso_morphismRestrict_of_le {U U' : Y.Opens} (h : U' ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ U') := by
  have h1 : IsPullback (f ∣_ U') (f ⁻¹ᵁ U').ι U'.ι f := isPullback_morphismRestrict f U'
  have h2 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have hU : Y.homOfLE h ≫ U.ι = U'.ι := Y.homOfLE_ι h
  have hX : X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U').ι := X.homOfLE_ι _
  have hsq : X.homOfLE (f.preimage_mono h) ≫ f ∣_ U = f ∣_ U' ≫ Y.homOfLE h := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Category.assoc, hU,
      morphismRestrict_ι, ← Category.assoc, hX]
  have h3 : IsPullback (X.homOfLE (f.preimage_mono h)) (f ∣_ U') (f ∣_ U) (Y.homOfLE h) := by
    refine IsPullback.of_right ?_ hsq h2.flip
    rw [hX, hU]
    exact h1.flip
  exact h3.isIso_snd_of_isIso

lemma bijective_app_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {V : Y.Opens}
    (hV : V ≤ U) : Function.Bijective (f.app V) := by
  have := isIso_morphismRestrict_of_le f hV
  have h0 : IsIso ((f ∣_ V).app ⊤) := inferInstance
  have h1 : IsIso (f.app (V.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op) := by
    rw [← morphismRestrict_app]
    exact h0
  have h2 : IsIso (f.app (V.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right _
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op)
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h2
  exact ConcreteCategory.bijective_of_isIso _

lemma injOn_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] :
    Set.InjOn f.base (f ⁻¹ᵁ U : Set X) := by
  intro a ha b hb hab
  have hinj : Function.Injective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).injective
  have := @hinj ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext
    ((morphismRestrict_base_coe f U ⟨a, ha⟩).trans (hab.trans
      (morphismRestrict_base_coe f U ⟨b, hb⟩).symm)))
  exact congrArg Subtype.val this

lemma exists_preimage_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {y : Y}
    (hy : y ∈ U) : ∃ x : X, x ∈ f ⁻¹ᵁ U ∧ f.base x = y := by
  have hsurj : Function.Surjective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).surjective
  obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
  refine ⟨x, hx, ?_⟩
  exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm.trans (congrArg Subtype.val hxy)

end

end GroundTheory.Arith.SchemeCoh
end
end

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FinitenessStep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

lemma isClosedImmersion_of_isIso' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f :=
  inferInstance

theorem isCoherent_unit (X : Scheme.{u}) : IsCoherent (𝟙_ X.Modules) := by
  refine ⟨isQuasicoherent_unit X, fun U _ => ?_⟩
  let one : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have hm : m = (show Γ(X, U) from m) • one := (mul_one (show Γ(X, U) from m)).symm
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self _)))

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

theorem finiteH_step
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))]
    (T : Set X) (hT : IsClosed T)
    (IH : ∀ T' : Set X, IsClosed T' → T' ⊂ T → ∀ F : X.Modules, IsCoherent F →
      Scheme.Modules.SupportedIn F T' → FiniteH.{u} A F)
    (F : X.Modules) (hF : IsCoherent F) (hFT : Scheme.Modules.SupportedIn F T) :
    FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := hF.1
  obtain ⟨I, hIT, G, hG, ⟨e⟩⟩ := exists_pushforward_iso_of_supportedIn F hF hT hFT
  have hFI : Scheme.Modules.SupportedIn F (I.support : Set X) := by
    have h := (Scheme.Modules.SupportedIn.univ G).pushforward I.subschemeι
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
    exact h.of_iso e
  by_cases hST : (I.support : Set X) = T
  swap
  · exact IH _ I.support.isClosed (lt_of_le_of_ne hIT hST) F hF hFI
  rcases isEmpty_or_nonempty I.subscheme with hZ | hZ
  · have h0 : (I.support : Set X) = ∅ := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.range_eq_empty _
    exact FiniteH.of_isZero A (Scheme.Modules.SupportedIn.isZero_of_empty (h0 ▸ hFI))
  set Z := I.subscheme
  set j : Z ⟶ X := I.subschemeι
  let _ : Z.Over (Spec (.of A)) := ⟨j ≫ (X ↘ Spec (.of A))⟩
  have : IsProper (Z ↘ Spec (.of A)) := (inferInstance : IsProper (j ≫ (X ↘ Spec (.of A))))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of A))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of A))
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨Z₁, c, O, hc, hirr, hOne, hcO⟩ := exists_irreducible_isIso_restrict Z
  let _ : Z₁.Over (Spec (.of A)) := ⟨c ≫ (Z ↘ Spec (.of A))⟩
  have : IsProper (Z₁ ↘ Spec (.of A)) := (inferInstance : IsProper (c ≫ (Z ↘ Spec (.of A))))
  obtain ⟨N, Z', i, π, U₁, hi, hiπ, hU₁, hπU⟩ := exists_chow (A := A) Z₁
  set ψ : Z' ⟶ X := π ≫ c ≫ j with hψ
  let _ : Z'.Over (Spec (.of A)) := ⟨ψ ≫ (X ↘ Spec (.of A))⟩
  have : ψ.IsOver (Spec (.of A)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of A)) := ⟨by
    change i ≫ ProjSpace.toSpecBase A N = (π ≫ c ≫ j) ≫ (X ↘ Spec (.of A))
    rw [hiπ]
    simp only [Category.assoc]
    rfl⟩
  have hZ'p : IsProper (ψ ≫ (X ↘ Spec (.of A))) := by
    have h : ψ ≫ (X ↘ Spec (.of A)) = i ≫ ProjSpace.toSpecBase A N :=
      (CategoryTheory.comp_over i (Spec (.of A))).symm
    rw [h]
    infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (X ↘ Spec (.of A))
  have : IsClosedImmersion (c ≫ j) := inferInstance

  have hG' : IsCoherent ((Scheme.Modules.pullback ψ).obj F) := isCoherent_pullback ψ hF
  set G' := (Scheme.Modules.pullback ψ).obj F
  obtain ⟨n₀, hn₀⟩ := ProjScheme.exists_relativeSerre i ψ G' hG'
  letI : (𝟙_ Z'.Modules).IsQuasicoherent := isQuasicoherent_unit Z'
  obtain ⟨n₁, hn₁⟩ := ProjScheme.exists_generatingSections_twist i (𝟙_ Z'.Modules)
    (isCoherent_unit Z')
  set n := max n₀ n₁
  obtain ⟨σ, hσ⟩ := hn₁ n (le_max_right _ _)
  set L := ProjScheme.twistingSheaf i (n : ℤ)
  have eL : ProjScheme.twist i (𝟙_ Z'.Modules) (n : ℤ) ≅ L := λ_ L
  obtain ⟨σL, hσL⟩ := exists_generatingSections_of_iso eL ⟨σ, hσ⟩
  have : L.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z'.ringCatSheaf).prop_of_iso eL
      (ProjScheme.isQuasicoherent_twist i (𝟙_ Z'.Modules) (n : ℤ))
  have hL : IsInvertibleSheaf L := ProjScheme.isInvertibleSheaf_twistingSheaf i (n : ℤ)

  have hcO' : ((c ⁻¹ᵁ O : Z₁.Opens) : Set Z₁).Nonempty := by
    obtain ⟨o, ho⟩ := hOne
    obtain ⟨z, hz, -⟩ := exists_preimage_of_isIso_morphismRestrict c ho
    exact ⟨z, hz⟩
  obtain ⟨z, hzU, hzO⟩ := nonempty_preirreducible_inter U₁.isOpen (c ⁻¹ᵁ O).isOpen hU₁ hcO'
  obtain ⟨y, hyU, hyz⟩ := exists_preimage_of_isIso_morphismRestrict π hzU
  obtain ⟨k, W', hyW', hbasis⟩ := exists_isBasisOn_generatingSection L hL σL y
  set s : Γ(L, ⊤) := (σL.s k).val (op ⊤)
  set Φ := (Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G' n)
  let α : F ⟶ Φ := (Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F ≫
    (Scheme.Modules.pushforward ψ).map (mulSection G' L s)

  set Wg : Z'.Opens := W' ⊓ π ⁻¹ᵁ (U₁ ⊓ c ⁻¹ᵁ O)
  set Bad : Set X := ψ.base '' (Wg : Set Z')ᶜ ∪ j.base '' (O : Set Z)ᶜ ∪
    (c ≫ j).base '' (U₁ : Set Z₁)ᶜ
  have hBad : IsClosed Bad :=
    ((ψ.isClosedMap _ Wg.isOpen.isClosed_compl).union
      (j.isClosedMap _ O.isOpen.isClosed_compl)).union
      ((c ≫ j).isClosedMap _ U₁.isOpen.isClosed_compl)
  obtain ⟨W, hWdef⟩ : ∃ W : X.Opens, (W : Set X) = Badᶜ := ⟨⟨Badᶜ, hBad.isOpen_compl⟩, rfl⟩
  have hcjinj : Function.Injective (c ≫ j).base := (c ≫ j).isClosedEmbedding.injective
  have hjinj : Function.Injective j.base := j.isClosedEmbedding.injective
  have hψy : ψ.base y = (c ≫ j).base (π.base y) := rfl
  have hyWg : y ∈ Wg := ⟨hyW', by
    change π.base y ∈ U₁ ⊓ c ⁻¹ᵁ O
    rw [hyz]
    exact ⟨hzU, hzO⟩⟩
  have hxW : ψ.base y ∈ W := by
    change ψ.base y ∈ (W : Set X)
    rw [hWdef]
    rintro ((⟨y', hy', hyy'⟩ | ⟨o, ho, hoy⟩) | ⟨z', hz', hzy⟩)
    · have h1 : π.base y' = π.base y := hcjinj hyy'
      have hy'U : y' ∈ π ⁻¹ᵁ U₁ := by
        change π.base y' ∈ U₁
        rw [h1, hyz]
        exact hzU
      exact hy' (injOn_of_isIso_morphismRestrict π hy'U hyU h1 ▸ hyWg)
    · have h1 : o = c.base (π.base y) := hjinj hoy
      apply ho
      rw [h1, hyz]
      exact hzO
    · have h1 : z' = π.base y := hcjinj hzy
      apply hz'
      rw [h1, hyz]
      exact hzU
  have hψW : ψ ⁻¹ᵁ W ≤ Wg := fun y' hy' => by
    have hy' : ψ.base y' ∈ (W : Set X) := hy'
    rw [hWdef] at hy'
    by_contra h
    exact hy' (Or.inl (Or.inl ⟨y', h, rfl⟩))
  have hjW : j ⁻¹ᵁ W ≤ O := fun z' hz' => by
    have hz' : j.base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inl (Or.inr ⟨z', h, rfl⟩))
  have hcjW : (c ≫ j) ⁻¹ᵁ W ≤ U₁ := fun z' hz' => by
    have hz' : (c ≫ j).base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inr ⟨z', h, rfl⟩)

  have hπW : IsIso (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) := isIso_morphismRestrict_of_le π hcjW
  have : IsClosedImmersion (ψ ∣_ W) := by
    have h1 : IsClosedImmersion (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) :=
      @isClosedImmersion_of_isIso' _ _ _ hπW
    have h2 : IsClosedImmersion ((c ≫ j) ∣_ W) := inferInstance
    rw [show ψ = π ≫ (c ≫ j) from rfl, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ h1 h2

  have hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 →
      ∀ m : Γ(F, V), a • m = 0 := by
    intro V _ hVW a ha m
    have hVc : (c ≫ j) ⁻¹ᵁ V ≤ U₁ := (Scheme.Hom.preimage_mono _ hVW).trans hcjW
    have hVj : j ⁻¹ᵁ V ≤ O := (Scheme.Hom.preimage_mono _ hVW).trans hjW
    have hπinj := (bijective_app_of_isIso_morphismRestrict π hVc).1
    have hcinj := (bijective_app_of_isIso_morphismRestrict c hVj).1
    have hja : j.app V a = 0 := by
      apply hcinj
      apply hπinj
      calc _ = (ψ.app V) a := rfl
        _ = 0 := ha
        _ = _ := by rw [map_zero]; exact (map_zero _).symm
    obtain ⟨m', rfl⟩ : ∃ m', e.hom.app V m' = m :=
      ⟨e.inv.app V m, by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]⟩
    have h0 : a • m' = 0 := by
      rw [smul_pushforward, hja, zero_smul]
      rfl
    rw [← Scheme.Modules.Hom.app_smul, h0, map_zero]
  have hunit := bijective_unit_app_of_le ψ F W hkill
  have hmul := bijective_mulSection_app G' L s hbasis
  have hα : ∀ V : X.Opens, V ≤ W → Function.Bijective (α.app V) := fun V hV =>
    (hmul (ψ ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hV).trans (hψW.trans inf_le_left))).comp
      (hunit V hV)

  obtain ⟨hΦcoh, hΦiso⟩ := hn₀ n (le_max_left _ _)
  have hΦ : FiniteH.{u} A Φ := fun p => by
    obtain ⟨e'⟩ := hΦiso p
    have := ProjScheme.finite_H.{u} i (ProjScheme.twist i G' n)
      (isCoherent_tensor_of_invertible hG' hL) p
    exact Module.Finite.equiv e'

  have hxT : ψ.base y ∈ T := by
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y), rfl⟩
  have hT' : IsClosed (T ∩ (W : Set X)ᶜ) := hT.inter W.isOpen.isClosed_compl
  have hT'T : T ∩ (W : Set X)ᶜ ⊂ T :=
    ⟨Set.inter_subset_left, fun h => (h hxT).2 hxW⟩
  have hK : FiniteH.{u} A (kernel α) :=
    have := hΦcoh.1
    IH _ hT' hT'T (kernel α) (isCoherent_kernel α hF)
      ((hFT.of_mono (kernel.ι α)).inter (kernel_supportedIn α W hα) hT W.isOpen.isClosed_compl)
  have hΦT : Scheme.Modules.SupportedIn Φ T := by
    refine ((Scheme.Modules.SupportedIn.univ _).pushforward ψ).mono ?_
    rintro _ ⟨y', -, rfl⟩
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y'), rfl⟩
  have hC : FiniteH.{u} A (cokernel α) :=
    IH _ hT' hT'T (cokernel α) (isCoherent_cokernel α hΦcoh)
      ((hΦT.of_epi (cokernel.π α)).inter (cokernel_supportedIn α W hα) hT
        W.isOpen.isClosed_compl)
  exact FiniteH.of_shortExact₂ (kerCoimSC_shortExact α) hK
    (FiniteH.of_shortExact₁ (coimCokSC_shortExact α) hΦ hC)

theorem finiteH_of_supportedIn
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (T : Closeds X) :
    ∀ F : X.Modules, IsCoherent F → Scheme.Modules.SupportedIn F T → FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have : IsNoetherian X := ⟨⟩
  induction T using WellFoundedLT.induction with
  | _ T IH =>
    intro F hF hFT
    refine finiteH_step X T T.isClosed (fun T' hT' hlt F' hF' hF'T' => ?_) F hF hFT
    exact IH ⟨T', hT'⟩ hlt F' hF' hF'T'

end

end GroundTheory.Arith.SchemeCoh
end
end
