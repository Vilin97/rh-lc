module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.KrullDimension
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
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
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
import Mathlib.Algebra.Order.Star.Int
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed

section

@[expose] public section

set_option autoImplicit false

open TopologicalSpace

namespace GlobalTheory

theorem exists_finite_topologicalKrullDim_inter_add_one_le {T : Type} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C →
      topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z := by
  obtain ⟨F, hF, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  choose g hg using fun t : F => QuasiSober.sober (hirr t.1 t.2) (hcl t.1 t.2)
  have := hF.to_subtype
  refine ⟨Set.range g, Set.finite_range g, fun C hC hd => ?_⟩
  refine topologicalKrullDim_add_one_le (hZ.inter hC) hZ ?_
  rintro x ⟨⟨t, ht, hxt⟩, -⟩
  exact ⟨g ⟨t, ht⟩, ⟨t, ht, (hg ⟨t, ht⟩).mem⟩, fun h => Set.disjoint_left.1 hd ⟨_, rfl⟩ h.2,
    (hg ⟨t, ht⟩).specializes hxt⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocal

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory

theorem restrictGlobal_appTop_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (a : Γ(X, ⊤)) :
    restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) = f.appLE V (f ⁻¹ᵁ V) le_rfl (restrictGlobal X V a) := by
  have h : f.app V (restrictGlobal X V a) = restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : V ⟶ ⊤).op) _
  rw [← h, Scheme.Hom.app_eq_appLE]

theorem length_sectionsOn_pullback_of_free (O : Type) [CommRing O] {X Y : Scheme.{0}}
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    (V : X.Opens) (n : ℕ) (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧
      Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n)
    (G : X.Modules) [G.IsQuasicoherent] :
    Module.length O (sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)) =
      n * Module.length O (sectionsOn G V) := by
  rw [Scheme.Hom.app_eq_appLE] at hfree
  letI := appLEAlgebra f (le_refl (f ⁻¹ᵁ V))
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  obtain ⟨hF, hFin, hr⟩ := hfree
  have hbc := isBaseChange_pullbackSections f G hU hV (le_refl (f ⁻¹ᵁ V))
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let ι := Module.Free.ChooseBasisIndex Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let E : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ V) ≃ₗ[Γ(X, V)] (ι → Γ(G, V)) :=
    (hbc.equiv.restrictScalars Γ(X, V)).symm ≪≫ₗ
      TensorProduct.congr b.equivFun (LinearEquiv.refl Γ(X, V) Γ(G, V)) ≪≫ₗ
      TensorProduct.comm _ _ _ ≪≫ₗ TensorProduct.piScalarRight _ _ _ _
  let A : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃+ (ι → sectionsOn G V) :=
    (sectionsOn.toΓ _ _).trans (E.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ (sectionsOn.toΓ G V).symm))
  let Φ : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃ₗ[O]
      (ι → sectionsOn G V) :=
    A.toLinearEquiv fun r x ↦ by
      funext i
      apply (sectionsOn.toΓ G V).injective
      change sectionsOn.toΓ G V ((sectionsOn.toΓ G V).symm
          (E (sectionsOn.toΓ _ _ (r • x)) i)) =
        sectionsOn.toΓ G V (r • (sectionsOn.toΓ G V).symm (E (sectionsOn.toΓ _ _ x) i))
      rw [AddEquiv.apply_symm_apply, sectionsOn.toΓ_smul, sectionsOn.toΓ_smul,
        AddEquiv.apply_symm_apply, ← hO, restrictGlobal_appTop_eq_appLE]
      rw [← appLEModule_smul, E.map_smul]
      rfl
  rw [Φ.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases subsingleton_or_nontrivial Γ(X, V) with hA | hA
  · haveI : Subsingleton Γ(G, V) := Module.subsingleton Γ(X, V) Γ(G, V)
    haveI : Subsingleton (sectionsOn G V) := (sectionsOn.toΓ G V).toEquiv.subsingleton_congr.2 this
    rw [Module.length_eq_zero_iff.2 this, mul_zero, mul_zero]
  · rw [← hr, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibre

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.FieldProj

theorem chi_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (k : Type)
    [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chi k F = (Module.length k (sectionsOn F ⊤)).toNat := by
  rw [chi_eq_hdim_zero k fun n hn => subsingleton_coh_of_suppDim_le_zero h hn, hdim_zero,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

theorem dim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

theorem closure_nonzeroLocus_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) {S : Set X} (hS : S.Finite) :
    AddSubgroup.closure {c : Pic X | ∃ (N : LB X) (hN : N.IsLB) (t : N.Sec),
      S ⊆ nonzeroLocus t ∧ c = cls N hN} = ⊤ := by
  refine eq_top_iff.2 fun c _ => ?_
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((hA.eventually_exists_finite_subset_nonzeroLocus hM hS).and
    (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) hS)).exists
  obtain ⟨P, hP, eP⟩ := cls_surj (cls M hM + n • cls A hA.isLB)
  obtain ⟨Q, hQ, eQ⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls A hA.isLB)
  obtain ⟨s, hs⟩ := h₁ P hP eP
  obtain ⟨t, ht⟩ := h₂ Q hQ eQ
  have e : cls M hM = cls P hP - cls Q hQ := by
    rw [eP, eQ, cls_triv, zero_add, add_sub_cancel_right]
  rw [e]
  exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
    (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)

theorem nonempty_pullback_structureModule_iso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback f).obj (QCoh.structureModule Y) ≅ QCoh.structureModule X) :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    final_of_representablyFlat _
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom) := inferInstance
  ⟨asIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom)⟩

section Main

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
  (f : X ⟶ Y) (hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r)
  (V : Y.Opens) (n : ℕ) (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
  (hfree : letI := (f.app V).hom.toAlgebra
    Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)

include hf hV hV' hfree

theorem chi_pullback_eq_mul [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (G : Y.Modules) [IsFiniteQC G] (hdim : suppDim G ≤ 0) (hsub : support G ⊆ (V : Set Y)) :
    chi k ((Scheme.Modules.pullback f).obj G) = n * chi k G := by
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set Y) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have hsupp' : support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
    QCoh.support_pullback f G
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f).obj G), IsClosed ({y} : Set X) := by
    intro y hy
    rw [hsupp'] at hy
    exact (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hy) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.base ⁻¹' {x}) hfin fun x hx =>
      (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hx) (hcl _ hx)).1).subset
      fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f).obj G) ≤ 0 :=
    dim_le_zero_of_finite_closed hfin' hpts
  rw [chi_eq_length_sections k _ hdim, chi_eq_length_sections k _ hdim',
    length_sectionsOn_top_eq_sum_of_separating G k (fun _ : Unit => V)
      (fun x hx => Set.mem_iUnion.2 ⟨(), hsub hx⟩) (fun i j hij => absurd rfl hij),
    length_sectionsOn_top_eq_sum_of_separating _ k (fun _ : Unit => f ⁻¹ᵁ V) ?_
      (fun i j hij => absurd rfl hij)]
  · simp_rw [length_sectionsOn_pullback_of_free k f hf _ n hV hV' hfree G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨(), hsub hy⟩

theorem diffVanish_chiPic_pullback_sub [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] {A : LB Y} (hA : IsAmpleLB A)
    (hX : ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists k F)
    (hY : ∀ (F : Y.Modules) [IsFiniteQC F], FiniteCohTwists k F) :
    ∀ (m : ℕ) (G : Y.Modules) [IsFiniteQC G], suppDim G ≤ m →
      topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) + 1 ≤ (m : WithBot ℕ∞) →
      DiffVanish m ((chiPic k ((Scheme.Modules.pullback f).obj G) ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) := by
  intro m
  induction m with
  | zero =>
    intro G _ h0 hk
    have hGU : support G ⊆ (V : Set Y) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f
    have := isFiniteQC_twist (F := G) hM
    have e := Twist.pullbackIso G f hM
    have hb := chi_pullback_eq_mul f hf V n hV hV' hfree (twist G M) (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f hM', chiPic_cls, chiPic_cls, ← chi_congr k e, hb, sub_self]
  | succ m ih =>
    intro G _ hk hUk
    set G' := (Scheme.Modules.pullback f).obj G
    have hZ : IsClosed (support G ∩ (V : Set Y)ᶜ) :=
      (isClosed_support (F := G)).inter V.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_topologicalKrullDim_inter_add_one_le _ hZ
    let S : Set Y := assPoints G ∪ f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (secPull t f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have h₁ := bwdDiff_chiPic_eq_chiPic_cut hN t (hY G)
    have h₂ := bwdDiff_chiPic_eq_chiPic_cut hN' (secPull t f) (hX G')
    obtain ⟨ec⟩ := cut_pullback_iso f G hN t hN'
    have key : bwdDiff (cls N hN) ((chiPic k G' ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) =
        (chiPic k ((Scheme.Modules.pullback f).obj (cut G hN t)) ∘ pull f) -
          (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f c)
      rw [chiPic_congr k ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih (cut G hN t) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set Y)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) ≤ m :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ m))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

end Main

theorem interNum_pull_eq_mul (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral Y]
    (sY : Y ⟶ Sp k) (f : X ⟶ Y) (hX : IsProjOver (f ≫ sY)) (hY : IsProjOver sY)
    (V : Y.Opens) (n : ℕ) (hgen : genericPoint Y ∈ V) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
        Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d) (L : Fin d → LB Y) (hL : ∀ i, (L i).IsLB) :
    letI := GlobalTheory.algebraΓOfHom (f ≫ sY); letI := GlobalTheory.algebraΓOfHom sY
    GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule X) (fun i => (L i).pull f) =
      (n : ℤ) * GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule Y) L := by
  letI := GlobalTheory.algebraΓOfHom (f ≫ sY)
  letI := GlobalTheory.algebraΓOfHom sY
  have := isNoetherian_of_isProjOver hX
  have := isNoetherian_of_isProjOver hY
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hY
  have hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r := fun _ => rfl
  have hVd : topologicalKrullDim ((V : Set Y)ᶜ : Set Y) + 1 ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDim_add_one_le V.isOpen.isClosed_compl isClosed_univ
      fun x _ => ⟨genericPoint Y, trivial, fun h => h hgen, genericPoint_specializes x⟩).trans ?_
    exact (topologicalKrullDim_subspace_le _ _).trans hd
  have hD := diffVanish_chiPic_pullback_sub f hf V n hV hV' hfree hA
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hX)
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hY) d (QCoh.structureModule Y)
    (suppDim_structureModule.trans_le hd)
    ((add_le_add_left (topologicalKrullDim_mono Set.inter_subset_right) 1).trans hVd)
  obtain ⟨e⟩ := nonempty_pullback_structureModule_iso f
  have h0 := congrFun (hD fun i => cls (L i) (hL i)) 0
  simp only [multiDiff_sub, multiDiff_map, multiDiff_comap, Pi.sub_apply, Pi.zero_apply,
    Function.comp_apply, chiPic_congr k e, map_zero] at h0
  rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
  rw [interNum_eq_multiDiff k _ hL,
    interNum_eq_multiDiff k _ fun i => Semi.LB.isLB_pull (hL i) f]
  exact h0

end GlobalTheory.FieldProj
end
end
end
