module

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenStabilizer
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ExistsGalMapApply

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.GeoB

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem exists_galMap_apply [IsGalois k Ω] (y z : GlobalTheory.Et.geom Ω p)
    (h : pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) z) :
    ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ y = z := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  obtain ⟨R, f, hf, x₀, hx₀⟩ := Scheme.exists_Spec_apply_eq (pullback.fst p ψ y)
  let κ : CommRingCat.of k ⟶ R := Spec.preimage (f ≫ p)
  let _ : Algebra k R := κ.hom.toAlgebra
  let iΩ : CommRingCat.of Ω ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : R ⟶ CommRingCat.of (Ω ⊗[k] R) := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hout : IsPullback (Spec.map iΩ) (Spec.map iR) ψ (f ≫ p) := by
    have := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Ω R)
    rw [← Spec.map_preimage (f ≫ p)]
    exact this
  have t : IsPullback (pullback.snd p ψ) (pullback.fst p ψ) ψ p := (IsPullback.of_hasPullback p ψ).flip
  have L := IsPullback.of_right' hout t
  set Φ := t.lift (Spec.map iΩ) (Spec.map iR ≫ f) (by rw [hout.w, Category.assoc]) with hΦ
  have hΦs : Φ ≫ pullback.snd p ψ = Spec.map iΩ := t.lift_fst _ _ _
  have hΦf : Φ ≫ pullback.fst p ψ = Spec.map iR ≫ f := t.lift_snd _ _ _
  have hrange : ∀ w : GlobalTheory.Et.geom Ω p, pullback.fst p ψ w ∈ Set.range f → ∃ P, Φ P = w := by
    intro w hw
    have : w ∈ Set.range (pullback.fst (pullback.fst p ψ) f) := by
      rw [Scheme.Pullback.range_fst]; exact hw
    obtain ⟨v, rfl⟩ := this
    refine ⟨L.isoPullback.inv v, ?_⟩
    rw [← Scheme.Hom.comp_apply, L.isoPullback_inv_fst]
  obtain ⟨P, rfl⟩ := hrange y ⟨x₀, hx₀⟩
  obtain ⟨Q, rfl⟩ := hrange z ⟨x₀, hx₀.trans h⟩
  have hfst : ∀ P, pullback.fst p ψ (Φ P) = f (Spec.map iR P) := fun P => by
    rw [← Scheme.Hom.comp_apply, hΦf, Scheme.Hom.comp_apply]
  have hPQ : Spec.map iR P = Spec.map iR Q := f.isOpenEmbedding.injective (by rw [← hfst, ← hfst, h])
  have hPQ' : P.asIdeal.comap iR.hom = Q.asIdeal.comap iR.hom := congrArg PrimeSpectrum.asIdeal hPQ
  have : P.asIdeal.IsPrime := P.2
  have : Q.asIdeal.IsPrime := Q.2
  obtain ⟨σ, hσ⟩ := GeoA.exists_comap_eq (k := k) (Ω := Ω) R P.asIdeal Q.asIdeal hPQ'
  refine ⟨σ, ?_⟩
  let T : CommRingCat.of (Ω ⊗[k] R) ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom (GeoA.act R σ).toRingEquiv.toRingHom
  have hTR : iR ≫ T = iR := by
    ext r
    change GeoA.act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp
  have hTΩ : iΩ ≫ T = CommRingCat.ofHom (σ : Ω →+* Ω) ≫ iΩ := by
    ext a
    change GeoA.act R σ (a ⊗ₜ 1) = σ a ⊗ₜ 1
    simp
  have heq : Spec.map T ≫ Φ = Φ ≫ GlobalTheory.Et.galMap Ω p σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, hΦf, ← Category.assoc, ← Spec.map_comp, hTR]
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, hΦs, ← Category.assoc, hΦs, ← Spec.map_comp,
        ← Spec.map_comp, hTΩ]
  have hTP : Spec.map T P = Q := PrimeSpectrum.ext (by rw [Spec.map_apply]; exact hσ.symm)
  rw [← hTP, ← Scheme.Hom.comp_apply, ← heq, Scheme.Hom.comp_apply]

end CrystallineSemistableComparison.GeoB
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponent

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace CrystallineSemistableComparison.GeoC

theorem isOpen_connectedComponent {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  apply CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace <;> assumption

theorem image_connectedComponent {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  refine (h.continuous.image_connectedComponent_subset x).antisymm ?_
  intro y hy
  refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
  have := h.symm.continuous.image_connectedComponent_subset (h x) ⟨y, hy, rfl⟩
  rwa [h.symm_apply_apply] at this

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem galMap_comp_inv (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p σ⁻¹ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, mul_inv_cancel, GlobalTheory.EtC.galMap_one]

theorem galMap_inv_comp (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ⁻¹ ≫ GlobalTheory.Et.galMap Ω p σ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, inv_mul_cancel, GlobalTheory.EtC.galMap_one]

instance (σ : Ω ≃ₐ[k] Ω) : IsIso (GlobalTheory.Et.galMap Ω p σ) :=
  ⟨⟨GlobalTheory.Et.galMap Ω p σ⁻¹, galMap_comp_inv p σ, galMap_inv_comp p σ⟩⟩

def galHomeo (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.geom Ω p ≃ₜ GlobalTheory.Et.geom Ω p where
  toFun := GlobalTheory.Et.galMap Ω p σ
  invFun := GlobalTheory.Et.galMap Ω p σ⁻¹
  left_inv x := by rw [← Scheme.Hom.comp_apply, galMap_comp_inv]; rfl
  right_inv x := by rw [← Scheme.Hom.comp_apply, galMap_inv_comp]; rfl
  continuous_toFun := (GlobalTheory.Et.galMap Ω p σ).continuous
  continuous_invFun := (GlobalTheory.Et.galMap Ω p σ⁻¹).continuous

theorem galMap_mul_apply (σ τ : Ω ≃ₐ[k] Ω) (y : GlobalTheory.Et.geom Ω p) :
    GlobalTheory.Et.galMap Ω p (σ * τ) y = GlobalTheory.Et.galMap Ω p τ (GlobalTheory.Et.galMap Ω p σ y) := by
  rw [GlobalTheory.EtC.galMap_mul, Scheme.Hom.comp_apply]

theorem galMap_one_apply (y : GlobalTheory.Et.geom Ω p) : GlobalTheory.Et.galMap Ω p 1 y = y := by
  rw [GlobalTheory.EtC.galMap_one]; rfl

theorem exists_components [IsGalois k Ω] [Smooth p] [ConnectedSpace X] [CompactSpace X] :
    ∃ (r : ℕ) (U : Fin r → (GlobalTheory.Et.geom Ω p).Opens),
      (∀ s, IsIntegral (U s).toScheme) ∧ (∀ y, ∃ s, y ∈ U s) ∧
      (∀ s s', s ≠ s' → Disjoint (U s : Set (GlobalTheory.Et.geom Ω p)) (U s')) ∧
      (∀ (σ : Ω ≃ₐ[k] Ω) s, ∃ s', GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') ∧
      (∀ s s', ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  set Y := GlobalTheory.Et.geom Ω p
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  have : CompactSpace Y := by dsimp only [Y, GlobalTheory.Et.geom]; infer_instance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p ψ)
  have : IsNoetherian Y := {}
  have hopen : ∀ y : Y, IsOpen (connectedComponent y) := isOpen_connectedComponent
  have : DiscreteTopology (_root_.ConnectedComponents Y) := ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents Y) := finite_of_compact_of_discrete
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (_root_.ConnectedComponents Y)
  let C : Fin r → Set Y := fun s => ConnectedComponents.mk ⁻¹' {e.symm s}
  have hC : ∀ y : Y, C (e (ConnectedComponents.mk y)) = connectedComponent y := fun y => by
    simp only [C, Equiv.symm_apply_apply, connectedComponents_preimage_singleton]
  have hCrep : ∀ s, ∃ y : Y, C s = connectedComponent y := fun s => by
    obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe (e.symm s)
    exact ⟨y, by rw [← hC y, hy, Equiv.apply_symm_apply]⟩
  have hCopen : ∀ s, IsOpen (C s) := fun s => by
    obtain ⟨y, hy⟩ := hCrep s; rw [hy]; exact hopen y
  let U : Fin r → Y.Opens := fun s => ⟨C s, hCopen s⟩
  have hg : ∀ (σ : Ω ≃ₐ[k] Ω) (y : Y),
      GlobalTheory.Et.galMap Ω p σ '' connectedComponent y = connectedComponent (GlobalTheory.Et.galMap Ω p σ y) :=
    fun σ y => image_connectedComponent (galHomeo p σ) y
  refine ⟨r, U, fun s => ?_, fun y => ⟨e (ConnectedComponents.mk y), ?_⟩, fun s s' hss' => ?_,
    fun σ s => ?_, fun s s' => ?_⟩
  · obtain ⟨y, hy⟩ := hCrep s
    have : ConnectedSpace (U s).toScheme := by
      change ConnectedSpace (C s)
      rw [hy]
      exact isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    exact GlobalTheory.isIntegral_of_smooth_field ((U s).ι ≫ pullback.snd p ψ)
  · change y ∈ C _
    rw [hC]; exact mem_connectedComponent
  · change Disjoint (C s) (C s')
    refine Set.disjoint_left.2 fun y h1 h2 => hss' ?_
    simp only [C, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact e.symm.injective (h1.symm.trans h2)
  · obtain ⟨y, hy⟩ := hCrep s
    refine ⟨e (ConnectedComponents.mk (GlobalTheory.Et.galMap Ω p σ y)), ?_⟩
    change _ '' C s = C _
    rw [hy, hC, hg]
  · obtain ⟨y₀, hy₀⟩ := hCrep s
    obtain ⟨y₁, hy₁⟩ := hCrep s'

    let Z : Set Y := {y | ∃ σ : Ω ≃ₐ[k] Ω, y ∈ connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀)}
    have hZstab : ∀ (τ : Ω ≃ₐ[k] Ω) y, y ∈ Z → GlobalTheory.Et.galMap Ω p τ y ∈ Z := by
      rintro τ y ⟨σ, hσ⟩
      refine ⟨σ * τ, ?_⟩
      rw [galMap_mul_apply, ← hg]
      exact ⟨y, hσ, rfl⟩
    have hZo : IsOpen Z := by
      have : Z = ⋃ σ : Ω ≃ₐ[k] Ω, connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀) := by
        ext y; simp [Z]
      rw [this]; exact isOpen_iUnion fun σ => hopen _
    have hZc : IsOpen Zᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨connectedComponent y, fun w hw hwZ => hy ?_, hopen y, mem_connectedComponent⟩
      obtain ⟨σ, hσ⟩ := hwZ
      refine ⟨σ, ?_⟩
      rw [connectedComponent_eq hσ, ← connectedComponent_eq hw]
      exact mem_connectedComponent
    have hy₀Z : y₀ ∈ Z := ⟨1, by rw [galMap_one_apply]; exact mem_connectedComponent⟩
    have hZ : Z = Set.univ := by
      by_contra hne
      obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem Z).1 hne
      have : Algebra.IsIntegral k Ω := inferInstance
      have : IsIntegralHom ψ := IsIntegralHom.SpecMap_iff.2 (fun x => Algebra.IsIntegral.isIntegral x)
      have : Surjective ψ := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      have hcl := (pullback.fst p ψ).isClosedMap
      have hsurj := (pullback.fst p ψ).surjective
      set A := pullback.fst p ψ '' Z
      set B := pullback.fst p ψ '' Zᶜ
      have hAB : A = Bᶜ := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
          obtain ⟨σ, hσ⟩ := GeoB.exists_galMap_apply p a c hca.symm
          exact hc (hσ ▸ hZstab σ a ha)
        · intro hx
          obtain ⟨a, rfl⟩ := hsurj x
          by_cases ha : a ∈ Z
          · exact ⟨a, ha, rfl⟩
          · exact absurd ⟨a, ha, rfl⟩ hx
      have hAcl : IsClopen A :=
        ⟨hcl _ (isOpen_compl_iff.1 hZc), hAB ▸ (hcl _ hZo.isClosed_compl).isOpen_compl⟩
      rcases isClopen_iff.1 hAcl with h | h
      · exact (Set.eq_empty_iff_forall_notMem.1 h) _ ⟨y₀, hy₀Z, rfl⟩
      · have : pullback.fst p ψ b ∈ A := h ▸ Set.mem_univ _
        rw [hAB] at this
        exact this ⟨b, hb, rfl⟩
    have : y₁ ∈ Z := hZ ▸ Set.mem_univ _
    obtain ⟨σ, hσ⟩ := this
    refine ⟨σ, ?_⟩
    change _ '' C s = C s'
    rw [hy₀, hy₁, hg, connectedComponent_eq hσ]

end CrystallineSemistableComparison.GeoC
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

namespace GeoD


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isProper_pspace (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  apply _root_.UpperTheory.Gal.Seam.Spec.isProper_pstr <;> assumption

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_pspace R N
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

end GeoD

theorem geoMain : GeometricGenericComponents := by
  intro l _ K M hM d hC
  obtain ⟨hconn, hsm⟩ := hC
  have : Smooth M.q := SmoothOfRelativeDimension.smooth d M.q
  have : CompactSpace M.X := GeoD.compactSpace_of_isProjOver hM.1
  have : QuasiCompact M.p := quasiCompact_of_compactSpace M.p
  have : CompactSpace M.gen := inferInstance
  obtain ⟨r, U, hint, hcov, hdisj, hperm, htrans⟩ := GeoC.exists_components (Ω := PadicAlgCl l) M.q
  have hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty := fun s => by
    obtain ⟨⟨y, hy⟩⟩ := (hint s).nonempty
    exact ⟨y, hy⟩
  refine ⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩,
    hint, fun σ => ?_, fun s s' => ?_⟩
  · obtain ⟨s, hs⟩ := hcov y
    exact ⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hdisj s s' h
  · set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ)
    choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)
    have hginj : Function.Injective g := (GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra h
      have h1 : (U s : Set _) = U s' :=
        Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))
      obtain ⟨y, hy⟩ := hne s
      exact Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
    have hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι := fun s => by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hf s
    exact ⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s),
      fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩
  · obtain ⟨τ, hτ⟩ := htrans s s'
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    have hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hτ
    exact ⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

end CrystallineSemistableComparison
end
end
end
