module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipalStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAtStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOneStatement
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_locPrincipal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.cartier_at_of_locally_principal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


open TensorProduct in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  intro k A _ _ φ I h1 h2
  letI := φ.toAlgebra
  haveI hA : Algebra.Smooth k A := h1
  have halg : (Ideal.Quotient.algebra k : Algebra k (A ⧸ I)) =
      ((Ideal.Quotient.mk I).comp φ).toAlgebra := Algebra.algebra_ext _ _ fun _ => rfl
  have hQ : Algebra.FormallySmooth k (A ⧸ I) := by
    have hs : @Algebra.Smooth k _ (A ⧸ I) _ ((Ideal.Quotient.mk I).comp φ).toAlgebra := h2
    rw [← halg] at hs
    exact hs.formallySmooth
  haveI : Algebra.FormallySmooth k A := hA.formallySmooth
  haveI : Module.Projective A (KaehlerDifferential k A) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.FinitePresentation k A := hA.finitePresentation
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  haveI : Module.Finite A (KaehlerDifferential k A) := KaehlerDifferential.finite k A
  haveI : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] KaehlerDifferential k A) :=
    Module.Finite.base_change A (A ⧸ I) _
  haveI : IsScalarTower A (A ⧸ I) I.Cotangent := by
    first
    | infer_instance
    | exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := A ⧸ I)
    Ideal.Quotient.mk_surjective).mp hQ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := Ideal.Cotangent.equivOfEq _ _ (Ideal.mk_ker (I := I))
  let i : I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] KaehlerDifferential k A :=
    LinearMap.extendScalarsOfSurjective hsurj
      (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) ∘ₗ e.symm.toLinearMap)
  let s : (A ⧸ I) ⊗[A] KaehlerDifferential k A →ₗ[A ⧸ I] I.Cotangent :=
    LinearMap.extendScalarsOfSurjective hsurj (e.toLinearMap ∘ₗ l)
  have hsi : s ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun hl (e.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    first
    | (simp only [s, i, LinearMap.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, h, LinearEquiv.apply_symm_apply]; done)
    | (show e (l (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) (e.symm x))) = x
       rw [h, LinearEquiv.apply_symm_apply])
  refine ⟨Module.Finite.of_surjective s fun x => ⟨i x, ?_⟩, Module.Projective.of_split i s hsi⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hsi x
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmoothStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.conormal_finite_projective_of_smooth : ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth → ((Ideal.Quotient.mk I).comp φ).Smooth → Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | exact GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPair

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Charts

theorem smooth_affine_chart {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  let φ₀ : CommRingCat.of k ⟶ Γ(X, U.1) := Spec.preimage (U.2.fromSpec ≫ g)
  have h1 : Spec.map φ₀ = U.2.fromSpec ≫ g := Spec.map_preimage _
  refine ⟨φ₀.hom, ?_, ?_⟩
  · have : Smooth (Spec.map φ₀) := by
      rw [h1]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (IsAffineOpen.isOpenImmersion_fromSpec (hU := U.2)) hg
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · have hc : Z.subschemeCover.f U ≫ (Z.subschemeι ≫ g) =
        Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U))) := by
      rw [Spec.map_comp, h1, ← Category.assoc, Z.subschemeCover_map_subschemeι,
        Z.glueDataObjι_ι]
      exact Category.assoc _ _ _
    have : Smooth (Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U)))) := by
      rw [← hc]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (Z.subschemeCover.map_prop U) hZ
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this

end GlobalTheory.CompanionTheory.Hypotheses₂.Charts
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPairStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.exists_smooth_affine_presentation_pair : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem locPrincipal_locally_const {k A : Type} [Field k] [CommRing A] [IsDomain A] (φ : k →+* A) (I : Ideal A)
    (hφ : φ.Smooth) (hI : ((Ideal.Quotient.mk I).comp φ).Smooth) (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ s, s ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum A, s ∉ q.asIdeal → I ≤ q.asIdeal →
      (LocPrincipal I q.asIdeal ↔ LocPrincipal I p.asIdeal) := by
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.conormal_finite_projective_of_smooth φ I hφ hI
  have hnoeth : IsNoetherianRing A := by
    algebraize [φ]
    have : Algebra.FiniteType k A := inferInstance
    exact Algebra.FiniteType.isNoetherianRing k A
  have := Module.finitePresentation_of_projective (A ⧸ I) I.Cotangent
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) hsurj
  have hrange : ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
      ∃ Q : PrimeSpectrum (A ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q := by
    intro q hq
    have : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact hq
    exact this
  obtain ⟨P0, hP0⟩ := hrange p hp
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := A ⧸ I) I.Cotangent) :=
    Module.isLocallyConstant_rankAtStalk
  have hO := hlc.isOpen_fiber (Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0)
  obtain ⟨W, hW, hWO⟩ := hce.isInducing.isOpen_iff.1 hO
  have hpW : p ∈ W := by
    have : P0 ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by rw [hWO]; rfl
    rwa [Set.mem_preimage, hP0] at this
  obtain ⟨_, ⟨s, rfl⟩, hps, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpW hW
  refine ⟨s, hps, fun q hs hq => ?_⟩
  obtain ⟨Q, hQ⟩ := hrange q hq
  have hQO : Module.rankAtStalk (R := A ⧸ I) I.Cotangent Q = Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0 := by
    have : Q ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by
      rw [Set.mem_preimage, hQ]; exact hsW hs
    rw [hWO] at this
    exact this
  have e : ∀ R : PrimeSpectrum (A ⧸ I), LocPrincipal I (PrimeSpectrum.comap (Ideal.Quotient.mk I) R).asIdeal ↔ Module.rankAtStalk (R := A ⧸ I) I.Cotangent R = 1 :=
    fun R => ⟨GlobalTheory.T.conormal_rank_one_of_locally_principal I R, GlobalTheory.T.locally_principal_of_conormal_rank_one I R⟩
  rw [← hQ, ← hP0, e, e, hQO]

theorem fromSpec_mem_basicOpen_iff {X : Scheme.{0}} (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1))
    (f : Γ(X, U.1)) : U.2.fromSpec q ∈ X.basicOpen f ↔ f ∉ q.asIdeal := by
  have := U.2.fromSpec_preimage_basicOpen f
  have h2 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ q ∈ PrimeSpectrum.basicOpen f := by
    rw [this]; rfl
  exact h2

theorem isClosed_of_locally_iff {T : Type*} [TopologicalSpace T] {C : Set T} (hC : IsClosed C)
    (P : T → Prop) (h : ∀ x ∈ C, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ C → (P y ↔ P x)) :
    IsClosed {x | x ∈ C ∧ P x} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxC : x ∈ C
  · obtain ⟨V, hV, hxV, hy⟩ := h x hxC
    refine ⟨V, fun y hyV hyS => hx ⟨hxC, (hy y hyV hyS.1).1 hyS.2⟩, hV, hxV⟩
  · exact ⟨Cᶜ, fun y hy hyS => hy hyS.1, hC.isOpen_compl, hxC⟩

theorem isClosed_cartAt : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  intro k _ X g Z hg hX hZ
  have key : ∀ x ∈ (Z.support : Set X), ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ (Z.support : Set X) → (CartAt Z y ↔ CartAt Z x) := by
    intro x hx
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    let U' : X.affineOpens := ⟨U, hU⟩
    have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hdom : IsDomain Γ(X, U'.1) := inferInstanceAs (IsDomain Γ(X, U))
    obtain ⟨φ, hφ, hI⟩ := GlobalTheory.T.exists_smooth_affine_presentation_pair g Z U' hg hZ
    have hrange : ∀ y ∈ U, ∃ q, U'.2.fromSpec q = y := by
      intro y hy
      have : y ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hy
      exact this
    have hIq : ∀ q : PrimeSpectrum Γ(X, U'.1), U'.2.fromSpec q ∈ (Z.support : Set X) →
        Z.ideal U' ≤ q.asIdeal := by
      intro q hq f hf
      by_contra hfq
      have hb := (fromSpec_mem_basicOpen_iff U' q f).2 hfq
      have hmem : U'.2.fromSpec q ∈ (Z.support : Set X) ∩ (U'.1 : Set X) :=
        ⟨hq, X.basicOpen_le f hb⟩
      rw [Z.coe_support_inter U'] at hmem
      exact (Scheme.mem_zeroLocus_iff _ _ _).1 hmem.1 f hf hb
    obtain ⟨q0, rfl⟩ := hrange x hxU
    obtain ⟨s, hs, h⟩ := locPrincipal_locally_const φ (Z.ideal U') hφ hI q0 (hIq q0 hx)
    refine ⟨X.basicOpen s, (X.basicOpen s).isOpen, (fromSpec_mem_basicOpen_iff U' q0 s).2 hs, ?_⟩
    intro y hy hyZ
    obtain ⟨q, rfl⟩ := hrange y (X.basicOpen_le s hy)
    have := h q ((fromSpec_mem_basicOpen_iff U' q s).1 hy) (hIq q hyZ)
    exact ⟨fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q0 (this.1 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q hc)),
      fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q (this.2 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q0 hc))⟩
  have hC : IsClosed (Z.support : Set X) := Z.support.isClosed
  refine ⟨isClosed_of_locally_iff hC _ key, isClosed_of_locally_iff hC _ fun x hx => ?_⟩
  obtain ⟨V, hV, hxV, hy⟩ := key x hx
  exact ⟨V, hV, hxV, fun y hyV hyC => not_congr (hy y hyV hyC)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end
