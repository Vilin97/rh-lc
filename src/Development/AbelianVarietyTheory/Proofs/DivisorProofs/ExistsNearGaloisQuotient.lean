module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpenStatement
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpenStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_invariant_nbhd_of_orbits {X : Scheme.{0}} [X.IsSeparated] {Γ : Type} [Group Γ] [Finite Γ]
    (act : Γ → (X ⟶ X)) (act_one : act 1 = 𝟙 X) (act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ)
    (Z : Set X) (hZ : IsCompact Z)
    (horb : ∀ z ∈ Z, ∃ O : X.Opens, IsAffineOpen O ∧ ∀ σ, act σ z ∈ O) :
    ∃ H : X.Opens, (∀ σ, act σ ⁻¹ᵁ H = H) ∧ (∀ z ∈ Z, z ∈ H) ∧ IsCompact (H : Set X) ∧
      (∀ x ∈ H, ∃ O : X.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) := by
  classical
  have hiso : ∀ σ, IsIso (act σ) := fun σ =>
    ⟨act σ⁻¹, by rw [← act_mul, mul_inv_cancel, act_one], by rw [← act_mul, inv_mul_cancel, act_one]⟩
  have hmul : ∀ σ τ (x : X), act (σ * τ) x = act τ (act σ x) := fun σ τ x => by
    rw [act_mul, Scheme.Hom.comp_apply]
  have hone : ∀ x : X, act 1 x = x := fun x => by rw [act_one]; rfl
  have hW : ∀ z : Z, ∃ V : X.Opens, IsAffineOpen V ∧ z.1 ∈ V ∧ ∀ σ, ∀ x ∈ V, act σ x ∈ V := by
    intro z
    obtain ⟨O, hO, hz⟩ := horb z.1 z.2
    have hmem : ∀ x : X, x ∈ (⨅ σ, act σ ⁻¹ᵁ O) ↔ ∀ σ, act σ x ∈ O := fun x => by
      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      rfl
    refine ⟨⨅ σ, act σ ⁻¹ᵁ O, IsAffineOpen.iInf fun σ => ?_, (hmem _).2 hz, fun σ x hx => (hmem _).2 fun τ => ?_⟩
    · have := hiso σ
      exact hO.preimage (act σ)
    · rw [← hmul]
      exact (hmem _).1 hx _
  choose V hV hzV hVa using hW
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun z : Z => (V z : Set X)) (fun z => (V z).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
  have hH : ∀ x : X, x ∈ (⨆ z ∈ t, V z) ↔ ∃ z ∈ t, x ∈ V z := fun x => by
    simp [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⨆ z ∈ t, V z, fun σ => ?_, fun z hz => ?_, ?_, fun x hx => ?_⟩
  · ext x
    change act σ x ∈ (⨆ z ∈ t, V z) ↔ x ∈ (⨆ z ∈ t, V z)
    rw [hH, hH]
    refine ⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, ?_⟩, fun ⟨z, hz, hx⟩ => ⟨z, hz, hVa z σ x hx⟩⟩
    have := hVa z σ⁻¹ _ hx
    rwa [← hmul, mul_inv_cancel, hone] at this
  · rw [hH]
    simpa using ht hz
  · have : ((⨆ z ∈ t, V z : X.Opens) : Set X) = ⋃ z ∈ t, (V z : Set X) := by
      ext x
      rw [SetLike.mem_coe, hH]
      simp
    rw [this]
    exact t.isCompact_biUnion fun z _ => (hV z).isCompact
  · obtain ⟨z, hz, hx⟩ := (hH x).1 hx
    exact ⟨V z, hV z, fun y hy => (hH y).2 ⟨z, hz, hy⟩, fun σ => hVa z σ x hx⟩

theorem eq_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {ρ : R →+* R'} (hρ : ρ.Finite) (p : Sp R') (hp : spMap ρ p = closedPoint R) : p = closedPoint R' := by
  have h₁ : Ideal.comap ρ (PrimeSpectrum.asIdeal p) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
  have h₂ : (PrimeSpectrum.asIdeal p).IsMaximal := by
    have := PrimeSpectrum.isPrime p
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ ?_
    rw [h₁]
    infer_instance
  exact PrimeSpectrum.ext (eq_maximalIdeal h₂)

theorem exists_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hS U' a
  classical
  have := hR.2
  have hR' : Base R' := ⟨hρ.1, charZero_of_injective_ringHom hρ.2.1⟩
  have := hG.1
  have := Fintype.ofFinite (Gal ρ)
  have := hS.separated
  have := hS.quasiCompact
  have : G'.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G'.hom]
    infer_instance⟩
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  have hover : ∀ (σ : Gal ρ) (g : G'.left), spMap ρ (G'.hom (a.act σ g)) = spMap ρ (G'.hom g) := fun σ g => by
    have h₁ : a.act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ) := (a.cart σ).1.w
    have h₂ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact σ.2 r
    rw [← Scheme.Hom.comp_apply (a.act σ), h₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (spMap (Gal.hom σ)), h₂]
  have hZ : IsClosed {g : G'.left | spMap ρ (G'.hom g) = closedPoint R} :=
    (isClosed_singleton_closedPoint R).preimage ((spMap ρ).continuous.comp G'.hom.continuous)
  refine exists_invariant_nbhd_of_orbits a.act a.act_one a.act_mul _ hZ.isCompact fun z hz => ?_
  obtain ⟨O, hO, h⟩ := GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen R' hR' D' A' G' hS U' (Finset.univ.image fun σ => a.act σ z) (fun x hx => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
    exact eq_closedPoint_of_finite hρ.2.2 _ ((hover σ z).trans hz))
  exact ⟨O, hO, fun σ => h _ (Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩)⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  first | exact @GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | exact GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | (intros; apply GlobalTheory.Mum.exists_invariant_nbhd_closedFibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_quotient_of_invariant_open {Γ : Type} [Group Γ] [Finite Γ] {Y S : Scheme.{0}} (act : Γ → (Y ⟶ Y))
    (h1 : act 1 = 𝟙 _) (hm : ∀ σ τ, act (σ * τ) = act σ ≫ act τ) (s : Y ⟶ S) (hs : ∀ σ, act σ ≫ s = s)
    (H : Y.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H)
    (hO : ∀ x ∈ H, ∃ O : Y.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) :
    ∃ (X : Over S) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ s ∧ IsAffineHom π ∧ Surjective π ∧
      (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) ∧
      (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) ∧
      ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V),
        (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  let r : Γ → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hr : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  have r1 : r 1 = 𝟙 _ := by
    rw [← cancel_mono H.ι, hr, h1, Category.id_comp, Category.comp_id]
  have rm : ∀ σ τ, r (σ * τ) = r σ ≫ r τ := fun σ τ => by
    rw [← cancel_mono H.ι, hr, hm, Category.assoc, hr, reassoc_of% hr]
  let ρ : Γ →* Aut H.toScheme := MonoidHom.mk'
    (fun σ => ⟨r σ⁻¹, r σ, by rw [← rm, inv_mul_cancel, r1], by rw [← rm, mul_inv_cancel, r1]⟩)
    (fun σ τ => Aut.ext (Iso.ext (show r (σ * τ)⁻¹ = r τ⁻¹ ≫ r σ⁻¹ by rw [mul_inv_rev, rm])))
  have hρ : ∀ σ, (ρ σ).asIso.hom = r σ⁻¹ := fun _ => rfl
  have hρ' : ∀ σ, r σ = (ρ σ⁻¹).asIso.hom := fun σ => by rw [hρ, inv_inv]
  have hpt : ∀ σ (x : H.toScheme), H.ι (r σ x) = act σ (H.ι x) := fun σ x => congr($(hr σ) x)
  have : OrbitsInAffineOpens ρ := ⟨fun x => by
    obtain ⟨O, hO₁, hO₂, hO₃⟩ := hO (H.ι x) x.2
    refine ⟨H.ι ⁻¹ᵁ O, hO₁.preimage_of_isOpenImmersion H.ι (by rwa [Scheme.Opens.opensRange_ι]), fun g => ?_⟩
    change H.ι (r g⁻¹ x) ∈ O
    rw [hpt]
    exact hO₃ _⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hinv : ∀ g, (ρ g).asIso.hom ≫ H.ι ≫ s = H.ι ≫ s := fun g => by
    rw [hρ, reassoc_of% hr, hs]
  refine ⟨Over.mk (hπ.desc (H.ι ≫ s) hinv), π, hπ.comp_desc _ hinv, hπ.isAffineHom, hπ.surjective, fun σ => ?_,
    fun x y hxy => ?_, fun V => ⟨hπ.app_injective V, fun f hf => ?_⟩⟩
  · exact (congrArg (· ≫ π) (hρ' σ)).trans (hπ.comp_eq _)
  · obtain ⟨g, rfl⟩ := (hπ.apply_eq_iff x y).mp hxy
    exact ⟨g⁻¹, (hpt _ _).symm⟩
  · exact hπ.mem_range_app V f fun g => ⟨hπ.preimage_le V g, hf g⁻¹ _⟩

theorem exists_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  intro R _ _ _ _ R' _ _ _ ρ _ hG D D' hD A' G' _ _ _ U' a H hH hO
  have := hG.1
  refine exists_quotient_of_invariant_open a.act a.act_one a.act_mul (G'.hom ≫ spMap ρ) (fun σ => ?_) H hH hO
  have e : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.2 x
  rw [← Category.assoc, (a.cart σ).1.w, Category.assoc, e]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galois_quotient_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  first | exact @GlobalTheory.Mum.exists_galois_quotient | exact GlobalTheory.Mum.exists_galois_quotient | (intros; apply GlobalTheory.Mum.exists_galois_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  first | exact @GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | exact GlobalTheory.Mum.quotient_smooth_and_baseChange_iso | (intros; apply GlobalTheory.Mum.quotient_smooth_and_baseChange_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNearGaloisQuotient

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ N : Near (spMap ρ) G', N.Law ∧ ∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS U' a
  obtain ⟨H, hH, hall, hc, horb⟩ := GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a
  obtain ⟨X, π, hX, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_galois_quotient_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb
  obtain ⟨N, hN⟩ := GlobalTheory.T.glue_local_descents_near_closedFibre_galois R hR R' ρ hF hG D D' hD A' G' hS U' a H hH hall hc X π hX h1 h2 h3 h4 h5
    (GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb X π hX h1 h2 h3 h4 h5)
  exact ⟨N, GlobalTheory.T.groupLaw_descends_galois_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a N hN, hN⟩

end GlobalTheory.Mum
end
end
end
