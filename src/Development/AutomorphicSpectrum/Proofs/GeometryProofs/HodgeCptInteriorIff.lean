module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtendToFractionFieldStatement
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnits
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SubfieldClosureEqTopOfEpi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem subfield_closure_eq_top_of_epi : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  intro O F _ _ β h
  set K := Subfield.closure (Set.range β) with hK
  by_contra hne
  have key := h (TensorProduct K F F) Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := F)).toRingHom (by
      ext o
      have ho : β o ∈ K := Subfield.subset_closure ⟨o, rfl⟩
      have e : β o = (⟨β o, ho⟩ : K) • (1 : F) := by
        rw [Subfield.smul_def, smul_eq_mul, mul_one]
      show β o ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] β o
      rw [e, TensorProduct.smul_tmul])
  have hlt : Submodule.span K {(1 : F)} < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro ht
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span K {(1 : F)} := ht ▸ Submodule.mem_top
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Subfield.smul_def, smul_eq_mul, mul_one]
    exact k.2
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have h1 : φ 1 = 0 := hφ (Submodule.mem_span_singleton_self 1)
  apply hφ0
  ext b
  have e : b ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] b := RingHom.congr_fun key b
  have e2 := congrArg (fun z => TensorProduct.lid K F (TensorProduct.map φ LinearMap.id z)) e
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, h1, zero_smul] at e2
  rcases smul_eq_zero.1 e2 with h | h
  · simpa using h
  · exact absurd h one_ne_zero

end PositivityTheory.UnitarySelfGeneration
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpiRingHomFieldClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem epi_subfield_closure_range_eq_top : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F),
    (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) →
    Subfield.closure (Set.range β) = ⊤ :=
  PositivityTheory.UnitarySelfGeneration.subfield_closure_eq_top_of_epi

end GlobalTheory.CompanionTheory.Ggeo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpiRingHomFieldClosureStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.epi_ring_hom_field_closure : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | exact GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top | (intros; apply GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GermVanishesOfGenericVanishing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem germ_vanishes_of_generic_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  intro X _ Ω O _ _ ξ hgen s₀ gm hcomp x a ha
  obtain ⟨t, ht⟩ : ∃ t, t = s₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) :=
    ⟨_, rfl⟩
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom gm)
  rw [← hcomp, Scheme.Hom.comp_appTop] at hnat
  have h1 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hnat) a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha, map_zero] at h1
  have hξt : ξ.appTop.hom t = 0 := by
    rw [ht]
    first
    | exact h1.symm
    | exact h1
  have hξt' : (ConcreteCategory.hom ξ.appTop) t = 0 := hξt
  have hpre := Scheme.preimage_basicOpen_top ξ t
  rw [hξt', Scheme.basicOpen_zero] at hpre
  have hbot : X.basicOpen t = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hmem : ξ (IsLocalRing.closedPoint Ω) ∈ X.basicOpen t :=
      (hgen q).mem_open (X.basicOpen t).isOpen hq
    have hc := (Scheme.Hom.mem_preimage ξ (U := X.basicOpen t)).mpr hmem
    rw [hpre] at hc
    exact (TopologicalSpace.Opens.mem_bot.mp hc).elim
  have ht0 : t = 0 := eq_zero_of_basicOpen_eq_bot t hbot
  have hnat2 := Scheme.ΓSpecIso_inv_naturality (Spec.preimage (X.fromSpecStalk x ≫ s₀))
  rw [Spec.map_preimage, Iso.comp_inv_eq] at hnat2
  rw [hnat2, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← ht, ht0, map_zero, map_zero]

end PositivityTheory.UnitarySelfGeneration
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.generic_vanishing_stalk_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | exact GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | (intros; apply GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.local_hom_char_zero_units : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | exact GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | (intros; apply GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
end
end
end
