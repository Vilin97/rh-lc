module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrEigenTangentExtensionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianExtensionOverDvrStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationLieLattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem fibAt_lat_eq_stdLat : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  intro X G _ Ω _ ξ Em _ _ M V K _ _ _ _ _ _ x z h₁ h₂ ψ g ℓ MX MC hx hpt hξ hle hint hfr hval
  subst hx
  have hMC : ∀ e, MC.pt e = MX.pt e := fun e => Over.OverMorphism.ext (hpt e)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨h, e, he, hv⟩
    have he' : e ∈ M.lat ⟨_, h₂⟩ := he
    rw [hfr.2] at he'
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    have hc : comb ℓ (fun i => (⟨(r i : Ω), hle (r i).2⟩ : regAt ξ ⟨_, h₁⟩)) = ∑ i, r i • ℓ i := rfl
    have h3 := hval (fun i => ⟨(r i : Ω), hle (r i).2⟩)
    rw [hc] at h3
    have e1 := LieModel.ValAt.unique hξ hv h3
    rw [hMC] at e1
    have e2 := MX.inj e1
    intro i
    rw [e2]
    exact hint _ _ (r i).2
  · intro w hw
    have hw' : ∀ i, w i ∈ (algebraMap V K).range := hw
    choose v hv using hw'
    have hsum : w = ∑ i, v i • (Pi.single i 1 : Fin g → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h₂, ℓ i, ?_, ?_⟩)
    · rw [hfr.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    · have h3 := hval (Pi.single i 1)
      have hc : comb ℓ (Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) = ℓ i := by
        unfold comb
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      have hs : (fun j => ψ ((Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) j)) = (Pi.single i 1 : Fin g → K) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hc, hs] at h3
      rw [hMC]
      exact h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationLieLatticeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_specialization_lie_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianPullbackTangentMap

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_cart_to_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)),
    ∃ φ₁ : tK.G.left ⟶ Y.t.G.left, IsGrpPullback tK.G Y.t.G (y ≫ Y.j) φ₁ ∧
      ∀ (u : epsAt (𝟙 (Sp K)) ⟶ tK.G) (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G),
        SameVec Y y v v' → u.left ≫ m.φ = v.left → u.left ≫ φ₁ = v'.left := by
  intro E _ _ _ H D l Xo c O _ β Y K _ y tK m
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hw : m.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact m.cart.1.w
  let φ' : tK.G.left ⟶ Y.oF.t.G.left := hp.lift m.φ (tK.G.hom ≫ y) hw
  have h1 : φ' ≫ Y.m0.toSABMap.φ = m.φ := hp.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = tK.G.hom ≫ y := hp.lift_snd _ _ _
  have hn : IsGrpPullback tK.G Xo.univ.t.G (y ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) :=
    by rw [h1]; exact m.cart
  have hc : IsGrpPullback tK.G Y.oF.t.G y φ' := IsGrpPullback.cancel Y.m0.toSABMap.cart hn h2
  refine ⟨φ' ≫ Y.m.φ, IsGrpPullback.comp hc Y.m.cart, ?_⟩
  rintro u v v' ⟨u', a, b, e⟩ huv
  have hu : u.left ≫ φ' = u' := by
    apply hp.hom_ext
    · rw [Category.assoc, h1, huv, b]
    · have wu : u.left ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) ≫ 𝟙 (Sp K) := Over.w u
      rw [Category.assoc, h2, ← Category.assoc, wu, a, Category.comp_id]
  rw [← Category.assoc, hu, e]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianPullbackTangentMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.semiabelian_pullback_tangent_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)),
    ∃ φ₁ : tK.G.left ⟶ Y.t.G.left, IsGrpPullback tK.G Y.t.G (y ≫ Y.j) φ₁ ∧
      ∀ (u : epsAt (𝟙 (Sp K)) ⟶ tK.G) (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G),
        SameVec Y y v v' → u.left ≫ m.φ = v.left → u.left ≫ φ₁ = v'.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationEigenFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan

theorem span_eq_eigSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K))
    (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K))
    (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y))
    (m' : SABMap tK T (spMap (algebraMap V K))) (n : ℕ) (σ : E →+* K) (σi : 𝓞 E →+* K) (b : Fin n → Fin g → K),
    spMap (algebraMap V K) ≫ z = y ≫ Y.j → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →
    (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    Z.M.lat.IsFrameAt ℓ ⟨_, h₂⟩ → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) →
    (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) →
    MU.IsActOf Xo.univ.t.act.act ρK → (∀ a : 𝓞 E, σi a = σ (a : E)) →
    IsIntFrame m m' σi (fun i => MU.pt (b i)) → LinearIndependent K b →
    Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z V K _ _ _ _ _ _ y z h₁ h₂ ψ g ℓ ρK MU MY T tK m m' n σ σi b hz hreg hint hfr₂ hfr₁ hsame hval hact hσ hif hli
  obtain ⟨ML, hML⟩ := (LieMove.main K Xo.X (under y) Xo.univ.t.G tK.G m.φ (Fin g → K) m.cart).1 MU
  obtain ⟨φ₁, hφ₁, htr⟩ := GlobalTheory.T.semiabelian_pullback_tangent_map E H D l Xo c O β Y K y tK m
  obtain ⟨σV, vV, hσV, hfr, hu⟩ := hif
  have hρ : ML.IsActOf tK.act.act ρK := by
    intro r e
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hML, hact r e, Over.comp_left, Over.comp_left, Category.assoc, m.act r, ← Category.assoc, hML]
    · rw [Over.w (ML.pt (ρK r e)), Over.comp_left, Category.assoc, Over.w (tK.act.act r), Over.w (ML.pt e)]
  have hepi : Epi (CommRingCat.ofHom (algebraMap V K)) := IsLocalization.epi (nonZeroDivisors V) K
  have hmono : Mono (spMap (algebraMap V K)) := by
    exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom (algebraMap V K)).op
  have hb : ∀ i, (ML.pt (b i)).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left := by
    intro i
    obtain ⟨u, hu1, hu2⟩ := hu i
    have hw : u ≫ tK.G.hom = (ML.pt (b i)).left ≫ tK.G.hom := by
      rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, ← m'.cart.1.w, ← Category.assoc, hu2,
        Category.assoc, Over.w (vV i), Over.w (ML.pt (b i))]
      exact (LieTangent.spec_dual_alg _ |>.trans (by simp))
    have : u = (ML.pt (b i)).left := m.cart.1.hom_ext (hu1.trans (hML _).symm) hw
    rw [← this]; exact hu2
  have key := GlobalTheory.T.dvr_eigen_tangent_extension V K T.G tK.G m'.φ (𝓞 E) T.act tK.act g n ML ρK σV vV b m'.cart m'.act hρ hfr hb
  have cast : ∀ (x x' : Sp K ⟶ Y.X) (_ : x = x') (M : LieModel Y.t.G x' (Fin g → K)),
      ∃ MC : LieModel Y.t.G x (Fin g → K), ∀ e, (MC.pt e).left = (M.pt e).left := by
    rintro _ _ rfl M
    exact ⟨M, fun _ => rfl⟩
  obtain ⟨MC, hMC⟩ := cast _ _ hz MY
  have hfib := GlobalTheory.T.dvr_specialization_lie_lattice Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V K (y ≫ Y.j) z h₁ h₂ ψ g ℓ MY MC hz hMC Z.gen hreg hint hfr₂ hval
  have hsm := Y.t.semi.smooth
  have h₁' : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) := by
    have : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z = y ≫ Y.j := hz
    rw [this]; exact h₁
  have hL : ∀ w, w ∈ stdLat V K g ↔ ∃ a : epsAt (𝟙 (Sp V)) ⟶ T.G, IsTanAt T.G (𝟙 _) a ∧
      (ML.pt w).left ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ a.left := by
    intro w
    have hA := GlobalTheory.T.semiabelian_extension_over_dvr V K Y.X Y.t.G T.G tK.G z m'.φ φ₁ Y.t.semi T.semi m'.cart (by rw [hz]; exact hφ₁) (ML.pt w) (ML.tan w)
    have hF := GlobalTheory.T.lie_lattice_eval_fraction_field Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M V z K (Fin g → K) MC Z.gen hsm h₂ h₁' w
    rw [hfib] at hF
    rw [hF, hA]
    have e : (ML.pt w).left ≫ φ₁ = (MC.pt w).left := by
      rw [hMC]; exact htr _ _ _ (hsame w) (hML w)
    rw [e]
  ext w
  rw [key w, ← hL w]
  show _ ↔ w ∈ stdLat V K g ⊓ (HT.eigSp ρK σ).restrictScalars V
  rw [Submodule.mem_inf]
  refine and_congr Iff.rfl ?_
  have : ∀ r, algebraMap V K (σV r) = σ (r : E) := fun r => by
    rw [← hσ r, ← hσV]; rfl
  simp [HT.eigSp, Submodule.mem_iInf, sub_eq_zero, this]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationEigenFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_specialization_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K))
    (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K))
    (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y))
    (m' : SABMap tK T (spMap (algebraMap V K))) (n : ℕ) (σ : E →+* K) (σi : 𝓞 E →+* K) (b : Fin n → Fin g → K),
    spMap (algebraMap V K) ≫ z = y ≫ Y.j → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →
    (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    Z.M.lat.IsFrameAt ℓ ⟨_, h₂⟩ → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) →
    (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) →
    MU.IsActOf Xo.univ.t.act.act ρK → (∀ a : 𝓞 E, σi a = σ (a : E)) →
    IsIntFrame m m' σi (fun i => MU.pt (b i)) → LinearIndependent K b →
    Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan.span_eq_eigSub | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan.span_eq_eigSub | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IntFrameSpan.span_eq_eigSub <;> assumption)
end
end
