module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangentsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenConditionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspaceStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModelStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

theorem mem_prime_germ_eq_zero {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) (x : A)
    (hF : IsField (X.presheaf.stalk x.1)) (f : Γ(X, A)) (hf : f ∈ (hA.primeIdealOf x).asIdeal) :
    X.presheaf.germ A x.1 x.2 f = 0 := by
  have hl := hA.isLocalization_stalk x
  have h1 : algebraMap Γ(X, A) (X.presheaf.stalk x.1) f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1)
      (hA.primeIdealOf x).asIdeal f).2 hf
  have h2 : ¬ IsUnit (algebraMap Γ(X, A) (X.presheaf.stalk x.1) f) := h1
  by_contra h0
  exact h2 (by
    let _ := hF.toField
    exact IsUnit.mk0 _ h0)

theorem germ_injective {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) [IsDomain Γ(X, A)] (x : A) :
    Function.Injective (X.presheaf.germ A x.1 x.2) := by
  have hl := hA.isLocalization_stalk x
  exact IsLocalization.injective (X.presheaf.stalk x.1)
    (M := (hA.primeIdealOf x).asIdeal.primeCompl)
    ((hA.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors)

theorem genPt_specializes_of_isDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  intro X Ω _ ξ A hA p hgen hdom hp z hz
  have hx : genPt ξ ∈ A := p.2.mem_open A.2 hp
  let x : A := ⟨genPt ξ, hx⟩
  let q : A := ⟨p.1, hp⟩
  have hF : IsField (X.presheaf.stalk x.1) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hgen.bij).toMulEquiv
  have hbot : (hA.primeIdealOf x).asIdeal = ⊥ := by
    refine le_antisymm (fun f hf => ?_) bot_le
    have h0 := mem_prime_germ_eq_zero hA x hF f hf
    have h1 : X.presheaf.germ A p.1 hp f = 0 := by
      apply hgen.inj p
      have h2 : X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f) =
          X.presheaf.germ A (genPt ξ) hx f := by
        exact congr($(X.presheaf.germ_stalkSpecializes hp p.2).hom f)
      rw [map_zero]
      change (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f)) = 0
      rw [h2]
      have h3 : X.presheaf.germ A (genPt ξ) hx f = 0 := h0
      rw [h3]
      exact map_zero (Scheme.stalkClosedPointTo ξ).hom
    exact germ_injective hA q (h1.trans (map_zero _).symm)
  obtain ⟨t, rfl⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  have hs : hA.primeIdealOf x ⤳ t := by
    refine (PrimeSpectrum.le_iff_specializes (hA.primeIdealOf x) t).1 ?_
    change (hA.primeIdealOf x).asIdeal ≤ _
    rw [hbot]
    exact bot_le
  have := hs.map hA.fromSpec.continuous
  rwa [hA.fromSpec_primeIdealOf] at this

end GlobalTheory.CompanionTheory.Ar.LocFrames
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.affine_domain_generic_specializes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | exact GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.SubFrame

theorem isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  intro X Ω _ ξ E _ _ L V' q g n b ix hix hb hL hV
  subst hV
  refine And.intro (hb.comp ix hix) ?_
  show L q ⊓ Submodule.restrictScalars (regAt ξ q) (Submodule.span Ω (Set.range (b ∘ ix))) = _
  rw [hL]
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ Submodule.span Ω (Set.range (b ∘ ix)) := hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx1
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hx2'
    have hc' : ∑ i, (c i : Ω) • b i = x := hc
    have hD : ∑ i, (∑ j, if ix j = i then d j else 0) • b i = x := by
      rw [← hd]
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    have key : ∀ i, (c i : Ω) = ∑ j, if ix j = i then d j else 0 := by
      have h0 := Fintype.linearIndependent_iff.1 hb
        (fun i => (c i : Ω) - ∑ j, if ix j = i then d j else 0) (by
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [hc', hD, sub_self])
      intro i
      exact sub_eq_zero.1 (h0 i)
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    by_cases h : ∃ j, ix j = i
    · obtain ⟨j, rfl⟩ := h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp only [not_exists] at h
      have hci : c i = 0 := by
        apply Subtype.ext
        rw [key i]
        simp [h]
      rw [hci, zero_smul]
      exact Submodule.zero_mem _
  · apply le_inf
    · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
    · exact Submodule.span_le_restrictScalars _ _ _

end GlobalTheory.CompanionTheory.Ar.SubFrame
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.lattice_frame_sub_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames

theorem exists_affine_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ p₀ hO hτ h1 h2 h3 h4 hp₀
  obtain ⟨hinj, hnoeth, hfr⟩ := hO
  haveI := hnoeth
  have := projProper _ _ _ Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3c, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ ⟨hinj, hnoeth, hfr⟩ hτ
  obtain ⟨g, b, hb, hS⟩ := h3c p₀ hp₀
  obtain ⟨S₁, hS₁⟩ := hS τ
  obtain ⟨S₂, hS₂⟩ := hS (ComplexEmbedding.conjugate τ)
  obtain ⟨hspan, N, hpN, hN⟩ := GlobalTheory.T.lattice_frame_open_condition Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ g b hb
  have e₁ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) p₀ g b S₁ Z.gen hspan hb.2 hS₁
  have e₂ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) p₀ g b S₂
    Z.gen hspan hb.2 hS₂
  have card : ∀ (S : Finset (Fin g)) (n : ℕ) (u : Fin n → Z.V), LinearIndependent Z.Ω u →
      Submodule.span Z.Ω (Set.range u) = Submodule.span Z.Ω (b '' S) → S.card = n := by
    intro S n u hu hsp
    have a₁ := finrank_span_eq_card hu
    have a₂ := finrank_span_eq_card (hb.1.comp (Subtype.val : S → Fin g) Subtype.val_injective)
    have a₃ : Set.range (b ∘ (Subtype.val : S → Fin g)) = b '' S := by
      rw [Set.range_comp, Subtype.range_coe]
    rw [a₃, ← hsp, a₁] at a₂
    simpa using a₂.symm
  have c₁ := card S₁ D.p b₁ h1 (h2.trans e₁)
  have c₂ := card S₂ D.q b₂ h3 (h4.trans e₂)
  let ι₁ := S₁.orderEmbOfFin c₁
  let ι₂ := S₂.orderEmbOfFin c₂
  have r₁ : Set.range (b ∘ ι₁) = b '' S₁ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have r₂ : Set.range (b ∘ ι₂) = b '' S₂ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  obtain ⟨W, hW, hWd⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X p₀.1
  have hmem : ∀ i, b i ∈ Z.M.lat p₀ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA, EB, i₁, i₂, MB, e, hpA, hAN, hval⟩ := GlobalTheory.T.lattice_sections_affine_model Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ (N ⊓ W) (Fin g) b ⟨hpN, hW⟩ hmem
  have hd : IsDomain Γ(Y.X, A) := hWd A hpA (hAN.trans inf_le_right)
  have hcl := GlobalTheory.T.affine_domain_generic_specializes Y.X Z.Ω _ A hA p₀ Z.gen hd hpA
  have hcA : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X), y = spMap f ≫ hA.fromSpec → centre y ∈ A := by
    intro f y hy
    have h5 : centre y ∈ Set.range hA.fromSpec := by
      subst hy
      exact ⟨spMap f (IsLocalRing.closedPoint ℂ), (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hA.range_fromSpec] at h5
  refine ⟨A, hA, EB, i₁, i₂, MB, e ∘ ι₁, e ∘ ι₂, b ∘ ι₁, b ∘ ι₂, hpA, fun q hq => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.p b ι₁ ι₁.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₁]; exact e₁)
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.q b ι₂ ι₂.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₂]; exact e₂)
  · intro f y v w hy hs hv hw
    have hyA := hcA f y hy
    have h := hcl _ hyA
    have hq := (hN ⟨centre y, h⟩ (hAN hyA).1).2
    exact ⟨GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z τ σ D.p _ y h v hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.p b ι₁ ι₁.injective hb.1 hq (by rw [r₁]; exact e₁))
        (fun i => hval y f h hy (ι₁ i) (v i) (hv i)),
      GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z _ σ D.q _ y h w hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.q b ι₂ ι₂.injective hb.1 hq (by rw [r₂]; exact e₂))
        (fun j => hval y f h hy (ι₂ j) (w j) (hw j))⟩
  · intro f y v w hy h hv hw
    exact ⟨fun i => hval y f h hy (ι₁ i) (v i) (hv i), fun j => hval y f h hy (ι₂ j) (w j) (hw j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.frame_at_component_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes <;> assumption)
end
end
