module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZmodTorsorBaseChangeTransportPoint
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfBasicOpenNonemptyOfUniversallyClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_mul_unit_add_eq_zero_of_integral {K A : Type*} [Field K] [CommRing A]
    (φ : K →+* A) (a : A) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (u b : A), IsUnit u ∧ a ^ m * (u + a * b) = 0 := by
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hq0).map φ, ?_⟩
  have hsplit : p.eval₂ φ a = a ^ p.rootMultiplicity 0 * q.eval₂ φ a := by
    conv_lhs => rw [hpq]
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hq' : q.eval₂ φ a = φ (q.coeff 0) + a * q.divX.eval₂ φ a := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      add_comm]
  rw [← hq', ← hsplit, hpa]

theorem isUnit_of_pow_mul_unit_add_eq_zero (X : Scheme.{0}) [ConnectedSpace X]
    (a u b : Γ(X, ⊤)) (m : ℕ) (hu : IsUnit u) (h : a ^ m * (u + a * b) = 0)
    (hne : ((X.basicOpen a : X.Opens) : Set X).Nonempty) : IsUnit a := by
  have hcover : ∀ x : X, x ∈ X.basicOpen a ∨ x ∈ X.basicOpen (u + a * b) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    by_cases hxa : IsUnit (X.presheaf.germ ⊤ x trivial a)
    · exact Or.inl hxa
    · right
      have hU : IsUnit (X.presheaf.germ ⊤ x trivial u) := hu.map _
      have hsum : X.presheaf.germ ⊤ x trivial u =
          X.presheaf.germ ⊤ x trivial (u + a * b) +
            -(X.presheaf.germ ⊤ x trivial a * X.presheaf.germ ⊤ x trivial b) := by
        rw [map_add (f := _), map_mul]; ring
      rw [hsum] at hU
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h1 | h1
      · exact h1
      · exact absurd (isUnit_of_mul_isUnit_left (IsUnit.neg_iff _ |>.1 h1)) hxa
  have hdisj : ∀ x : X, x ∈ X.basicOpen a → x ∈ X.basicOpen (u + a * b) → False := by
    intro x hxa hxg
    rw [Scheme.mem_basicOpen_top] at hxa hxg
    have hx : x ∈ X.basicOpen (a ^ m * (u + a * b)) := by
      rw [Scheme.mem_basicOpen_top, map_mul, map_pow]
      exact (hxa.pow m).mul hxg
    rw [h, Scheme.basicOpen_zero] at hx
    exact hx
  have hall : ∀ x : X, x ∈ X.basicOpen a := by
    intro x
    by_contra hx
    have hxg := (hcover x).resolve_left hx
    obtain ⟨y, -, hy1, hy2⟩ := isPreconnected_univ
      ((X.basicOpen a : X.Opens) : Set X) ((X.basicOpen (u + a * b) : X.Opens) : Set X)
      (X.basicOpen a).isOpen (X.basicOpen (u + a * b)).isOpen
      (fun z _ => hcover z) (by simpa using hne) ⟨x, Set.mem_univ _, hxg⟩
    exact hdisj y hy1 hy2
  exact X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
    (fun x _ => (X.mem_basicOpen_top a x).1 (hall x))

theorem isUnit_of_basicOpen_nonempty_of_universallyClosed :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      [UniversallyClosed f] [ConnectedSpace X] (a : Γ(X, ⊤)),
      ((X.basicOpen a : X.Opens) : Set X).Nonempty → IsUnit a := by
  intro k _ X f _ _ a hne
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  obtain ⟨m, u, b, hu, h⟩ := exists_pow_mul_unit_add_eq_zero_of_integral F.hom a (hF a)
  exact isUnit_of_pow_mul_unit_add_eq_zero X a u b m hu h hne

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionOnConnectedFibreUnit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.FibreFunctionConstant

theorem exists_section_of_germs (Y : Scheme.{0}) (g : ∀ y : Y, Y.presheaf.stalk y)
    (hg : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (t : Γ(Y, W)),
      ∀ z (hz : z ∈ W), Y.presheaf.germ W z hz t = g z) :
    ∃ a : Γ(Y, ⊤), ∀ y, Y.presheaf.germ ⊤ y trivial a = g y := by
  choose W hW t ht using hg
  have compat : TopCat.Presheaf.IsCompatible Y.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i)).trans
      ((ht i y hi).trans ((ht j y hj).symm.trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j)).symm))
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcov t compat
  refine ⟨a, fun q => ?_⟩
  have e := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : W q ≤ ⊤)) q (hW q) a
  have e2 : (Y.presheaf.map (homOfLE (le_top : W q ≤ ⊤)).op).hom a = t q := ha q
  exact e.symm.trans ((congrArg (fun z => (Y.presheaf.germ (W q) q (hW q)).hom z) e2).trans (ht q q (hW q)))

theorem unit_of_cover {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hc : IsCptGen ξ)
    (π : Γ(X, ⊤)) (ϖ : Ω) (h0 : ϖ ≠ 0)
    (hπ : ∀ p : Cpt ξ, genMap ξ p (X.presheaf.germ ⊤ p.1 trivial π) = ϖ)
    (k : Type) [Field k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    [ConnectedSpace Y] (ι : Y ⟶ X) (hι : ι.appTop π = 0) (hr : Set.range ι = zeroSet ξ ϖ)
    (h : Cpt ξ → Ω)
    (H : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      h p ∈ regAt ξ q ∧ (h p - h q) / ϖ ∈ regAt ξ q)
    (hex : ∃ p, ¬ unitAt ξ p ϖ ∧ unitAt ξ p (h p)) : ∀ p, ¬ unitAt ξ p ϖ → unitAt ξ p (h p) := by
  have hy : ∀ y : Y, ι y ∈ zeroSet ξ ϖ := fun y => hr ▸ ⟨y, rfl⟩
  choose hs hn using hy
  have hreg : ∀ y : Y, ∃ c : X.presheaf.stalk (ι y), genMap ξ ⟨ι y, hs y⟩ c = h ⟨ι y, hs y⟩ := fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    exact (HU _ hU (hn y)).1
  choose c hcv using hreg
  have hzero : ∀ y : Y, (ι.stalkMap y).hom (X.presheaf.germ ⊤ (ι y) trivial π) = 0 := fun y => by
    have := Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial π
    rw [this]
    have e : (ι.app ⊤).hom π = 0 := hι
    erw [e]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_section_of_germs Y (fun y => (ι.stalkMap y).hom (c y)) (fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (c y)
    refine ⟨ι ⁻¹ᵁ (W ⊓ U), ⟨hW, hU⟩, ι.app (W ⊓ U) (X.presheaf.map (homOfLE inf_le_left).op t), fun z hz => ?_⟩
    have hz' : ι z ∈ W ⊓ U := hz
    rw [← Scheme.Hom.germ_stalkMap_apply ι (W ⊓ U) z hz']
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) (ι z) hz' t
    erw [e1]
    obtain ⟨d, hd⟩ := (HU ⟨ι z, hs z⟩ hz'.2 (hn z)).2
    have e2 : genMap ξ ⟨ι z, hs z⟩ (X.presheaf.germ W (ι z) hz'.1 t) = h ⟨ι y, hs y⟩ := by
      rw [← hcv y, ← ht]
      exact genMap_germ_eq_genMap_germ ξ W ⟨ι z, hs z⟩ ⟨ι y, hs y⟩ hz'.1 hW t
    have e3 : X.presheaf.germ W (ι z) hz'.1 t = c z + X.presheaf.germ ⊤ (ι z) trivial π * d := by
      apply hc.inj ⟨ι z, hs z⟩
      have e4 := hπ ⟨ι z, hs z⟩
      refine e2.trans ?_
      rw [map_add (f := _), map_mul]
      erw [hcv z, e4, hd]
      field_simp
      ring
    erw [e3]
    rw [map_add (f := _), map_mul, hzero, zero_mul, add_zero])
  have hiff : ∀ y : Y, y ∈ Y.basicOpen a ↔ unitAt ξ ⟨ι y, hs y⟩ (h ⟨ι y, hs y⟩) := fun y => by
    rw [Scheme.mem_basicOpen_top]
    erw [ha y]
    rw [isUnit_map_iff]
    refine Iff.trans ?_ (unitAt_iff_of_isCptGen ξ hc ⟨ι y, hs y⟩ _).symm
    constructor
    · intro hu
      exact ⟨c y, hu, hcv y⟩
    · rintro ⟨u, hu, e⟩
      rwa [← hc.inj ⟨ι y, hs y⟩ (e.trans (hcv y).symm)]
  have lift : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ y : Y, p = ⟨ι y, hs y⟩ := fun p hp => by
    obtain ⟨y, hy⟩ : p.1 ∈ Set.range ι := hr ▸ (coe_mem_zeroSet p).2 hp
    exact ⟨y, Subtype.ext hy.symm⟩
  obtain ⟨p₀, hp₀, hu₀⟩ := hex
  obtain ⟨y₀, rfl⟩ := lift p₀ hp₀
  have hu := isUnit_of_basicOpen_nonempty_of_universallyClosed k Y f a ⟨y₀, (hiff y₀).2 hu₀⟩
  intro p hp
  obtain ⟨y, rfl⟩ := lift p hp
  refine (hiff y).1 ?_
  rw [Y.basicOpen_of_isUnit hu]
  trivial

end PositivityTheory.Xgn.FibreFunctionConstant

open PositivityTheory.Xgn.FibreFunctionConstant in
theorem PositivityTheory.Xgn.function_on_connected_fibre_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hc hconn h H hex
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hUc, -⟩ := cpt_open_integral X Ω ξ hc
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa using hUc)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  haveI : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := O))
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hrr : ∀ x : Spec (CommRingCat.of O), x ∈ Set.range r ↔ ϖ ∈ x.asIdeal := fun x => by
    have e : Set.range r = PrimeSpectrum.zeroLocus (RingHom.ker (IsLocalRing.residue O) : Set O) :=
      range_comap_of_surjective _ _ (IsLocalRing.residue_surjective (R := O))
    rw [e, IsLocalRing.ker_residue, hmax, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff
  let ι : pullback (U.ι ≫ s) r ⟶ X := pullback.fst _ _ ≫ U.ι
  have hr : Set.range ι = zeroSet ξ (algebraMap O Ω ϖ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : genPt ξ ⤳ ι y := (hU _).1 (pullback.fst (U.ι ≫ s) r y).2
      refine ⟨h1, ?_⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr]
      refine ⟨pullback.snd (U.ι ≫ s) r y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      simp [ι]
    · rintro ⟨h1, h2⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr] at h2
      have h3 : (⟨x, (hU x).2 h1⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ s) r) := by
        rw [Scheme.Pullback.range_fst]
        exact h2
      obtain ⟨y, hy⟩ := h3
      refine ⟨y, ?_⟩
      simp [ι, hy]
  haveI : ConnectedSpace (pullback (U.ι ≫ s) r : Scheme.{0}) := by
    rw [← hr, ← Set.image_univ] at hconn
    rw [connectedSpace_iff_univ]
    exact ⟨hconn.1.of_image, ι.isEmbedding.isInducing.isPreconnected_image.1 hconn.2⟩
  refine unit_of_cover ξ hc (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) _
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (fun p => ConstReg.genMap_germ_const ξ s hs p ϖ)
    (IsLocalRing.ResidueField O) _ (pullback.snd (U.ι ≫ s) r) ι ?_ hr h H hex
  have e : ι ≫ s = pullback.snd (U.ι ≫ s) r ≫ r := by
    rw [← pullback.condition]; simp [ι]
  have e1 : r.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    have h3 := congrArg (fun q => q.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
    have h3' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField O))).inv.hom (IsLocalRing.residue O ϖ) =
      r.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := h3
    rw [← h3', (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ), map_zero]
  have e2 : (ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e1, map_zero]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  exact e2
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem unitAt_of_localLifts_of_unitAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) :=
  @PositivityTheory.Xgn.function_on_connected_fibre_unit

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstantStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.connected_special_fibre_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PropZPf

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_sub_mem {L : Lat ξ Ω} {q : Cpt ξ} {w σ tp tq y : Ω} (a : ℤ) (M : ℕ) (hw0 : w ≠ 0)
    (hwq : w ∈ regAt ξ q) (hσ : σ ≠ 0) (hgq : L.IsGenAt q tq) (htp : tp ≠ 0)
    (hhq : w ^ a / (σ / tq) ^ M ∈ regAt ξ q) (hy : y ∈ L q) (hd : tp - tq = w • y) :
    (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w ∈ regAt ξ q := by
  rw [hgq.2, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hr : ((r • tq : Ω)) = (r : Ω) * tq := rfl
  rw [hr, smul_eq_mul] at hd
  have htq := hgq.1
  have e1 : tp = tq * (1 + w * r) := by linear_combination hd
  have hu : (1 + w * (r : Ω)) ≠ 0 := by
    intro h0; apply htp; rw [e1, h0, mul_zero]
  have e2 : w ^ a / (σ / tp) ^ M = w ^ a / (σ / tq) ^ M * (1 + w * r) ^ M := by
    rw [e1, div_pow, div_pow, mul_pow]
    field_simp
  have g := geom_sum_mul (1 + w * (r : Ω)) M
  have e3 : (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w =
      w ^ a / (σ / tq) ^ M * (r : Ω) * ∑ i ∈ Finset.range M, (1 + w * (r : Ω)) ^ i := by
    rw [e2, div_eq_iff hw0]
    linear_combination (-(w ^ a / (σ / tq) ^ M)) * g
  rw [e3]
  refine mul_mem (mul_mem hhq r.2) (Subring.sum_mem _ fun i _ => pow_mem ?_ i)
  exact add_mem (one_mem _) (mul_mem hwq r.2)

end GlobalTheory.CompanionTheory.Ar.Flat.PropZPf


open GlobalTheory.CompanionTheory.Ar.Flat.PropZPf in
theorem GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb htriv hgen
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, hord₀⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.nonempty L σ hvb hgen
  have hw0 : algebraMap O Ω ϖ ≠ 0 := fun e => hϖ.ne_zero (hinj (by rw [map_zero]; exact e))
  have hwreg : ∀ p : Cpt ξ, algebraMap O Ω ϖ ∈ regAt ξ p := fun p =>
    (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p ϖ).1
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  have hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ := by
    intro q hq o ho
    rw [hunit]
    intro hmem
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    have hP : (s q.1).asIdeal.IsPrime := (s q.1).isPrime
    rw [hu] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1
        rwa [Units.inv_mul] at this))
    · exact (hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)
  have hσ : σ ≠ 0 := hord₀.ne_zero hM.ne'
  obtain ⟨t, ht⟩ := htriv
  have htq : ∀ q : Cpt ξ, ¬ unitAt ξ q (algebraMap O Ω ϖ) → L.IsGenAt q (t q) := fun q hq => by
    obtain ⟨U, hU, H⟩ := ht q hq
    obtain ⟨h0, h1, -⟩ := H q hU hq
    exact ⟨h0, h1⟩
  have hloc : ∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) →
        (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p ∈ regAt ξ q ∧
        ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p -
          (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) q) / algebraMap O Ω ϖ ∈ regAt ξ q := by
    intro p hp
    obtain ⟨U, hU, H⟩ := ht p hp
    refine ⟨U, hU, fun q hqU hq => ?_⟩
    obtain ⟨h0, h1, y, hy, hd⟩ := H q hqU hq
    exact ⟨hreg q (t p) ⟨h0, h1⟩, div_sub_mem a M hw0 (hwreg q) hσ (htq q hq) h0
      (hreg q (t q) (htq q hq)) hy hd⟩
  have hu₀ : unitAt ξ p₀ ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p₀) := by
    have := ZUnit.inv ((orderAt_iff_div (htq p₀ hp₀).1 (htq p₀ hp₀).2).1 hord₀)
    rwa [inv_div] at this
  have key := GlobalTheory.T.connected_special_fibre_constant X Ω ξ O s ϖ hϖ hinj hs hg hconn
    (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) hloc ⟨p₀, hp₀, hu₀⟩
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hp : unitAt ξ p (algebraMap O Ω ϖ)
  · have hgp := hgen p (hgf p hp)
    rw [orderAt_iff_div hgp.1 hgp.2, div_self hσ, one_pow, one_div]
    refine ZUnit.inv ⟨zpow_ne_zero a hw0, ZLat.zpow_mem_regAt hp a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hp (-a)
  · rw [orderAt_iff_div (htq p hp).1 (htq p hp).2]
    have h1 : unitAt ξ p (algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) := key p hp
    have := ZUnit.inv h1
    rwa [inv_div] at this
end
end
