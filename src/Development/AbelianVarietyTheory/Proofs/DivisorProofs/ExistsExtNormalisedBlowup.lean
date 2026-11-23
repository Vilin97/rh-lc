module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCoverStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeet

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_extension_generic_point_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  first | exact @GlobalTheory.TorDown.ext_of_fraction_meet | exact GlobalTheory.TorDown.ext_of_fraction_meet | (intros; apply GlobalTheory.TorDown.ext_of_fraction_meet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphism

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_fieldPoint : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  intro U X c _ _ K _ y
  set P := pullback y c
  haveI : IsAffine P := inferInstance
  let f : P ⟶ Sp K := pullback.fst y c
  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (P.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = P.isoSpec.inv ≫ f := Spec.map_preimage _
  haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance

  obtain ⟨p, -⟩ := (pullback.fst y c).surjective (IsLocalRing.closedPoint K)
  haveI : Nontrivial A := by
    have q : PrimeSpectrum A := P.isoSpec.hom.base p
    exact q.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A : Type)
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Module.Finite K A := hfin
  haveI : Module.Finite K (A ⧸ m) := Module.Finite.trans A (A ⧸ m)
  refine ⟨A ⧸ m, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ P.isoSpec.inv ≫ pullback.snd y c, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphismStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  first | exact @GlobalTheory.FinLift.lift_fieldPoint | exact GlobalTheory.FinLift.lift_fieldPoint | (intros; apply GlobalTheory.FinLift.lift_fieldPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtOfMinAt5

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MinExt

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G k ψ) (e : g ≫ f = k) :
    ∃ φ', IsGrpPullback G'' G' g φ' := by
  subst e
  have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [n.1.w, Category.assoc]
  exact ⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩

theorem exists_ext_of_minAt5 : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left), IsGenFibre F y α₁ → ∀ b : cycAway n →+* R, y ≫ F.s = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ i := by
  intro g n F Z z i OZ h R _ _ _ _ _ _ G₁ _ _ hG₁ y α₁ hα₁ b hyb
  obtain ⟨o', _, β, S', s', U, c, π, G, _, e, _, N, ⟨-, hz, -, hiz, -, hOZ, hamp⟩,
    ⟨-, -, -, -, -, hcfin, hcsurj, hUπ, -, -, hπp, -⟩, ⟨hGsa, hGsm, he⟩, ⟨-, hL⟩⟩ := h
  haveI := hcfin
  haveI := hcsurj
  haveI := hπp
  haveI : IsProper z := by
    obtain ⟨m, j, hj, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  obtain ⟨K', _, _, _, y', hy'⟩ := GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism U.toScheme F.X c (FractionRing R) y
  obtain ⟨R', _, _, _, _, _, ρ, eR, -, hinj, hcomp, hmeet⟩ := GlobalTheory.T.exists_local_normal_domain_finite_extension R K'
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  let gam : FractionRing R →+* FractionRing R' := (eR.symm : K' →+* FractionRing R').comp (algebraMap (FractionRing R) K')
  have E1 : spMap gam = spMap (eR.symm : K' →+* FractionRing R') ≫ spMap (algebraMap (FractionRing R) K') :=
    spMap_comp_eq _ _
  have E2 : spMap gam ≫ jK R = jK R' ≫ spMap ρ := by
    change spMap gam ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
    rw [← spMap_comp_eq, ← spMap_comp_eq]
    congr 1
    ext r
    simp only [RingHom.comp_apply, gam]
    rw [← hcomp r]
    simp
  let yy : Sp (FractionRing R') ⟶ S' := spMap (eR.symm : K' →+* FractionRing R') ≫ y' ≫ U.ι
  have E4 : spMap gam ≫ y = (spMap (eR.symm : K' →+* FractionRing R') ≫ y') ≫ c := by
    rw [Category.assoc, hy', E1, Category.assoc]
  have E3 : yy ≫ π = spMap gam ≫ y ≫ i := by
    simp only [yy, Category.assoc]
    rw [hUπ, ← Category.assoc y' c i, hy', E1]
    simp only [Category.assoc]
  let G₁' := (Over.pullback (spMap ρ)).obj G₁
  have hG₁' : IsSemiAbelian G₁' := IsSemiAbelian.pullback (spMap ρ) G₁ hG₁
  haveI : IsCommMonObj G₁' := hG₁'.comm
  have h1 := ((isGrpPullback_pullback G₁' (jK R')).comp (isGrpPullback_pullback G₁ (spMap ρ))).congr E2.symm rfl
  obtain ⟨φ1, hφ1⟩ := exists_factor (isGrpPullback_pullback G₁ (jK R)) h1 rfl
  have h2 := (hφ1.comp hα₁).congr E4 rfl
  obtain ⟨φ2, hφ2⟩ := exists_factor (isGrpPullback_pullback F.univ.A c) h2 rfl
  have h3 := (hφ2.comp he).congr (Category.assoc _ _ _) rfl
  have hyz : yy ≫ π ≫ z = jK R' ≫ spMap (ρ.comp b) := by
    rw [← Category.assoc, E3, Category.assoc, Category.assoc, hiz, hyb, ← Category.assoc, E2, spMap_comp_eq,
      Category.assoc]
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_minimalCompactification_extension_of_cover (cycAway n) g Z S' z π OZ hOZ hamp G N hGsa hGsm hL R' (ρ.comp b) G₁' hG₁' yy _ h3 hyz
  have hmeet' : ∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x :=
    fun x w hw => hmeet x w (by rw [hw]; simp [gam])
  exact GlobalTheory.T.exists_extension_generic_point_fraction_meet Z R R' gam hmeet' (y ≫ i) a' (ha'.trans E3)

end GlobalTheory.MinExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem Taut.exists_ext_normBl : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  intro g _ φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ y α₁ hC
  obtain ⟨hsa, hab, hgen, hmum, hy⟩ := hC
  obtain ⟨J, -, -, hval, hbl, -, -, hji, hpre, -, -⟩ := hB
  obtain ⟨hreg, hchar, -, -, hpar, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  haveI : IsOpenImmersion i := hM.isThetaCompact.1.2.2.1
  haveI : IsCommMonObj G₁ := hsa.comm
  haveI : IsNoetherianRing C.R := C.compl.1
  haveI : IsIntegrallyClosed C.R := hmum.1.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.MinExt.exists_ext_of_minAt5 g n F Z z i OZ hM C.R G₁ hsa y α₁ hgen C.b hy
  have hon : IsPolFanOn id φ C.Q.X := hφ C.Q.X hrk
  have he : ∀ k, ∃ e : ℕ, (e : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := by
    intro k
    have hmem : (n : ℤ) • C.δ k ∈ balForms (id : ℤ → ℤ) C.Q.X := Submodule.smul_mem _ _ (hcone.mem k)
    have hnn : ∀ w, 0 ≤ ((n : ℤ) • C.δ k) w w := fun w => by
      simpa using mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
    obtain ⟨c, hc⟩ := hon.integral _ hmem hnn
    have hc0 : 0 ≤ c := by
      have hne : (n : ℤ) • C.δ k ≠ 0 := by
        refine fun h => hcone.basis.linearIndependent.ne_zero k (Subtype.ext ?_)
        exact (smul_eq_zero.1 h).resolve_left (by omega)
      have := hon.pos _ hmem hnn hne
      rw [hc] at this
      exact_mod_cast this.le
    lift c to ℕ using hc0
    exact ⟨d * c, by rw [hc]; push_cast; rfl⟩
  choose e he using he
  have hJ := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F Z i φ hφ d J hval C.R C.compl.2.1 C.b a C.Q G₁ y α₁ hsa hgen ha
    hmum C.m C.t C.δ e hpar hab hcone hdef hmono he
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.NormBlLift.lift_normBl g n F Z S i π j J hbl hji hpre C.R a y ha _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hJ
  refine ⟨ξ, ?_⟩
  have hπ : (jK C.R ≫ ξ) ≫ π = y ≫ i := by rw [Category.assoc, hξ, ha]
  have hr : Set.range (jK C.R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [← hpre]
    exact ⟨y p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]⟩
  have hl := IsOpenImmersion.lift_fac j (jK C.R ≫ ξ) hr
  have : IsOpenImmersion.lift j (jK C.R ≫ ξ) hr = y := by
    rw [← cancel_mono i, ← hπ, ← hji, ← Category.assoc, hl]
  rw [← this, hl]

end GlobalTheory.TChart
end
end
