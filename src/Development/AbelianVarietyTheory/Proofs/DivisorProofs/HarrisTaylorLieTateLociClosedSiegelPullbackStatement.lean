module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomAtIffOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieOcExistsSpMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorization

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorizationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.closedImmersion_restrict_clopen_factorization : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  first | (exact @GlobalTheory.clopen_cut_closedImmersion) | (exact GlobalTheory.clopen_cut_closedImmersion) | (intros; apply GlobalTheory.clopen_cut_closedImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullback

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this


omit [GrpObj A] [GrpObj A'] in
theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  first | (exact @GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (exact GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (intros; apply GlobalTheory.UPel.HT.exists_preEta_of_siegPull  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_affine_points : ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X), (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) → ∃ z : T ⟶ Z, z ≫ i = g := by
  first | (exact @GlobalTheory.factor_closedImmersion_of_affine_points) | (exact GlobalTheory.factor_closedImmersion_of_affine_points) | (intros; apply GlobalTheory.factor_closedImmersion_of_affine_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullback

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem lieGeom_locus_closed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  intro p _ D R _ b N hN3 hNp h M B _ ζ S s₁ t c e he hK X _ πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hab : IsAbelianScheme AX := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
  obtain ⟨Z₁, i₁, hi₁, hZ₁⟩ := lieHer_closed b (πX ≫ t) AX hab.smooth actX
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback p D R b N h M B ζ S s₁ t c e he hK X πX AX φX φ₂X actX ηX hpb hsq hros heta
  obtain ⟨U, hU, hUx⟩ := PreEta.exists_clopen_geomAt p D R b N hN3 hNp X (πX ≫ t) o
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.closedImmersion_restrict_clopen_factorization i₁ hi₁ U hU
  refine ⟨Z, j, hj, fun T g => ?_⟩
  rw [hZ T g]
  apply and_congr
  · constructor
    · rintro ⟨y, rfl⟩ R' _ β x hx
      exact (hZ₁ R' β (x ≫ y ≫ i₁) (by simpa only [Category.assoc] using hx)).1 ⟨x ≫ y, by simp⟩
    · intro H
      refine GlobalTheory.T.exists_factor_closedImmersion_of_affine_points i₁ hi₁ g fun R' _ x => ?_
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      exact (hZ₁ R' β (x ≫ g) (by simpa only [Category.assoc] using hβ)).2 (H R' β x hβ)
  · constructor
    · intro hg k _ _ x β _
      refine (ho k (x ≫ g)).1 ((hUx k (x ≫ g)).1 ?_)
      rintro _ ⟨u, rfl⟩
      exact hg ⟨x.base u, by simp⟩
    · intro H
      rintro _ ⟨τ, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T τ
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      have hG := (hUx k (x ≫ g)).2 ((ho k (x ≫ g)).2 (H k x β hβ))
      obtain ⟨u, hu⟩ : τ ∈ Set.range x.base := by rw [hx]; rfl
      exact hG ⟨u, by simp [hu]⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  first | (exact @GlobalTheory.UPel.HT.lieGeom_locus_closed) | (exact GlobalTheory.UPel.HT.lieGeom_locus_closed) | (intros; apply GlobalTheory.UPel.HT.lieGeom_locus_closed  <;> assumption)
end
end
