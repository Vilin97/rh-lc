module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValuesStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.TorsionList

theorem pow_exp (n k : ℕ) (c : Multiplicative (Fin k → ZMod n)) : c ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem pushHom_bij {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩
  · exact (Over.w x).trans (Over.w y).symm
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem spMap_comp_assoc {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] {X : Scheme.{0}}
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (y : Sp A ⟶ X) :
    spMap (h.comp g) ≫ spMap f ≫ y = spMap h ≫ spMap (g.comp f) ≫ y := by
  simp only [spMap_comp, Category.assoc]

abbrev lft {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (p : Over.mk a ⟶ G) : X ⟶ G.left := p.left

theorem pow_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (y : Over.mk b ⟶ G) (hx : lft x = lft y) (n : ℕ) : lft (x ^ n) = lft (y ^ n) := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem one_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    lft (1 : Over.mk a ⟶ G) = lft (1 : Over.mk b ⟶ G) := by
  subst h
  rfl

theorem transport {S X : Scheme.{0}} {G : Over S} {a b : X ⟶ S} (h : a = b) (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk a ⟶ G, lft p' = lft p := by
  subst h
  exact ⟨p, rfl⟩

theorem lft_pushHom {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {X : Scheme.{0}} (t : X ⟶ S') (y : Over.mk t ⟶ A') :
    lft (pushHom h (Over.mk t) y) = y.left ≫ φ := rfl

theorem toUnit_mk_left {X Y : Scheme.{0}} (f : Y ⟶ X) : (toUnit (Over.mk f)).left = f :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))

theorem toUnit_left {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_cover_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  intro S G _ _ L g m N R _ _ x hm hmu hN hP
  obtain ⟨P, α, hg, hp, -⟩ := hP
  haveI := P.isAb.comm
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  have hu : IsUnit (((m ^ 2 : ℕ)) : R) := by rw [Nat.cast_pow]; exact hmu.pow 2
  obtain ⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩ :=
    GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu
  let b := spMap (algebraMap R R₁)
  let A₁ := (Over.pullback b).obj P.A
  haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj
  have h₁ := isGrpPullback_pullback P.A b
  obtain ⟨ψ, hψ⟩ := H A₁ _ h₁
  have hc := h₁.comp hp
  have hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N := by
    rw [hN]
    simp [Fintype.card_fun, ZMod.card, ← pow_mul]
    ring_nf
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x) := Over.homMk (𝟙 _) (by simp)
  let Q := (preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)
  have hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α := fun c => by
    simp [Q, U, pushHom, pushPt, preHom]
  refine ⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by
    rw [← map_pow, pow_exp, map_one], ?_⟩
  intro K _ i₁ pt hpt
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d,
      t ≫ (Q c).left = t ≫ (Q d).left → c = d := by
    intro k _ _ t c d h
    have hinj : Function.Injective ((preHom (G := A₁) (toUnit (Over.mk t))).comp ψ) := by
      rw [injective_iff_map_eq_one]
      exact fun c hc => (hψ k t).2 c hc
    apply hinj
    apply Over.OverMorphism.ext
    show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left
    rw [Over.comp_left, Over.comp_left, toUnit_left]
    apply hc.1.hom_ext
    · rw [hQ, hQ] at h
      simpa [Category.assoc] using h
    · have e1 := Over.w (ψ c)
      have e2 := Over.w (ψ d)
      simp only [Category.assoc]
      erw [e1, e2]
  refine ⟨fun a a' h => ?_, ?_⟩
  · have h' := congrArg (fun z => z.left) h
    simp only [hpt] at h'
    let k := AlgebraicClosure K
    have := key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by
      rw [spMap_comp, Category.assoc, Category.assoc]; exact congrArg (spMap (algebraMap K k) ≫ ·) h')
    exact e.injective this
  · intro K' _ _ i' p hp2
    have ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x :=
      (spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm
    obtain ⟨p', hp'⟩ := transport ht.symm p
    obtain ⟨p₁, hp₁⟩ := (pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'
    have hk : p₁ ^ (m ^ 2) = 1 := by
      apply (pushHom_bij hc _).1
      rw [map_pow, hp₁, map_one]
      apply Over.OverMorphism.ext
      change lft _ = lft _
      rw [pow_lft_congr ht.symm p' p hp', hp2]
      exact one_lft_congr ht
    obtain ⟨c, rfl⟩ := ((hψ K' _).1 p₁).1 hk
    refine ⟨e.symm c, ?_⟩
    rw [hpt]
    simp only [Equiv.apply_symm_apply]
    change lft p = _
    have h2 := congrArg lft hp₁
    rw [← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]
    simp only [Category.assoc]

end GlobalTheory.UMin.TorsionList
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  first | exact @GlobalTheory.UMin.TorsionList.exists_cover_torsion_list | exact GlobalTheory.UMin.TorsionList.exists_cover_torsion_list | (intros; apply GlobalTheory.UMin.TorsionList.exists_cover_torsion_list <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  first | exact @GlobalTheory.UMin.thG_unique_of_polFib | exact GlobalTheory.UMin.thG_unique_of_polFib | (intros; apply GlobalTheory.UMin.thG_unique_of_polFib <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thList_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  intro S G _ _ L ρ hL hρ g m N R _ _ x θ hm hu hN hP
  obtain ⟨R₁, _, _, q, hfin, hff, hq, hpts⟩ := GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections S G L g m N R x hm hu hN hP
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  have hcomp : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K),
      spMap i₁ ≫ spMap (algebraMap R R₁) = spMap (i₁.comp (algebraMap R R₁)) := by
    intro K _ i₁; simp [spMap]
  let pt₀ : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K) (a : Fin N), Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G :=
    fun i₁ a => Over.homMk (spMap i₁ ≫ (q a).left) (by
      have h := Over.w (q a)
      simp only [Over.mk_hom] at h ⊢
      rw [Category.assoc, h, ← Category.assoc, hcomp])
  have key : ∀ a : Fin N, ∃ c : R₁, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K)
      (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn (i₁ c)) := by
    intro a
    refine GlobalTheory.T.exists_ring_element_of_local_field_point_values R₁ (fun K _ i₁ v => ∀ (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G),
        pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn v)) ?_ ?_
    · intro K _ i₁ u v hu' hv'
      exact GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre S G L ρ hL hρ g m R x K (i₁.comp (algebraMap R R₁)) hm hu hP _ (pt₀ i₁ a) u v
        (hu' _ rfl) (hv' _ rfl)
    · intro p hp
      obtain ⟨f, hf, c, hc⟩ := GlobalTheory.T.exists_local_thetaConstants_localisation S G L ρ hL hρ g m R x θ R₁ N q hm hu hP hq p hp
      exact ⟨f, hf, c a, fun K _ j pt hpt => hc K j a pt hpt⟩
  choose c hc using key
  refine ⟨R₁, inferInstance, inferInstance, c, hfin, hff, fun K _ i i₁ hi => ?_⟩
  subst hi
  obtain ⟨hinj, hcov⟩ := hpts K i₁ (pt₀ i₁) (fun a => rfl)
  exact ⟨pt₀ i₁, hinj, fun a => hc a K i₁ _ rfl, hcov⟩

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_constants_functions_finite_flat_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  first | exact @GlobalTheory.UMin.thList_cover | exact GlobalTheory.UMin.thList_cover | (intros; apply GlobalTheory.UMin.thList_cover <;> assumption)
end
end
