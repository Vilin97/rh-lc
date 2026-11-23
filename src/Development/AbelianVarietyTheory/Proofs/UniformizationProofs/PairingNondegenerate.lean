module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAbelianPartDimAddTorusRank
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfCubWeilOrthogonal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusQuotientCardTorsion

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
namespace TorsionCount

theorem card_torsion_eq_mul {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B) (N : ℕ)
    (h : ∀ b : B, b ^ N = 1 → ∃ a : A, a ^ N = 1 ∧ f a = b) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {a : A // a ^ N = 1 ∧ f a = 1} * Nat.card {b : B // b ^ N = 1} := by
  choose s hs hs' using h
  rw [← Nat.card_prod]
  have hf : ∀ a : A, a ^ N = 1 → f a ^ N = 1 := fun a ha => by rw [← map_pow, ha, map_one]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : {a : A // a ^ N = 1 ∧ f a = 1} × {b : B // b ^ N = 1} =>
      (⟨x.1.1 * s x.2.1 x.2.2, by rw [mul_pow, x.1.2.1, hs, _root_.one_mul]⟩ : {a : A // a ^ N = 1})) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨a, ha⟩, b, hb⟩ ⟨⟨a', ha'⟩, b', hb'⟩ e
    have e₁ : a * s b hb = a' * s b' hb' := congrArg Subtype.val e
    have e₂ := congrArg f e₁
    rw [map_mul, map_mul, hs', hs', ha.2, ha'.2, _root_.one_mul, _root_.one_mul] at e₂
    subst e₂
    have e₃ := mul_right_cancel e₁
    subst e₃
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨(⟨a * (s (f a) (hf a ha))⁻¹, ?_, ?_⟩, ⟨f a, hf a ha⟩), Subtype.ext (inv_mul_cancel_right _ _)⟩
    · rw [mul_pow, inv_pow, ha, hs, inv_one, _root_.one_mul]
    · rw [map_mul, map_inv, hs', mul_inv_cancel]

theorem card_hom_torsion {X U : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] (N : ℕ) :
    Nat.card {φ : Multiplicative X →* U // φ ^ N = 1} = Nat.card {u : U // u ^ N = 1} ^ Module.finrank ℤ X := by
  let e := Module.finBasis ℤ X
  have key : Function.Bijective (fun (φ : {φ : Multiplicative X →* U // φ ^ N = 1}) (k : Fin (Module.finrank ℤ X)) =>
      (⟨φ.1 (Multiplicative.ofAdd (e k)), DFunLike.congr_fun φ.2 _⟩ : {u : U // u ^ N = 1})) := by
    have ext : ∀ φ ψ : Multiplicative X →* U,
        (∀ k, φ (Multiplicative.ofAdd (e k)) = ψ (Multiplicative.ofAdd (e k))) → φ = ψ := fun φ ψ h => by
      have : (MonoidHom.toAdditiveRight φ).toIntLinearMap = (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
        e.ext fun k => congrArg Additive.ofMul (h k)
      exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun this (Multiplicative.toAdd χ))
    constructor
    · intro φ ψ h
      exact Subtype.ext (ext _ _ fun k => congrArg Subtype.val (congrFun h k))
    · intro v
      let l : X →ₗ[ℤ] Additive U := e.constr ℤ fun k => Additive.ofMul (v k).1
      have hl : ∀ k, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom (Multiplicative.ofAdd (e k)) = (v k).1 :=
        fun k => congrArg Additive.toMul (e.constr_basis ℤ _ k)
      refine ⟨⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, ext _ _ fun k => ?_⟩,
        funext fun k => Subtype.ext (hl k)⟩
      rw [MonoidHom.pow_apply, hl, (v k).2, MonoidHom.one_apply]
  rw [Nat.card_congr (Equiv.ofBijective _ key), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_units_torsion (K : Type) [Field K] [IsAlgClosed K] {N : ℕ} (hN : (N : K) ≠ 0) :
    Nat.card {u : Kˣ // u ^ N = 1} = N := by
  have : NeZero (N : K) := ⟨hN⟩
  have : NeZero N := NeZero.of_neZero_natCast K
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K N

theorem card_torsion_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (N : ℕ) :
    Nat.card {a : A // a ^ N = 1} = Nat.card {b : B // b ^ N = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by
    rw [← e.map_eq_one_iff, map_pow]; rfl)

end TorsionCount


open TorsionCount in
theorem torusQuotient_card_torsion :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ S) (N : ℕ),
      (N : K) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X ∧
        Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} =
          N ^ Module.finrank ℤ X * Nat.card {b : Over.mk p ⟶ Q.B // b ^ N = 1} := by
  intro S X _ _ _ G _ _ Q K _ _ p N hN
  have := Q.q_hom
  have := Q.i_hom
  have hN' : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN Nat.cast_zero)
  let e : Kˣ ≃* Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have inj : ∀ t t' : Over.mk p ⟶ splitTorus S X, t ≫ Q.i = t' ≫ Q.i → t = t' := fun t t' h =>
    Q.isKernel.hom_ext h (toUnit_unique _ _)
  have h₃ : ∀ t : Over.mk p ⟶ splitTorus S X, (t ≫ Q.i) ≫ Q.q = 1 := fun t => by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have key : Function.Bijective (fun t : {t : Over.mk p ⟶ splitTorus S X // t ^ N = 1} =>
      (⟨t.1 ≫ Q.i, by rw [← MonObj.pow_comp, t.2, MonObj.one_comp], h₃ _⟩ :
        {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1})) := by
    refine ⟨fun t t' h => Subtype.ext (inj _ _ (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, hx, hq⟩
    have h₁ : x ≫ Q.q = toUnit _ ≫ η[Q.B] := hq.trans Hom.one_def
    refine ⟨⟨Q.isKernel.lift _ _ h₁, inj _ _ ?_⟩, Subtype.ext (Q.isKernel.lift_fst _ _ _)⟩
    rw [MonObj.pow_comp, IsPullback.lift_fst, hx, MonObj.one_comp]
  have c₁ : Nat.card {x : Over.mk p ⟶ G // x ^ N = 1 ∧ x ≫ Q.q = 1} = N ^ Module.finrank ℤ X := by
    rw [← Nat.card_congr (Equiv.ofBijective _ key), card_torsion_congr (splitTorusPointsEquiv S X (Over.mk p)) N,
      card_hom_torsion]
    exact congrArg (· ^ _) ((card_torsion_congr e N).symm.trans (card_units_torsion K hN))
  refine ⟨c₁, ?_⟩
  rw [← c₁]
  refine card_torsion_eq_mul (MonoidHom.mk' (fun x : Over.mk p ⟶ G => x ≫ Q.q) fun x y => MonObj.mul_comp _ _ _) N
    ((torusQuotient_points_lift S X G Q K p).2 N fun a => ?_)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hN'
  have h0 : r ≠ 0 := by
    rintro rfl
    exact a.ne_zero (hr.symm.trans (zero_pow hN'.ne'))
  exact ⟨Units.mk0 r h0, Units.ext (by simpa using hr)⟩

end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PairingNondegenerate

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.SpecialPairing

theorem card_map {A₀ A A' : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] (r : A →* A₀) (j : A →* A') (N : ℕ)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (K : Subgroup A₀) :
    Nat.card (((powMonoidHom N).ker ⊓ K.comap r).map j) = Nat.card {x : A₀ // x ^ N = 1 ∧ x ∈ K} := by
  rw [Subgroup.card_map_of_injective hj]
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨r y.1, by rw [← map_pow, show y.1 ^ N = 1 from y.2.1, map_one],
    y.2.2⟩) ⟨fun y y' h => Subtype.ext (ri _ _ y.2.1 y'.2.1 (congrArg Subtype.val h)), fun x => ?_⟩)
  obtain ⟨y, hy, e⟩ := rs x.1 x.2.1
  exact ⟨⟨y, hy, show r y ∈ K from e ▸ x.2.2⟩, Subtype.ext e⟩

theorem core {A₀ A A' B : Type} [CommGroup A₀] [CommGroup A] [CommGroup A'] [CommGroup B] (r : A →* A₀)
    (j : A →* A') (q : A₀ →* B) (N M : ℕ) (P' : A' → A' → Prop) (P : B → B → Prop)
    (ri : ∀ y y', y ^ N = 1 → y' ^ N = 1 → r y = r y' → y = y') (rs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ r y = x)
    (hj : Function.Injective j) (qs : ∀ b, b ^ N = 1 → ∃ x, x ^ N = 1 ∧ q x = b)
    (hP : ∀ y y', y ^ N = 1 → y' ^ N = 1 → P (q (r y)) (q (r y')) → P' (j y) (j y'))
    (h1 : ∀ b, b ^ N = 1 → P 1 b)
    (hc : Nat.card {x : A₀ // x ^ N = 1 ∧ q x = 1} * Nat.card {x : A₀ // x ^ N = 1} = M)
    (rad : ∀ T H : Subgroup A', (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = M →
      (∀ x ∈ T, ∀ y ∈ H, P' x y) → ∀ x, x ^ N = 1 → (∀ y ∈ H, P' x y) → x ∈ T)
    (b : B) (hb : b ^ N = 1) (h : ∀ b', b' ^ N = 1 → P b b') : b = 1 := by
  have tq : ∀ y : A, y ^ N = 1 → q (r y) ^ N = 1 := fun y hy => by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  have tj : ∀ y : A, y ^ N = 1 → j y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, rfl⟩ := qs b hb
  obtain ⟨y, hy, rfl⟩ := rs x hx
  obtain ⟨y', hy', e⟩ := rad (((powMonoidHom N).ker ⊓ q.ker.comap r).map j)
    (((powMonoidHom N).ker ⊓ (⊤ : Subgroup A₀).comap r).map j)
    (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1) (by rintro _ ⟨z, hz, rfl⟩; exact tj z hz.1)
    (by
      rw [card_map r j N ri rs hj, card_map r j N ri rs hj, ← hc]
      simp only [Subgroup.mem_top, and_true, MonoidHom.mem_ker])
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      refine hP z z' hz.1 hz'.1 ?_
      rw [show q (r z) = 1 from hz.2]
      exact h1 _ (tq _ hz'.1))
    (j y) (tj y hy) (by
      rintro _ ⟨z', hz', rfl⟩
      exact hP y z' hy hz'.1 (h _ (tq _ hz'.1)))
  obtain rfl := hj e
  exact hy'.2

theorem exists_embedding (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Algebra V W]
    [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure (FractionRing V), Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure (FractionRing V))) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V)]
    exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure (FractionRing V)) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure (FractionRing V) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker φ.toRingHom) = ⊥
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem torsion_ext (W : Type) [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W)) {Ω : Type} [Field Ω] (f : W →+* Ω) [IsLocalHom f] (y y' : Over.mk p ⟶ G) (hy : y ^ N = 1)
    (hy' : y' ^ N = 1) (e : Spec.map (CommRingCat.ofHom f) ≫ y.left = Spec.map (CommRingCat.ofHom f) ≫ y'.left) :
    y = y' := by
  have := GlobalTheory.TorsionSeparable.epi_specMap (IsLocalRing.ResidueField.lift f)
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Category.assoc, cancel_epi] at e
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W))) rfl
  exact (GlobalTheory.existsUnique_torsion_lift W S G p N hN (ρ ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])).unique ⟨hy, rfl⟩ ⟨hy', e.symm⟩

theorem toBase_bijective {S S' : Scheme.{0}} (G : Over S) (f : S' ⟶ S) (T : Over S') :
    Function.Bijective (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f)
      pullback.condition (T := T)) :=
  ⟨fun x y h => Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun z => z.left) h)
    ((Over.w x).trans (Over.w y).symm)), fun x =>
    ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩⟩



theorem pairing_nondegenerate : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ x : Over.mk p ⟶ (t.l 0).Q.B, x ^ N = 1 → (∀ y : Over.mk p ⟶ (t.l 0).Q.B, y ^ N = 1 → CubWeil (t.l 0).D.M.c N x y 1) → x = 1 := by
  intro hAb hL V _ _ _ A G _ _ s t Ω _ _ p N hN
  obtain ⟨dvr, cpl, -⟩ := s.cdvr
  have := s.semi.smooth
  have := s.semi.separated
  have := (t.l 0).Q.q_hom
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* Ω, p = Spec.map (CommRingCat.ofHom φ₀) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  let f : V →+* Ω := φ₀.comp (Ideal.Quotient.mk _)
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact h)
    exact ha.ne_zero (by rw [RingHom.comp_apply, this, map_zero])⟩
  have hNΩ : (N : Ω) ≠ 0 := by simpa using (hN.map f).ne_zero
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNΩ
  obtain ⟨g', hg'⟩ : ∃ g', SmoothOfRelativeDimension g' (t.l 0).Q.B.hom := by
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := φ₀.domain_nontrivial
    have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact GlobalTheory.AbelianDim.exists_relDim _ _ (t.l 0).Q.isAb
  have hd := (GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').1 hg'
  obtain ⟨c₁, c₂⟩ := torusQuotient_card_torsion _ _ _ (t.l 0).Q Ω (Spec.map (CommRingCat.ofHom φ₀)) N hNΩ
  rw [GlobalTheory.card_torsion_geometricPoint_of_field hAb _ _ (t.l 0).Q.isAb g' hg' Ω _ N hNΩ] at c₂
  let T₀ : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) :=
    Over.mk (Spec.map (CommRingCat.ofHom φ₀))
  have hpf : Spec.map (CommRingCat.ofHom f) = T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  let β : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) ≃*
      (Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ G) :=
    MulEquiv.ofBijective (toBaseHom (toBase_mul_pullback G _) T₀) (toBase_bijective G _ T₀)
  have hβ : ∀ x, (β x).left = x.left ≫ (fstG _ 0 G).left := fun _ => rfl
  let ι₀ : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hpf.symm)
  have fin : Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  have fin' := (show Set.Finite {x : T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G | x ^ N = 1} from fin).image
    (fun x => ι₀ ≫ β x)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V G N
    hN Ω f hf fin'.toFinset (by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := fin'.mem_toFinset.1 hx
      show (ι₀ ≫ β u) ^ N = 1
      rw [← MonObj.comp_pow, ← map_pow, show u ^ N = 1 from hu, map_one, MonObj.comp_one])
  obtain ⟨φ, φi, hφ⟩ := exists_embedding V W inj
  let TW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let ρ : Over.mk (T₀.hom ≫ thick V (IsLocalRing.maximalIdeal V) 0) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) (by
      refine Eq.trans ?_ hpf
      rw [← hf', CommRingCat.ofHom_comp, Spec.map_comp]; rfl)
  let σ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ TW :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      have e := congrArg (fun z => Spec.map (CommRingCat.ofHom z)) hφ
      simp only [CommRingCat.ofHom_comp, Spec.map_comp] at e
      exact e)
  let r : (TW ⟶ G) →* (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) := β.symm.toMonoidHom.comp (preHom ρ)
  have hr : ∀ y, (r y).left ≫ (fstG _ 0 G).left = Spec.map (CommRingCat.ofHom f') ≫ y.left := fun y =>
    (hβ _).symm.trans (congrArg (fun z => z.left) (β.apply_symm_apply (ρ ≫ y)))
  let q : (T₀ ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G) →* (T₀ ⟶ (t.l 0).Q.B) :=
    MonoidHom.mk' (· ≫ (t.l 0).Q.q) fun x y => MonObj.mul_comp x y _
  refine core r (preHom σ) q N (N ^ (2 * A.g)) (fun x y => CubWeil s.P.c N x y 1)
    (fun x y => CubWeil (t.l 0).D.M.c N x y 1) (fun y y' hy hy' e => ?_) (fun x hx => ?_) (fun y y' e => ?_)
    ?_ (fun y y' hy hy' h => ?_) (fun b hb => cubWeil_one_left _ hb) ?_
    (mem_of_cubWeil_orthogonal hL V A G s _ N (Nat.one_le_iff_ne_zero.2 hN0))
  · refine torsion_ext W G _ N (by simpa using hN.map (algebraMap V W)) f' y y' hy hy' ?_
    rw [← hr, ← hr, e]
  · obtain ⟨y, hy, e⟩ := lifts (ι₀ ≫ β x) (fin'.mem_toFinset.2 ⟨x, hx, rfl⟩)
    refine ⟨y, hy, β.injective (Over.OverMorphism.ext ?_)⟩
    have e' : (ι₀ ≫ β x).left = (β x).left := Category.id_comp _
    rw [hβ, hr y, e, e']
  · exact GlobalTheory.over_points_ext_of_injective _ G W _ φ φi _ y y' (congrArg (fun z => z.left) e)
  · refine (torusQuotient_points_lift _ _ _ (t.l 0).Q Ω _).2 N fun a => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hN0)
    have hz0 : z ≠ 0 := by rintro rfl; exact a.ne_zero (by rw [← hz, zero_pow hN0])
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  · have := ((cubWeil_one_iff_closedFibre V A G s t W Ω f' inferInstance _ N hN y y' (r y) (r y') hy hy' (hr y) (hr y')).2 h).comp σ
    rwa [map_one] at this
  · have e : N ^ (2 * A.g) = N ^ Module.finrank ℤ s.X * (N ^ Module.finrank ℤ s.X * N ^ (2 * g')) := by
      rw [hd]; ring
    rw [e]
    exact congrArg₂ (· * ·) ((Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)).trans c₁) c₂

end GlobalTheory.UU.SpecialPairing
end
end
end
