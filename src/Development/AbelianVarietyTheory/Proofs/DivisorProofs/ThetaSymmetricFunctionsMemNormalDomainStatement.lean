module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListsUniqueUpToPermScalarStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCoverStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPerm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymCmp

theorem grpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq_of_f {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq_of_f (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_ext_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  intro S G _ _ L ρ hL hρ g m R _ x θ hm hu hP K F _ _ i i' φ hi N pt c pt' c' H H'
  subst hi
  obtain ⟨p₁, -, h₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N K F φ (spMap i ≫ x) (SecAt.pull G L θ i) pt c H
  simp only [SecAt.pull] at h₁
  rw [pullS_pullS G hL] at h₁
  have ey : spMap φ ≫ spMap i ≫ x = spMap (φ.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ringHom]
  have key : ∀ {y y' : Sp F ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x),
      u.left = u'.left → ∀ {p : Fin N → (Over.mk y ⟶ G)} {d : Fin N → F},
      ThList G L ρ m y (VVRank.pullS G _ u θ) p d →
      ∃ p' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) p' d := by
    intro y y' e u u' hu p d h
    subst e
    obtain rfl : u = u' := Over.OverMorphism.ext hu
    exact ⟨p, h⟩
  obtain ⟨q₁, H₁⟩ := key ey _ (Over.homMk (spMap (φ.comp i)) rfl : Over.mk (spMap (φ.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ringHom]) h₁
  have hPy : PolFib G L g (spMap (φ.comp i) ≫ x) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_id G)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g R x).2 F (φ.comp i) hP
  have hmF : (m : F) ≠ 0 := by
    rw [← map_natCast (φ.comp i) m]
    exact (hu.map (φ.comp i)).ne_zero
  exact (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar S G L ρ hL hρ g m m N N F (spMap (φ.comp i) ≫ x) hm hmF hm hmF hPy).1 _ q₁ pt' _ c' H₁ H'

end GlobalTheory.UMin.SymCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPermStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  first | exact @GlobalTheory.UMin.SymCmp.thList_ext_perm | exact GlobalTheory.UMin.SymCmp.thList_ext_perm | (intros; apply GlobalTheory.UMin.SymCmp.thList_ext_perm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UMin.SymRing

theorem exists_common_field : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁], Module.FaithfullyFlat R R₁ → ∀ (K : Type) [Field K] (i : R →+* K), ∃ (K' : Type) (_ : Field K') (φ : K →+* K') (i₁ : R₁ →+* K'), i₁.comp (algebraMap R R₁) = φ.comp i := by
  intro R R₁ _ _ _ hff K _ i
  letI : Algebra R K := i.toAlgebra
  haveI : Nontrivial (K ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ K
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R] R₁)
  letI : Field ((K ⊗[R] R₁) ⧸ M) := Ideal.Quotient.field M
  refine ⟨(K ⊗[R] R₁) ⧸ M, inferInstance,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := R₁)).toRingHom,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := R₁)).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.commutes, show i r = algebraMap R K r from rfl, AlgHom.commutes]

theorem symTup_map' {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun a => i (c a)) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem symTup_perm' {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  funext j
  show _ = (Finset.univ.val.map c).esymm _ ^ _
  rw [symTup, ← Function.comp_def c σ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem sym_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N R _ _ _ _ _ x θ hm hmu hN hP
  obtain ⟨R₁, _, _, c, hfin, hff, hc⟩ := GlobalTheory.T.theta_constants_functions_finite_flat_cover S G L ρ hL hρ g m N R x θ hm hmu hN hP
  have hP' : ∀ j, ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) →
      i₁ (symTup c j) = i₂ (symTup c j) := by
    intro j K _ i₁ i₂ h
    obtain ⟨pt₁, h₁⟩ := hc K (i₁.comp (algebraMap R R₁)) i₁ rfl
    obtain ⟨pt₂, h₂⟩ := hc K (i₁.comp (algebraMap R R₁)) i₂ h.symm
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K _ _ (RingHom.id K) (RingHom.id_comp _) N pt₁ _ pt₂ _ h₁ h₂
    rw [symTup_map', symTup_map', funext hσ]
    exact (symTup_perm' (fun b => i₁ (c b)) σ).symm ▸ rfl
  choose e he using fun j => GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat R R₁ hfin hff (symTup c j) (hP' j)
  refine ⟨e, fun K _ i pt c' hl j => ?_⟩
  obtain ⟨K', _, φ, i₁, hφ⟩ := exists_common_field R R₁ hff K i
  obtain ⟨pt₁, h₁⟩ := hc K' (φ.comp i) i₁ hφ
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K' i (φ.comp i) φ rfl N pt c' pt₁ _ hl h₁
  apply φ.injective
  have h1 : φ (i (e j)) = i₁ (algebraMap R R₁ (e j)) := by rw [← RingHom.comp_apply, ← RingHom.comp_apply, hφ]
  rw [h1, ← he j K' i₁, symTup_map', symTup_map', funext hσ]
  exact congrFun (symTup_perm' (fun a => φ (c' a)) σ) j

end GlobalTheory.UMin.SymRing

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  first | exact @GlobalTheory.UMin.SymRing.sym_ring | exact GlobalTheory.UMin.SymRing.sym_ring | (intros; apply GlobalTheory.UMin.SymRing.sym_ring <;> assumption)
end
end
