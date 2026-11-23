module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegreesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellationStatement
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinity

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def polyScale (c : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (Polynomial.C c * Polynomial.X)

theorem polyScale_polyScale (c d : F) (p : F[X]) :
    polyScale d (polyScale c p) = polyScale (c * d) p := by
  have : (polyScale d).comp (polyScale c) = polyScale (c * d) := by
    apply Polynomial.algHom_ext
    simp only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, Polynomial.C_mul]
    ring
  exact congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this

theorem polyScale_one (p : F[X]) : polyScale (1 : F) p = p := by
  show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p
  rw [map_one, one_mul, Polynomial.aeval_X_left_apply]

theorem polyScale_injective {c : F} (hc : c ≠ 0) : Function.Injective (polyScale c) := by
  intro p q h
  have := congrArg (polyScale c⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one] at this

theorem rescale_injective {c : F} (hc : c ≠ 0) : Function.Injective (PowerSeries.rescale c) := by
  intro p q h
  have := congrArg (PowerSeries.rescale c⁻¹) h
  rwa [PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc,
    PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at this

theorem transcendental_X : Transcendental F (RatFunc.X : RatFunc F) := by
  rw [transcendental_iff_injective]
  intro p q h
  have e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r := by
    intro r
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [e, e] at h
  exact IsFractionRing.injective F[X] (RatFunc F) h

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def ratScale (c : F) (hc : c ≠ 0) : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (algebraMap F[X] (RatFunc F)).comp (polyScale c).toRingHom)
    ((IsFractionRing.injective F[X] (RatFunc F)).comp (polyScale_injective hc))

noncomputable def lsScale (c : F) (hc : c ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c))
    ((IsFractionRing.injective (PowerSeries F) (LaurentSeries F)).comp (rescale_injective hc))

noncomputable def ratInv : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹).toRingHom)
    (fun x y h => (transcendental_iff_injective.1 fun h => transcendental_X (IsAlgebraic.inv_iff.1 h)) h)

theorem lsScale_comp (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c) :=
  IsLocalization.lift_comp _

theorem ratScale_alg (c : F) (hc : c ≠ 0) (p : F[X]) :
    ratScale c hc (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (polyScale c p) :=
  IsLocalization.lift_eq _ _

theorem ratInv_alg (p : F[X]) :
    ratInv (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p :=
  IsLocalization.lift_eq _ _

theorem ext_rat {A : Type} [CommRing A] {f g : RatFunc F →+* A}
    (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a)) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  apply Polynomial.ringHom_ext
  · intro a; simpa [RatFunc.algebraMap_C] using hC a
  · simpa [RatFunc.algebraMap_X] using hX

theorem ratScale_C (c : F) (hc : c ≠ 0) (a : F) : ratScale c hc (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratScale_alg]; simp [polyScale]

theorem ratScale_X (c : F) (hc : c ≠ 0) :
    ratScale c hc RatFunc.X = RatFunc.C c * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratScale_alg]; simp [polyScale, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem ratInv_C (a : F) : ratInv (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratInv_alg]; simp

theorem ratInv_X : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratInv_alg]; simp

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

theorem alg_C (a : F) : algebraMap (RatFunc F) (LaurentSeries F) (RatFunc.C a) =
    algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.C a) := by
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem alg_X : algebraMap (RatFunc F) (LaurentSeries F) RatFunc.X =
    algebraMap (PowerSeries F) (LaurentSeries F) PowerSeries.X := by
  simp [RatFunc.coe_X]

theorem rescale_C' (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases n with _ | n <;> simp

theorem lsScale_rat (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by
  have hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p) :=
    fun p => RingHom.congr_fun (lsScale_comp c hc) p
  apply ext_rat
  · intro a
    simp only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']
  · simp only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X,
      rescale_C']

theorem ratInv_ratScale (c : F) (hc : c ≠ 0) :
    ratInv.comp (ratScale c hc) = (ratScale c⁻¹ (inv_ne_zero hc)).comp ratInv := by
  apply ext_rat
  · intro a; simp only [RingHom.comp_apply, ratScale_C, ratInv_C]
  · simp only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv,
      inv_inv]

theorem scaling_expansion_infinity :
    ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  intro F _ _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h2' : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  refine ⟨ratScale 2 h2, (algebraMap (RatFunc F) (LaurentSeries F)).comp ratInv, lsScale 2 h2,
    lsScale 2⁻¹ h2', lsScale_comp 2 h2, lsScale_rat 2 h2, lsScale_comp 2⁻¹ h2', ?_, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, lsScale_rat, RingHom.comp_assoc, RingHom.comp_assoc,
      ratInv_ratScale 2 h2]
  · ext a; simp only [RingHom.comp_apply, ratInv_C, alg_C]
  · ext a; simp only [RingHom.comp_apply, alg_C]

end GlobalTheory.Nef.InfScale
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinityStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity : ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  first | exact @GlobalTheory.Nef.InfScale.scaling_expansion_infinity | exact GlobalTheory.Nef.InfScale.scaling_expansion_infinity | (intros; apply GlobalTheory.Nef.InfScale.scaling_expansion_infinity <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueConstantLocalRing

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem comp_grpMul {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (x : T' ⟶ T) (f g : T ⟶ G) :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, Subsingleton.elim (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  have : (η[G] : 𝟙_ (Over S) ⟶ G) ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [comp_grpMul, Category.comp_id, h1, _root_.one_mul]
  exact congrArg (·.left) this

theorem triv_isPath {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (c : R) (b : Sp R ⟶ S) :
    IsPath G c b (triv G b) := by
  refine { base := triv_over G b, zero := ?_, scale := ?_ }
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.constantCoeff (R := R))) = 𝟙 _ := by
      ext x; simp
    rw [this, Spec.map_id, Category.id_comp]
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.rescale c)) = CommRingCat.ofHom (PowerSeries.C (R := R)) := by
      ext x n; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with h <;> simp [h]
    rw [this, Category.assoc, Category.assoc, unitSec_comp_sqr]

theorem eq_unitSec_of_sqr_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (z : Sp R ⟶ G.left)
    (hz : z ≫ sqr G = z) : z = (z ≫ G.hom) ≫ unitSec G := by
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h : z' * z' = z' := by
    have e := comp_grpMul z' (𝟙 G) (𝟙 G)
    rw [Category.comp_id] at e
    rw [← e]
    ext
    exact hz
  have h1 : z' = 1 := by simpa using h
  have h2 := congrArg (·.left) h1
  rw [Hom.one_def] at h2
  refine h2.trans ?_
  rw [Over.comp_left]
  congr 1

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem triv_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  intro S G _ R _
  refine ⟨fun c b => triv_isPath G c b, fun z hz => eq_unitSec_of_sqr_eq G z hz, ?_⟩
  intro _ hq c hc b ξ hξ
  exact GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees S G R hq c 1 one_pos hc b ξ (triv G b) hξ (triv_isPath G c b)
    (fun _ _ _ _ j hj hj' => absurd hj' (by omega))

end GlobalTheory.Nef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueConstantLocalRingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.formalSquaringPath_unique_constant_localRing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  first | exact @GlobalTheory.Nef.triv_unique | exact GlobalTheory.Nef.triv_unique | (intros; apply GlobalTheory.Nef.triv_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isProper_of_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H],
    IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  intro Ω _ _ H _ hP ξ hξ hrat
  obtain ⟨β, hβ⟩ := hrat
  obtain ⟨σ, j, r₂, rh, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity Ω
  have comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by rw [← Spec.map_comp]; rfl
  have compA : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      {Z : Scheme.{0}} (h : Sp A ⟶ Z), spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
    intros; rw [← Category.assoc, comp]
  have canc := (GlobalTheory.T.spec_injectiveRingMap_cancellation).1
  have cancS := (GlobalTheory.T.spec_injectiveRingMap_cancellation).2
  haveI := hP
  haveI : IsSeparated H.hom := inferInstance
  have sqr_hom : sqr H ≫ H.hom = H.hom := Over.w (𝟙 H * 𝟙 H)
  have hi : Function.Injective (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) :=
    IsFractionRing.injective _ _
  have ha : Function.Injective (algebraMap (RatFunc Ω) (LaurentSeries Ω)) := RingHom.injective _
  have hj : Function.Injective j := RingHom.injective _

  have hσ : spMap σ ≫ β = β ≫ sqr H := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [compA, ← h2, ← comp, Category.assoc, hβ, compA, h1, ← compA, hξ.scale, ← Category.assoc,
      ← Category.assoc, hβ]

  have hβb : β ≫ H.hom = spMap RatFunc.C := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, Category.comp_id, comp, comp, h6]
  have hsq : (spMap j ≫ β) ≫ H.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries Ω) (LaurentSeries Ω))) ≫ spMap PowerSeries.C := by
    rw [Category.assoc, hβb, comp, h5]; exact (comp _ _).symm
  have hE : ValuativeCriterion.Existence H.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed H.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) H.hom).1
  let V : ValuativeCommSq H.hom :=
    { R := PowerSeries Ω
      K := LaurentSeries Ω
      i₁ := spMap j ≫ β
      i₂ := spMap PowerSeries.C
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l⟩⟩ := hE V
  have hζ1 : spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ l.l = spMap j ≫ β := l.fac_left
  have hζ2 : l.l ≫ H.hom = spMap PowerSeries.C := l.fac_right
  have hrC : (PowerSeries.rescale (2⁻¹ : Ω)).comp PowerSeries.C = PowerSeries.C := by
    refine RingHom.ext fun x => PowerSeries.ext fun n => ?_
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with hn
    · subst hn; rw [pow_zero, _root_.one_mul]
    · rw [MulZeroClass.mul_zero]
  have hcc : (PowerSeries.constantCoeff (R := Ω)).comp (PowerSeries.rescale (2⁻¹ : Ω)) =
      PowerSeries.constantCoeff (R := Ω) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      _root_.one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hcC : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, PowerSeries.constantCoeff_C]; rfl

  have hζs : spMap (PowerSeries.rescale (2⁻¹ : Ω)) ≫ l.l = l.l ≫ sqr H := by
    refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hζ2, comp, hrC, sqr_hom, hζ2]
    · rw [compA, ← h3, ← comp, Category.assoc, hζ1, compA, h4, ← compA, hσ, ← Category.assoc,
        ← Category.assoc, hζ1]

  have hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((2⁻¹ : Ω) ^ n - 2) := by
    intro n hn
    rw [isUnit_iff_ne_zero, sub_ne_zero, inv_pow]
    intro h
    have h0 : (2 : Ω) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have e : (2 : Ω) ^ (n + 1) = 1 := by
      calc (2 : Ω) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
        _ = 2 ^ n * (2 ^ n)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ h0
    have e' : (2 : ℕ) ^ (n + 1) = 1 := by exact_mod_cast e
    have : 1 < (2 : ℕ) ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hz := (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.1 (spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l)
    (by rw [Category.assoc, ← hζs, compA, hcc])
  have hzero : spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l = 𝟙 (Sp Ω) ≫ unitSec H := by
    rw [hz, Category.assoc (spMap _) l.l H.hom, hζ2, comp, hcC, show spMap (RingHom.id Ω) = 𝟙 (Sp Ω) from Spec.map_id _]
  have hζt : l.l = triv H (𝟙 (Sp Ω)) :=
    (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.2 inferInstance (2⁻¹) hunit (𝟙 _) l.l
      ⟨by rw [Category.comp_id]; exact hζ2, hzero, hζs⟩

  have hβu : β = spMap RatFunc.C ≫ unitSec H := by
    refine canc _ _ j hj _ _ _ ?_
    rw [← hζ1, hζt, triv, Category.id_comp, compA, ← h5, ← compA]
  refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
  · rw [hξ.base, triv_over]
  · rw [← hβ, hβu, compA, h6, triv, Category.id_comp, compA]

end GlobalTheory.Nef
end
end
