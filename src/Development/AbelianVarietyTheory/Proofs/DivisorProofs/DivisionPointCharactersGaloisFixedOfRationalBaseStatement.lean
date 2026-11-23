module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointNthMultipleGaloisFixedPointStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValuesGaloisFixedOfIdempotentTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ETors

open GlobalTheory.BXOf GlobalTheory.TorusExt ReciprocityTheory.ChartRestriction.G.DVR

theorem cubN_pow_eq_pow {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (P : Subgroup A)
    (H : Subgroup U) (hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, θ x y z ∈ H) {n : ℕ} {b d : A} (hb : b ∈ P) (hd : d ∈ P)
    (hn : b ^ n = 1) : ∃ h ∈ H, cubN θ n 1 b (d ^ n) = h ^ n := by
  have hN : cubN θ n 1 b d ∈ H := H.prod_mem fun i _ => hθ _ (P.mul_mem P.one_mem (P.pow_mem hb i)) _ hb _ hd
  have key : ∀ j : ℕ, ∃ r ∈ H, cubN θ n 1 b (d ^ j) = cubN θ n 1 b d ^ j * r ^ n := by
    intro j
    induction j with
    | zero => exact ⟨1, H.one_mem, by rw [pow_zero, C.N_one]; simp⟩
    | succ j ih =>
      obtain ⟨r, hr, e⟩ := ih
      have a := C.N_add n 1 b (d ^ j) d
      rw [hn, _root_.mul_one (1 : A), C.face, _root_.mul_one, _root_.one_mul, e, ← pow_succ] at a
      refine ⟨r * (θ b (d ^ j) d)⁻¹, H.mul_mem hr (H.inv_mem (hθ _ hb _ (P.pow_mem hd j) _ hd)), ?_⟩
      rw [eq_mul_inv_of_mul_eq a, mul_pow, inv_pow, pow_succ (cubN θ n 1 b d), ← _root_.mul_assoc,
        mul_right_comm (cubN θ n 1 b d ^ j)]
  obtain ⟨r, hr, e⟩ := key n
  exact ⟨_ * r, H.mul_mem hN hr, by rw [e, mul_pow]⟩

theorem sig_val_fixed {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {F : Type} [Field F] (σ : F →+* F)
    {J : (Spec (CommRingCat.of F) ⟶ X) → L.ι} (hJ : Good L (closedPoint F) J) (r : Spec (CommRingCat.of F) ⟶ Y)
    (hr : Spec.map (CommRingCat.ofHom σ) ≫ r = r) :
    Units.map σ.toMonoidHom (sig F (val t r (closedPoint F) J)) = sig F (val t r (closedPoint F) J) := by
  have e := val_nat ht σ hJ hJ r
  have hdel : ∀ k, del L σ J J (r ≫ φ k) = 1 := fun k => by
    rw [← del_id hL hJ (r ≫ φ k)]
    unfold del
    rw [← Category.assoc, hr, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [hr, Finset.prod_eq_one (fun k _ => by rw [hdel, one_zpow]), _root_.one_mul] at e
  exact e.symm

theorem exists_c_eq_pow {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (h : DataFrom T iw s ε n Q e) (a : Q.X) :
    ∃ d : 𝟙_ (Over (Sp R)) ⟶ Q.B, Q.c a = d ^ n := by
  obtain ⟨β, -, -, ⟨g, gm⟩, -, -, c, -⟩ := h
  let x : (Fin T.r → ℤ) → (Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap iw) ⟶ T.B) := fun v => toUnit _ ≫ T.c₀ v
  have xl : ∀ v, (x v).left = spMap iw ≫ (T.c₀ v).left := fun v => by
    show (𝟙 _ ≫ spMap iw) ≫ _ = _
    rw [Category.id_comp]
  have xa : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    show toUnit _ ≫ T.c₀ (v + v') = _
    rw [T.c₀_add]; exact MonObj.comp_mul _ _ _
  have w : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 _ ≫ spMap iw := by
    rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (g.lift _ _ w) (g.lift_snd _ _ w)
  have hd : (x (e a)).left = d.left ≫ β := (xl _).trans (g.lift_fst _ _ w).symm
  have key : ∀ k : ℕ, (x (((k + 1 : ℕ) : ℤ) • e a)).left = (d ^ (k + 1)).left ≫ β := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [Nat.cast_succ (k + 1), add_smul, one_smul, xa, pow_succ d (k + 1)]
      exact gm _ _ _ _ _ ih hd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨d, Over.OverMorphism.ext (g.hom_ext ?_ ?_)⟩
  · rw [c, ← key, xl]
  · rw [Over.w, Over.w]

attribute [local instance] gtGroup

theorem charVal_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) (k : ℕ) :
    charVal (k • t) χ y J * cubN (th D y J) k 1 t.b (cP D _ χ) = charVal t χ y J ^ k := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  induction k with
  | zero => rw [zero_nsmul, zero_val χ hJ]; simp [cubN]
  | succ k ih =>
    have a := add_val (k • t) t χ hJ
    rw [nsmul_b, C.s01, C.s12] at a
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [succ_nsmul, pow_succ, ← ih, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, a, mul_right_comm]

theorem corr_pullGen_of_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ hζ Q e hQ _ D' F σ t ht ⟨z, hz, hz0⟩ hb
  set K := AlgebraicClosure (FractionRing R) with hK
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) K :=
    RingHom.ext fun x => σ.commutes x
  have hnt : n • t = 0 := ((isNsmul_iff_eq _ _ _).1 hz).symm.trans ((isZero_iff_eq _).1 hz0)
  choose J hJ using fun ψ : (TF (R := R) K).left ⟶ D'.toPre.P.A.left =>
    exists_chart D'.toPre.P.isLB (ψ (closedPoint K))
  replace hJ : Good D'.toPre.P.L (Z := (TF (R := R) K).left) (closedPoint K) J := hJ
  suffices H : ∀ χ, σ.toAlgHom.toRingHom (sig K (charVal t χ (closedPoint K) J) : K) =
      (sig K (charVal t χ (closedPoint K) J) : K) from
    ((eq_gtExt_iff _ hσ t t).1 (gtExt_eq_self_of_charVal_fixed R D'.toPre K _ hσ t hb J hJ H).symm).2
  let H : Subgroup ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ :=
    MonoidHom.eqLocus ((Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp (sig K)) (sig K)
  let P : Subgroup (TF (R := R) K ⟶ D'.toPre.P.A) :=
    { carrier := {x | extMap _ hσ ≫ x = x}
      mul_mem' := fun {a b} ha hb => (MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) ha hb)
      one_mem' := MonObj.comp_one _
      inv_mem' := fun {a} ha => (GrpObj.comp_inv _ _).trans (congrArg (·⁻¹) ha) }
  have hP : ∀ d : 𝟙_ (Over (Sp R)) ⟶ D'.toPre.P.A, toUnit _ ≫ d ∈ P := fun d => by
    show extMap _ hσ ≫ toUnit _ ≫ d = toUnit _ ≫ d
    rw [← Category.assoc, toUnit_unique (extMap _ hσ ≫ toUnit _) (toUnit _)]
  have hbP : t.b ∈ P := Over.OverMorphism.ext hb
  have hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, th D'.toPre (T := TF (R := R) K) (closedPoint K) J x y z ∈ H := by
    intro x hx y hy z hz
    refine sig_val_fixed D'.toPre.P.isLB D'.toPre.cub.isGen _ hJ (lift x (lift y z)).left ?_
    show (extMap _ hσ ≫ lift x (lift y z)).left = _
    rw [comp_lift, comp_lift, hx, hy, hz]
  have C : IsCub (th D'.toPre (T := TF (R := R) K) (closedPoint K) J) := isCub_cubV D'.toPre.cub hJ

  have := F.o.onB.hom F.e
  have := F.o.onB.hom (star F.e)
  have := F.o.onB.hom F.f
  have := F.inc_hom
  have hr := F.o.onB.rosati (star F.e)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros GlobalTheory.SemiRigid.globalFns D'.toPre.P.isAb D'.toPre.P.isLB _ _ hr
  have rel : ∀ χ, ∃ h ∈ H, charVal t χ (closedPoint K) J = charVal t (star F.e • χ) (closedPoint K) J * h := by
    intro χ
    refine ⟨val u (lift (cP D'.toPre _ χ) t.b).left (closedPoint K) J, ?_, ?_⟩
    · refine sig_val_fixed D'.toPre.P.isLB hu _ hJ (lift (cP D'.toPre _ χ) t.b).left ?_
      show (extMap _ hσ ≫ lift (cP D'.toPre _ χ) t.b).left = _
      rw [comp_lift, comp_cP, hbP]
    · refine (val_corr hJ (ht.2 u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      rw [val_pull hJ, Category.id_comp]; rfl

  have root : ∀ w : ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ, w ^ n = 1 → w ∈ H := by
    intro w hw
    have hinj : Function.Injective ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))) :=
      (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)
    have hζ' := hζ.map_of_injective hinj
    have : NeZero n := ⟨by omega⟩
    have hw' : (sig K w : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw'
    have e : σ (sig K w : K) = (sig K w : K) :=
      (congrArg σ hi.symm).trans ((map_pow σ _ i).trans ((congrArg (· ^ i) (σ.commutes _)).trans hi))
    exact Units.ext e

  have img : ∀ a : Q.X, charVal t (F.f • F.xi a) (closedPoint K) J ∈ H := by
    intro a
    obtain ⟨d, hd⟩ := exists_c_eq_pow T iw s ε hn Q e hQ a
    have hc : cP D'.toPre (TF (R := R) K) (F.f • F.xi a) = (toUnit _ ≫ (d ≫ F.inc) ≫ F.o.onB.act F.f) ^ n := by
      rw [cP, F.o.c_lin, F.c_xi, hd, MonObj.pow_comp, MonObj.pow_comp, MonObj.comp_pow]
    have hbn : t.b ^ n = 1 := by rw [← nsmul_b, hnt, zero_b]
    obtain ⟨h, hh, e₁⟩ := cubN_pow_eq_pow C P H hθ hbP (hP ((d ≫ F.inc) ≫ F.o.onB.act F.f)) hbn
    have e₂ := charVal_pow t (F.f • F.xi a) hJ n
    rw [hnt, zero_val (D := D'.toPre) (F := K) _ hJ, _root_.one_mul, hc, e₁] at e₂
    have := H.mul_mem (root (charVal t (F.f • F.xi a) (closedPoint K) J * h⁻¹)
      (by rw [mul_pow, ← e₂, inv_pow, mul_inv_cancel])) hh
    rwa [inv_mul_cancel_right] at this
  intro χ
  obtain ⟨a, ha⟩ := F.onto χ
  obtain ⟨h, hh, e₁⟩ := rel χ
  obtain ⟨h', hh', e₂⟩ := rel (F.f • F.xi a)
  have m : charVal t χ (closedPoint K) J ∈ H := by
    rw [e₁, ha, eq_mul_inv_of_mul_eq e₂.symm]
    exact H.mul_mem (H.mul_mem (img a) (H.inv_mem hh')) hh
  exact congrArg Units.val m

end GlobalTheory.Mum.ETors
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValuesGaloisFixedOfIdempotentTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.characterValues_galoisFixed_of_idempotent_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  first | exact @GlobalTheory.Mum.ETors.corr_pullGen_of_torsion | exact GlobalTheory.Mum.ETors.corr_pullGen_of_torsion | (intros; apply GlobalTheory.Mum.ETors.corr_pullGen_of_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusExt

noncomputable section

namespace GlobalTheory.Mum.IdemDiff

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem val_act (oa : D.OAct O) (a : O)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))

theorem gtPtAct_of_isAdd : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  intro R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hs : star a * star a = star a := by rw [← star_mul, ha]
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a := by rw [← oa.onB.map_mul, ha]
  have ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a) := by rw [← oa.onB.map_mul, hs]
  obtain ⟨b₁, v₁⟩ := (isAdd_iff_val _ _ _).1 hadd
  have gb : g.b = g.b ≫ oa.onB.act a := by rw [hg.1, Category.assoc, ← aa]
  have tb : t.b = t.b ≫ oa.onB.act a := by
    have e := gb
    rw [b₁, MonObj.mul_comp, ← hh.1] at e
    exact mul_right_cancel e
  refine ⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩
  have vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b := fun χ =>
    (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)
  have vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b :=
    (val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)
  have vc := IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b
  have vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
    rw [vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]
  have ra := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2
  rw [← tb, ← hh.1, ← b₁] at ra
  have e₂ := v₁ (star a • χ) y J hJ
  rw [cf] at e₂
  have a₁ := congrArg Additive.ofMul ra
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul (v₁ χ y J hJ)
  have a₄ := congrArg Additive.ofMul vg'
  have a₅ := congrArg Additive.ofMul vh
  show _ = charVal t χ y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₃ - a₄ + a₅ - a₁ - a₂

end GlobalTheory.Mum.IdemDiff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  first | exact @GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | exact GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | (intros; apply GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.TorusExt
attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Mum.RatChar

theorem charFixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hact hb χ
  let f : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing R) := σ.toAlgHom.toRingHom
  have hf : f.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := σ.toAlgHom.comp_algebraMap
  have hB := D'.tau_bimult
  obtain ⟨h, ⟨hhb, hhs⟩, ⟨z, hz, hzι⟩, hhe⟩ := GlobalTheory.T.lattice_point_nth_multiple_galois_fixed_point T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ (F.xp p₀.y)
  have hya : p.y = F.xi (F.xp p₀.y) := by rw [hy, F.xi_xp]
  have hg : n • p.g = iota hB _ p.y := by
    obtain ⟨z', hz', hz'ι⟩ := p.eq
    rw [← (isNsmul_iff_eq _ _ _).1 hz', ← (isIota_iff_eq hB _ _).1 hz'ι]
  have hh : n • h = iota hB _ p.y := by
    rw [hya, ← (isNsmul_iff_eq _ _ _).1 hz, ← (isIota_iff_eq hB _ _).1 hzι]
  set t := p.g - h with ht
  have htn : n • t = 0 := by rw [ht, nsmul_sub, hg, hh, sub_self]
  have hte : GtPtAct F.o F.e t t :=
    GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent F.o F.e F.idem p₀.g p.g h t hact hhe ((isAdd_iff_eq _ _ _).2 (sub_add_cancel p.g h).symm)
  have hfixh : gtExt D'.toPre f hf h = h := ((eq_gtExt_iff f hf h h).2 ⟨hhb.symm, hhs⟩).symm
  have hgb : extMap f hf ≫ p.g.b = p.g.b := by
    obtain ⟨b, hb⟩ := hb
    apply Over.OverMorphism.ext
    rw [Over.comp_left, extMap_left, hb, ← Category.assoc]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  have htb : extMap f hf ≫ t.b = t.b := by
    have e1 : gtExt D'.toPre f hf t = gtExt D'.toPre f hf p.g - h := by rw [ht, map_sub, hfixh]
    have e2 := congrArg GtPtF.b e1
    rw [gtExt_b, sub_eq_add_neg, add_b, neg_b, gtExt_b, hgb] at e2
    rw [e2, ht, sub_eq_add_neg, add_b, neg_b]
  have htb' : spMap f ≫ t.b.left = t.b.left := by
    have := congrArg (fun q => q.left) htb
    simpa [Over.comp_left, extMap_left] using this
  have hts := GlobalTheory.T.characterValues_galoisFixed_of_idempotent_torsion T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ t hte ⟨0, (isNsmul_iff_eq _ _ _).2 htn.symm, (isZero_iff_eq _).2 rfl⟩ htb'
  have hfixt : gtExt D'.toPre f hf t = t := ((eq_gtExt_iff f hf t t).2 ⟨htb'.symm, hts⟩).symm
  have hfixg : gtExt D'.toPre f hf p.g = p.g := by
    have : p.g = t + h := (sub_add_cancel p.g h).symm
    rw [this, map_add (f := _), hfixt, hfixh]
  exact ((eq_gtExt_iff f hf p.g p.g).1 hfixg.symm).2 χ

end GlobalTheory.Mum.RatChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  first | exact @GlobalTheory.Mum.RatChar.charFixed | exact GlobalTheory.Mum.RatChar.charFixed | (intros; apply GlobalTheory.Mum.RatChar.charFixed <;> assumption)
end
end
