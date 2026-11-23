module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFamiStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbeliaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyOfTensorDataPosDefUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomialStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetricStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  first | exact @GlobalTheory.Mum.canon_isBiRig | exact GlobalTheory.Mum.canon_isBiRig | (intros; apply GlobalTheory.Mum.canon_isBiRig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinements

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonFam

theorem gm_iso {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (hp : x ∈ B.U p.1 ⊓ A.U p.2) (hq : x ∈ B.U q.1 ⊓ A.U q.2) :
    gm (𝟙 X) x _ (w.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (w.s q) := by
  have hm : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨hp, hq⟩
  have e := congrArg (gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2))) (hw p q)
  exact (gm_res _ x _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) x p q hm) (gm_res _ x _ hm _))))

theorem lbIso_trans {X : Scheme.{0}} {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨w', hw'⟩ := H'

  have cself : ∀ (x : X) (r : C.ι) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      gm (𝟙 X) x (C.U r ⊓ C.U r) (C.g r r) = 1 := by
    intro x r p hr hp
    have e := gm_iso hw' x (r, p) (r, p) ⟨hr, hp⟩ ⟨hr, hp⟩
    rw [gm_self hB (𝟙 X) x hp, inv_one, _root_.mul_one] at e
    exact mul_eq_right.1 e.symm
  have glue : ∀ (r : C.ι) (i : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U i)ˣ, ∀ (x : X) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      x ∈ A.U i → gm (𝟙 X) x _ s = gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := by
    intro r i
    let W : B.ι → X.Opens := fun p => C.U r ⊓ B.U p ⊓ A.U i
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U i := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => hx.1
    have l₂ : ∀ p, W p ≤ B.U p ⊓ A.U i := fun p x hx => ⟨hx.1.2, hx.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₁ p) (w'.s (r, p)) * res (l₂ p) (w.s (p, i))
    have hu : ∀ (x : X) (p : B.ι) (hx : x ∈ W p), gm (𝟙 X) x (W p) (u p) =
        gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := fun x p hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x (l₁ p) hx _) (gm_res _ x (l₂ p) hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U r ⊓ A.U i) W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, ⟨⟨hx.1, hp⟩, hx.2⟩⟩) u (fun p p' x hx => by
        rw [hu x p hx.1, hu x p' hx.2]
        have hr : x ∈ C.U r := hx.1.1.1
        have hp : x ∈ B.U p := hx.1.1.2
        have hp' : x ∈ B.U p' := hx.2.1.2
        have hi : x ∈ A.U i := hx.1.2
        rw [gm_iso hw' x (r, p) (r, p') ⟨hr, hp⟩ ⟨hr, hp'⟩, gm_iso hw x (p, i) (p', i) ⟨hp, hi⟩ ⟨hp', hi⟩]
        simp only []
        rw [cself x r p hr hp, gm_self hA (𝟙 X) x hi, inv_one]
        simp only [_root_.one_mul, _root_.mul_one]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun x p hr hp hi => ?_⟩
    have hx : x ∈ W p := ⟨⟨hr, hp⟩, hi⟩
    exact (gm_res _ x (l₀ p) hx s).symm.trans ((congrArg (gm (𝟙 X) x (W p)) (hs p)).trans (hu x p hx))
  choose s hs using glue
  refine ⟨⟨fun q => s q.1 q.2⟩, fun q q' => unit_ext fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have hr : x ∈ C.U q.1 := hx.1.1
  have hi : x ∈ A.U q.2 := hx.1.2
  have hr' : x ∈ C.U q'.1 := hx.2.1
  have hi' : x ∈ A.U q'.2 := hx.2.2
  have hm : (𝟙 X : X ⟶ X) x ∈ C.U q.1 ⊓ A.U q.2 ⊓ (C.U q'.1 ⊓ A.U q'.2) := hx
  refine (gm_res _ x _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C (𝟙 X) x q q' hm) (gm_res _ x _ hx _))).symm)
  show gm (𝟙 X) x _ (s q.1 q.2) = _ * _ * gm (𝟙 X) x _ (s q'.1 q'.2)
  rw [hs q.1 q.2 x p hr hp hi, hs q'.1 q'.2 x p hr' hp hi',
    gm_iso hw' x (q.1, p) (q'.1, p) ⟨hr, hp⟩ ⟨hr', hp⟩, gm_iso hw x (p, q.2) (p, q'.2) ⟨hp, hi⟩ ⟨hp, hi'⟩]
  simp only []
  rw [gm_self hB (𝟙 X) x hp, inv_one]
  simp only [_root_.one_mul, _root_.mul_one]
  ac_rfl

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

end GlobalTheory.Mum.CanonFam


open GlobalTheory.Mum.CanonFam in
theorem GlobalTheory.Mum.CanonFam.exists_unif_refines : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro R _ _ _ hR Q G _ _ P hG hC R' _ _ _ ρ hR' hinj hfin D ε hRef
  obtain ⟨D', F, hF, A', G', _, _, U', oA, oG, G₁, _, _, inc, pr, π, π₂, hG', hlin, hG₁, hinc, hpr, hip, hpi, hpb, hsq,
    hlb⟩ := GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily R hR Q G P hG hC R' ρ hR' hinj hfin D ε hRef
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data R' (base_of_isCN hR') D D' F hF A' G' hG' U' oA oG hlin G₁ hG₁ inc pr hinc hpr hip hpi
  refine ⟨G₁, inferInstance, inferInstance, π, π₂, A, U, hpb, hsq, ?_⟩
  have l1 : (abelian₂ G₁ U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have l2 : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  exact lbIso_trans l1 (pull_isLB l2 _) hU hlb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinementsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.canonical_mumford_family_uniformises_refinements : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.CanonFam.exists_unif_refines | exact GlobalTheory.Mum.CanonFam.exists_unif_refines | (intros; apply GlobalTheory.Mum.CanonFam.exists_unif_refines <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) →
  ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
  ∃ (D' : DegData R (maximalIdeal R)) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) ∧
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) ∧ w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tensPol | exact GlobalTheory.Mum.TensPol.exists_tensPol | (intros; apply GlobalTheory.Mum.TensPol.exists_tensPol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriods

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_canonOn_of_isMonomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  intro R _ _ _ hR Q hQ m t β hm ht hs h0 h1
  have hpd : ((GlobalTheory.W8 + GlobalTheory.W8.transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [GlobalTheory.w8_add_transpose_eq_e8]; exact GlobalTheory.e8_posDef
  have hdet : IsUnit (GlobalTheory.W8 + GlobalTheory.W8.transpose).det := by
    rw [GlobalTheory.w8_add_transpose_eq_e8, GlobalTheory.e8_det_eq_one]; exact isUnit_one
  obtain ⟨D', pr, xe, w, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form R hR Q hQ GlobalTheory.W8 hpd hdet
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular R hR Q D' GlobalTheory.W8 hpd hdet (by norm_num) pr xe w h₁ h₂ h₃ h₄ h₅
  obtain ⟨β', hβ', -⟩ := GlobalTheory.T.polarisedDegeneration_tensorPower_monomial R Q D'.toPre GlobalTheory.W8 pr xe hpd ⟨h₁, h₂, h₃, w, h₄, h₅⟩ m t β hm ht hs h0 h1
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  obtain ⟨G', iG, cG, A', hsa, ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hB D'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hsa U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, iG2, cutoffSecondDeriv, inc, pr', hsaG, hinc, hpr, e₁, e₂⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hsa (oG.act F.e) (oG.hom F.e) hidem
  have hL : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have hC : CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G _ := ⟨pull_isLB hL _, D', F, A', G', iG, cG, U', oA, oG, inc, pr',
    fun y => hβ'.psiUnitOn y fun p hp => hp, hsa, hlin, hinc, hpr, e₁, e₂, ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩⟩
  exact ⟨G, iG2, cutoffSecondDeriv, _, ⟨hR, hQ, hsaG, GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric R hR Q G _ hC.canon, GlobalTheory.T.canonical_mumford_family_uniformises_refinements R hR Q G _ hsaG hC.canon⟩, hC⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriodsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_canonical_mumford_family_monomial_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  first | exact @GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | exact GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | (intros; apply GlobalTheory.Mum.exists_canonOn_of_isMonomialTau <;> assumption)
end
end
