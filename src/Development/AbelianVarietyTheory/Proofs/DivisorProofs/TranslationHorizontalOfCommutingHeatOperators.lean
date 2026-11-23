module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatiosStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationExtensionOfAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocDerKDesc

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem desc_agree (hdd : ∀ a, IsField ⊤ (dd a)) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (V : h.J → Q.P.A.left.Opens) (hV : ∀ i, h.W i = Y.q.left ⁻¹ᵁ V i)
    (e : h.J → Fld Q.P.A.left)
    (hq : ∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (e i V' f) = h.d i _ ((Y.q.left.app V').hom f))
    (i i' : h.J) (W : Q.P.A.left.Opens) (hW : W ≤ V i ⊓ V i') (f : Γ(Q.P.A.left, W)) :
    (m.app W).hom (e i W f) = (m.app W).hom (e i' W f) := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  refine FunDescent.app_injective b _ ?_
  show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
  rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
  refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
    ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
  · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    rwa [map_ofNat] at this
  · rw [hc, hΘ, constFn, map_zero, map_zero]

end Ray

theorem exists_locDerK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a, IsField ⊤ (dd a)) → IsBasic Y h → ∀ {K : Type} [Field K] [CharZero K] (φ : R →+* K), (∀ a b, φ (h.Θ a b) = 0) → ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left), m ≫ Q.P.A.hom = p ≫ spMap φ → ∃ dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W), GlobalTheory.KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ dl ∧ (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m → ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB K _ _ φ hΘ Z p m hm
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  have hc := fun i i' W hW f => desc_agree Y h hdd φ hΘ p m hm V hV e hq i i' W hW f
  have hcov : ∀ y, ∃ i, m y ∈ V i := fun y => by
    obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  have hloc : ∀ i, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) (V i) (fun W f => (m.app W).hom (e i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add (f := _)]
    · rw [(he i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  obtain ⟨dl, hdl, hu⟩ := InteriorKS.glue_along p Q.P.A.hom m _ V hcov (fun i W f => (m.app W).hom (e i W f)) hloc hc
  refine ⟨dl, hdl, fun Z' a b w i W hWi f => ?_⟩
  have hWV : W ≤ V i := fun x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    exact (hWi.trans (hV i).le) hx
  have e1 : dl W f = (m.app W).hom (e i W f) := by
    refine hu W f _ fun j => ?_
    rw [res_app m inf_le_left, ← (he i).1.2.2 W (W ⊓ V j) inf_le_left hWV f]
    exact hc i j _ (le_inf (inf_le_left.trans hWV) inf_le_right) _
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  rw [e1, pbT, pbT, dite_eq_left (le_refl _), dite_eq_left hle, ← hq i W hWV]
  have k : ∀ (c : Z' ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W) x,
      (b.appLE (m ⁻¹ᵁ W) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (le_refl _)).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
    rintro _ rfl hc x
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [k (a ≫ Y.q.left) w (by rw [Scheme.Hom.comp_preimage]; exact hle)]
  exact congrArg (fun ψ => ψ.hom (e i W f)) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)

end GlobalTheory.Heat.AbConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTer

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gens

theorem res_ι_app {X : Scheme.{0}} (U : X.Opens) (V : U.toScheme.Opens) (x : Γ(X, U.ι ''ᵁ V))
    (hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    (U.toScheme.presheaf.map (homOfLE hle).op).hom ((U.ι.app (U.ι ''ᵁ V)).hom x) = x := by
  have h1 := Scheme.Hom.appIso_hom U.ι V
  rw [Scheme.Opens.ι_appIso] at h1
  have h3 := congrArg (fun f => f.hom x) h1
  simp only [Iso.refl_hom, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact (congrArg (fun f => (U.toScheme.presheaf.map f).hom ((U.ι.app (U.ι ''ᵁ V)).hom x))
    (Subsingleton.elim (homOfLE hle).op _)).trans h3.symm

theorem gs_ι {X : Scheme.{0}} (U : X.Opens) (j : X ⟶ U.toScheme) (hj : j ≫ U.ι = 𝟙 X) (V : U.toScheme.Opens)
    (x : Γ(X, U.ι ''ᵁ V)) (y : X) (hy : j y ∈ V) : gs j y V x = gs (𝟙 X) y (U.ι ''ᵁ V) x := by
  have hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq U.ι V).ge
  have e := gs_res j y hle hy ((U.ι.app (U.ι ''ᵁ V)).hom x)
  rw [res_ι_app] at e
  rw [e, gs_pull j U.ι y _ (hle hy), hj]

theorem gens : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R), ∃ N : ℕ, 1 ≤ N ∧ ∃ (Ix : Type) (U : Ix → Q.P.A.left.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(Q.P.A.left, U i)), (⨆ i, U i = ⊤) ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) ∧ ∀ i j, ∃ σ σ' : Q.SecB N 0, ∀ z ∈ U i, ∀ J, Good Q.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z (U i) (r i j) * sval σ' (𝟙 _) z J := by
  intro R _ _ Q
  obtain ⟨N, hN, M, s, hcov, hs⟩ := Q.P.ample ⊤ (isAffineOpen_top _)
  choose haff r hr hsurj using hs
  let ιU := (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).ι
  let j : Q.P.A.left ⟶ (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).toScheme := Q.P.A.left.topIso.inv
  have hj : j ≫ ιU = 𝟙 _ := by
    show Q.P.A.left.topIso.inv ≫ (⊤ : Q.P.A.left.Opens).ι = _
    rw [← Scheme.topIso_hom, Iso.inv_hom_id]
  have hιj : ιU ≫ j = 𝟙 _ := by
    show (⊤ : Q.P.A.left.Opens).ι ≫ Q.P.A.left.topIso.inv = _
    rw [← Scheme.topIso_hom, Iso.hom_inv_id]; rfl
  have hjι : ∀ w, j (ιU w) = w := fun w => by show (ιU ≫ j).base w = w; rw [hιj]; rfl
  have hfe : FormEq (K := Fin N) (fun _ => 𝟙 Q.P.A.left) (fun _ => (1 : ℤ)) (Q.famφB 0) (DegPre.famε N) := by
    intro U _ h
    refine Eq.trans ?_ (GlobalTheory.Mum.OriginSec.formEq_zero Q N U h)
    simp [Finset.prod_const, Fin.prod_univ_one]
  have hσ : ∀ a, ∃ σ : Q.SecB N 0, ∀ (z : Q.P.A.left) J, Good Q.P.L z J → sval σ (𝟙 _) z J = sval (s a) j z J := by
    intro a
    obtain ⟨s', hs'⟩ := GlobalTheory.UU.exists_pullSec_sval
      (s a : LB.Sec (LB.LinComb Q.P.L (K := Fin N) (fun _ => ιU) (fun _ => (1 : ℤ)))) j
      (fun _ : Fin N => 𝟙 Q.P.A.left) (fun _ => hj)
    obtain ⟨σ, hσ⟩ := exists_sec Q.P.isLB hfe s'
    exact ⟨σ, fun z J hJ => (hσ _ _ z J hJ).trans ((hs' _ _ z J hJ).trans (by rw [Category.id_comp]))⟩
  choose σ hσv using hσ
  refine ⟨N, hN, Fin (M + 1), fun a => ιU ''ᵁ nonzeroLocus (s a), fun _ => Fin (M + 1), fun a b => r a b, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show j y ∈ ⨆ a, nonzeroLocus (s a) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ⟨j y, ha, show (j ≫ ιU).base y = y by rw [hj]; rfl⟩⟩
  · exact fun a => (haff a).image_of_isOpenImmersion ιU
  · intro a
    have key : ∀ (U U' : (Spec (CommRingCat.of R)).Opens) (_ : U = U') (W : Q.P.A.left.Opens) e e'
        (rr : Fin (M + 1) → Γ(Q.P.A.left, W)),
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U' W e').hom rr) →
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U W e).hom rr) := by
      rintro _ _ rfl _ _ _ _ h; exact h
    have e2 := morphismRestrict_appLE Q.P.A.hom ⊤ ⊤ (nonzeroLocus (s a)) le_top
    have h' := (congrArg (fun g => Function.Surjective (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom g) (r a))) e2).mp (hsurj a)
    exact key ⊤ ((⊤ : (Spec (CommRingCat.of R)).Opens).ι ''ᵁ ⊤) (Scheme.Opens.ι_image_top _).symm
      (ιU ''ᵁ nonzeroLocus (s a)) _ _ (r a) h'
  · intro a b
    refine ⟨σ b, σ a, fun z hz J hJ => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hσv _ _ _ hJ, hσv _ _ _ hJ]
    have hm := hJ.mem (fun _ : Fin N => ιU) j
    have hw' : j (ιU w) ∈ nonzeroLocus (s a) := by rw [hjι]; exact hw
    refine ⟨(GlobalTheory.Mum.OriginSec.isUnit_sval_iff' (s a) j (ιU w) hJ).2 hw', ?_⟩
    have hm' : j (ιU w) ∈ nonzeroLocus (s a) ⊓ (powOver Q.P.A Q.P.L ⊤ N).U (fun _ => J (j ≫ ιU)) := ⟨hw', hm⟩
    have e := congrArg (gs j (ιU w) _) (hr a b (fun _ => J (j ≫ ιU)))
    rw [gs_res _ _ _ hm', gs_mul _ _ _ hm', gs_res _ _ _ hm', gs_res _ _ _ hm'] at e
    rw [gs_ι _ j hj _ (r a b) _ hw'] at e
    exact e
end GlobalTheory.Heat.Gens
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocDerKMono

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Heat.DerComm
open GlobalTheory.KS GlobalTheory.LocDerExt

theorem appLE_congr {X Y : Scheme.{0}} {g g' : Y ⟶ X} (e : g = g') (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (h' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V h = g'.appLE U V h' := by
  subst e; rfl

theorem locDerK_mono {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ W₁ : X.Opens}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D W₀ d) (hW : W₁ ≤ W₀) :
    LocDerK q p m D W₁ d :=
  ⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW),
   fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩

theorem eq_of_gen {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {V : X.Opens}
    {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D V d)
    (h' : LocDerK q p m D V d') {M : Type} (r : M → Γ(X, V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ V (fun _ _ => trivial)).hom r))
    (he : ∀ j, d V (r j) = d' V (r j)) : d V = d' V := by
  funext f
  obtain ⟨P, rfl⟩ := hs f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := by
      simp
    have : (p.appLE ⊤ V (fun _ _ => trivial)).hom a =
        constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
      unfold constFn; rw [e]
    rw [this, h.base V le_rfl, h'.base V le_rfl]
  | add P Q hP hQ => rw [map_add (f := _), h.add V le_rfl, h'.add V le_rfl, hP, hQ]
  | mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]

theorem comm_of_gen : ∀ {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (dl : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK q p m D ⊤ dl → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y), T₀ ≫ m = m ≫ T → T₀ ≫ q = q → T ≫ p = p → ∀ (Ix : Type) (U : Ix → X.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(X, U i)), (⨆ i, U i = ⊤) → (∀ i, IsAffineOpen (U i)) → (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) → (∀ i j, dl (T ⁻¹ᵁ U i) ((T.app (U i)).hom (r i j)) = pbT T₀ (dl (U i) (r i j)) (m ⁻¹ᵁ (T ⁻¹ᵁ U i))) → ∀ (W : X.Opens) (f : Γ(X, W)), dl (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (dl W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W)) := by
  intro R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg
  have pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V) := fun V => by
    rw [← hm]; exact le_rfl
  have app1 : ∀ (V : X.Opens) (g : Γ(X, V)),
      (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g := by
    intro V g; rw [Scheme.Hom.comp_app]; rfl
  have app2 : ∀ (V : X.Opens) (g : Γ(X, V)),
      pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g := by
    intro V g
    rw [pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    have := congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))
    refine this.trans ?_
    exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)
  let d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)
  let d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)
  have h1 : LocDerK q p (m ≫ T) D ⊤ d1 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d1, map_add (f := _)]; exact hdl.add _ le_top _ _
    · simp only [d1, map_mul]; rw [hdl.mul _ le_top, app1, app1]; exact rfl
    · simp only [d1]; rw [app_res T h, hdl.res _ _ _ le_top]; rfl
    · simp only [d1]
      rw [Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]
      exact hdl.base _ le_top a
  have h2 : LocDerK q p (m ≫ T) D ⊤ d2 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d2]; rw [hdl.add _ le_top, pbT_add]
    · simp only [d2]; rw [hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]
    · simp only [d2]
      rw [hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]
    · simp only [d2]; rw [hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]
  have key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V := fun i V hV =>
    GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top)
      (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV
  intro W f
  show d1 W f = d2 W f
  refine eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_
  · intro y hy
    have : (m ≫ T).base y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  · intro k
    rw [← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]

end GlobalTheory.Heat.DerComm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCommutesTranslation

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTranslW

theorem lift_commutes_translation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl ∧ ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀
  let φ : ChartRing k m d →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  have hφΘ : ∀ a b, φ (h.Θ a b) = 0 := fun a b => by
    have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
      by_contra hne
      exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
    simp [φ, hρ, h0]
  obtain ⟨dl, hdl, hdesc⟩ := GlobalTheory.Heat.AbConst.exists_locDerK_desc Y h (fun a => (hinv a).1) hB φ hφΘ A₀.hom m₀ hm₀.1.w
  have hD : (fun r => φ (D r)) = fun r => (ρ r).snd := funext fun r => by simp [φ, hρ]
  rw [hD] at hdl
  refine ⟨dl, hdl, fun y T₀ hT₀ hT₀' W f => ?_⟩
  obtain ⟨N, hN, Ix, U, M, r, hU, hUa, hgen, hrat⟩ := GlobalTheory.Heat.Gens.gens P.D.toPre
  refine GlobalTheory.Heat.DerComm.comm_of_gen A₀.hom P.D.toPre.P.A.hom m₀ _ dl hdl _ T₀ hT₀ hT₀' (Over.w _) Ix U M r hU hUa hgen (fun i j => ?_) W f
  obtain ⟨σ, σ', hσ⟩ := hrat i j
  exact GlobalTheory.T.closedFibreLift_comm_translation_section_ratios E H k m d t P gam hmon hli hab Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀ dl hdl hdesc y T₀ hT₀
    hT₀' N hN σ σ' (U i) (r i j) hσ

end GlobalTheory.HeatTranslW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationHorizontalOfCommutingHeatOperators

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtsHoriz

theorem transl_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ hcl y x hx hx₁
  obtain ⟨_, hA₀, -, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback _ _
    ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) P.D.toPre.P.A _ _ _
    (IsPullback.of_hasPullback P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
  obtain ⟨dl, hdl, hcomm⟩ := GlobalTheory.HeatTranslW.lift_commutes_translation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ _ _ _ hA₀
  have hw : (pullback.fst P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) ≫
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left) ≫ P.D.toPre.P.A.hom =
      pullback.snd _ _ ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [Category.assoc, Over.w, pullback.condition]
  let T₀ := pullback.lift _ _ hw
  exact GlobalTheory.TranslHoriz.isHoriz_of_comm k _ P.D.toPre.P.A P.D.toPre.P.isAb ρ B' _ π₁ π₂ h₁ h₂ hcl _ _ _ hA₀ dl hdl (P.D.toPre.c y) T₀
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (hcomm y T₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) x hx hx₁

end GlobalTheory.PtsHoriz
end
end
