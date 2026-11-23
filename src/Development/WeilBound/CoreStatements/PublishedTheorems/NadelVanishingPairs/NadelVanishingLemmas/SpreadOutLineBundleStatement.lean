module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBaseChangeSections

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SecFlatBC

theorem pullLE_ofSec {X X' : Scheme.{0}} {L : LB X} (τ : L.Sec) (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens)
    (e : V' ≤ π ⁻¹ᵁ V) :
    AbLaw.SecOn.pullLE L π V V' e (LB.ofSec τ V) = LB.ofSec (Cartier.secPull τ π) V' := by
  refine LB.sec_ext fun j => ?_
  rw [AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]
  simp only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sum_smul_f {X' : Scheme.{0}} {R' : Type} [CommRing R'] (f' : X' ⟶ Sp R') {M : LB X'} {n : ℕ}
    (c : Fin n → R') (τ : Fin n → M.Sec) (i : M.ι) :
    (∑ a, AbLaw.cst f' ⊤ (c a) • τ a).f i = ∑ a, cstOn f' _ (c a) * (τ a).f i := by
  let F : M.Sec →+ Γ(X', M.U i) := ⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩
  change F _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _
  rw [show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]
  rfl

theorem exists_sum_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  intro R R' _ _ φ X X' f f' π _ _ L hφ H hL σ
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  have H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := H
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := GlobalTheory.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) :=
    GlobalTheory.isAffineOpen_finset_biInf hD
  have hc' := AbLaw.PerfOfModel.iSup_preimage π hc
  let E := AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'
  let E₀ := AbLaw.CechOne.secKerEquiv L f hc
  let d := ((AbLaw.cechLB f L D).d 0 1).hom
  obtain ⟨x, hx, hxy⟩ := (AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2
  have hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R') :=
    Module.Flat.ker_lTensor_eq (R := R) R' R' d
  rw [hker] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let e := S.equivFin
  refine ⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩

  have key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π := by
    apply E.injective
    apply Subtype.ext

    rw [← hxy, map_sum, map_sum, map_sum, Submodule.coe_sum,
    ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]
    funext s
    have hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s =
        AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i)) := by
      rw [← AbLaw.CechOne.secKerEquiv_val L f hc]
      exact congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm
    change (e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) =
      (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s
    rw [hk, AbLaw.CechOne.secKerEquiv_val]
    change _ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _
    rw [AbLaw.SecOnR.pull_of, pullLE_ofSec]
    rfl
  intro i
  rw [key, sum_smul_f]

end GlobalTheory.SecFlatBC
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FlatBaseChangeSections

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.flat_base_change_sections : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  first | exact @_root_.GlobalTheory.SecFlatBC.exists_sum_secPull | exact _root_.GlobalTheory.SecFlatBC.exists_sum_secPull | (intros; apply _root_.GlobalTheory.SecFlatBC.exists_sum_secPull <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundle

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem subring_subtype_flat {k : Type} [Field k] (R : Subring k) : R.subtype.Flat := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 R.subtype_injective
  let _ := FractionRing.liftAlgebra R k
  have := FractionRing.isScalarTower_liftAlgebra R k
  have h1 : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  have h2 : Module.Flat R k := Module.Flat.trans R (FractionRing R) k
  exact (RingHom.flat_algebraMap_iff (R := R) (S := k)).2 h2

theorem resG_cstOn_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (c : R) : resG X h (cstOn p U c) = cstOn p V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫
    X.presheaf.map (homOfLE h).op).hom c = _
  erw [Scheme.Hom.appLE_map]
  rfl

theorem app_cstOn_const {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (j : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ j ⁻¹ᵁ U) (c : R) :
    resG Y h ((j.app U).hom (cstOn p U c)) = cstOn (j ≫ p) V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫ j.appLE U V h).hom c = _
  exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom c)
    (Scheme.Hom.appLE_comp_appLE j p ⊤ U V le_top h)

theorem cstOn_comp_spMap_const {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (p : X ⟶ Sp R') (U : X.Opens) (c : R) : cstOn (p ≫ spMap φ) U c = cstOn p U (φ c) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ spMap φ).appLE ⊤ U le_top =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p.appLE ⊤ U le_top := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    erw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun g => g.hom c) e

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {n : ℕ}
    (c : Fin n → R) (τ : Fin n → L.Sec) : L.Sec where
  f i := ∑ a, cstOn p _ (c a) * (τ a).f i
  compat i j := by
    change resG X _ _ = _ * resG X _ _

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_mul, resG_cstOn_const, resG_cstOn_const, mul_left_comm]
    exact congrArg _ ((τ a).compat i j)

theorem resG_comb_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X X₁ X₀ : Scheme.{0}}
    (f : X ⟶ Sp R') (f₁ : X₁ ⟶ Sp R) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁) (hf : j ≫ f₁ = f ≫ spMap φ)
    {n : ℕ} (c : Fin n → R) {U₀ : X₀.Opens} (t : Fin n → Γ(X₀, U₀)) {U₁ : X₁.Opens} {V V' W : X.Opens}
    (h₁ : U₁ ≤ π₁ ⁻¹ᵁ U₀) (hV : V ≤ j ⁻¹ᵁ U₁) (hV' : V' ≤ (j ≫ π₁) ⁻¹ᵁ U₀) (hW' : W ≤ V') (hW : W ≤ V) :
    resG X hW' (∑ a, cstOn f V' (φ (c a)) * resG X hV' (((j ≫ π₁).app U₀).hom (t a))) =
      resG X hW (resG X hV ((j.app U₁).hom
        (∑ a, cstOn f₁ U₁ (c a) * resG X₁ h₁ ((π₁.app U₀).hom (t a))))) := by

  rw [Cartier.resG_resG, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, app_cstOn_const, resG_cstOn_const, hf, cstOn_comp_spMap_const,
    Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG]
  rfl

theorem exists_finset_sec_descends : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  classical
  intro k _ R₀ X X₀ f f₀ π _ L σ hπ hL
  obtain ⟨n, c, τ, hσ⟩ := GlobalTheory.T.flat_base_change_sections R₀ k R₀.subtype X₀ X f₀ f π L (subring_subtype_flat R₀) hπ hL σ
  refine ⟨Finset.univ.image c, fun R₁ hR hF X₁ f₁ π₁ j _ hj hf => ?_⟩
  subst hj
  let c₁ : Fin n → R₁ := fun a => ⟨c a, hF (by simp)⟩
  refine ⟨secComb f₁ c₁ fun a => Cartier.secPull (τ a) π₁, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((j ≫ π₁) x)))
  have h1 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ (L.pull (j ≫ π₁)).U fun _ => i := (Cartier.pull_U L _ fun _ => i).ge
  have h2 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ ((L.pull π₁).pull j).U fun _ _ => i :=
    (j.preimage_mono (Cartier.pull_U L π₁ fun _ => i).ge).trans
      (Cartier.pull_U (L.pull π₁) j fun _ _ => i).ge
  refine ⟨(j ≫ π₁) ⁻¹ᵁ L.U i, fun _ => i, fun _ _ => i, h1, h2, 1, hi, ?_⟩
  refine Eq.trans ?_ (one_mul _).symm
  refine (congrArg (resG X h1) (hσ fun _ => i)).trans ?_
  exact resG_comb_pull R₁.subtype f f₁ π₁ j hf c₁ (fun a => (τ a).f i)
    (Cartier.pull_U L π₁ fun _ => i).le (Cartier.pull_U (L.pull π₁) j fun _ _ => i).le
    (Cartier.pull_U L (j ≫ π₁) fun _ => i).le h1 h2

end GlobalTheory.LogPair
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_finset_sec_descends | exact _root_.GlobalTheory.LogPair.exists_finset_sec_descends | (intros; apply _root_.GlobalTheory.LogPair.exists_finset_sec_descends <;> assumption)
end
end
