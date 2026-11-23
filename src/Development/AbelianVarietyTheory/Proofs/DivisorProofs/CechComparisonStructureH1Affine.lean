module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCoverStatement
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpec

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem appLE_ι_appLE_eq_secMap : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  intro X T p U O hO V e r
  have hU : IsAffineOpen U.1 := U.2
  have key : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((p ∣_ U.1) ≫ hU.isoSpec.hom).appLE ⊤ V (by simp) =
      p.appLE U.1 O hO ≫ (p ⁻¹ᵁ U.1).ι.appLE O V e := by
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Scheme.Hom.appTop ((p ∣_ U.1) ≫ hU.isoSpec.hom) ≫
      (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change U.1.topIso.inv ≫ (p ∣_ U.1).appLE ⊤ V (show V ≤ (p ∣_ U.1) ⁻¹ᵁ ⊤ from fun _ _ => trivial) = _
    rw [morphismRestrict_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact (p.map_appLE _ _).trans (p.appLE_map _ _).symm
  exact (congrArg (fun f => f.hom r) key).symm

end GlobalTheory.CechDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpecStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  first | exact @GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | exact GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | (intros; apply GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinear

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

theorem resG_secMap_lin {U V : Z.Opens} (h : V ≤ U) (r : R) :
    resG Z h ((secMap s U).hom r) = (secMap s V).hom r := by
  exact (Sec.res s h).commutes r

theorem resG_sub_sum_lin {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) {N : ℕ} (r : Fin N → R)
    (y : Fin N → Γ(Z, U)) :
    resG Z h (x - ∑ k, (secMap s U).hom (r k) * y k) =
      resG Z h x - ∑ k, (secMap s V).hom (r k) * resG Z h (y k) := by

  rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, resG_secMap_lin]

theorem isCocycle_sub_sum_lin {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {N : ℕ}
    (r : Fin N → R) {e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')} (he : ∀ k, IsCocycle W (e k)) :
    IsCocycle W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') := by
  intro i i' i''
  beta_reduce
  rw [resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]
  simp only [← hc i i' i'', ← he _ i i' i'', mul_add,
    Finset.sum_add_distrib]
  ring

theorem fc_sub_sum_lin (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {N : ℕ}
    (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')) :
    fc s W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') =
      fc s W c - ∑ k, r k • fc s W (e k) := by
  funext V V' a
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  exact resG_sub_sum_lin s _ _ r _

theorem cmp_sub_sum_lin : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  intro R _ Z s J W hW c hc N r e he
  rw [cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]

  simp only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]
  congr 2
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  exact fc_sub_sum_lin s W c r e

end GlobalTheory.CechCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinearStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechClassMap_sub_sum_const_linear : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  first | exact @GlobalTheory.CechCmp.cmp_sub_sum_lin | exact GlobalTheory.CechCmp.cmp_sub_sum_lin | (intros; apply GlobalTheory.CechCmp.cmp_sub_sum_lin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZero

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechCmp

theorem IsCocycle.res_on {Z : Scheme.{0}} {J : Type} {W : J → Z.Opens}
    {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {U : Z.Opens} {i j k : J}
    (hi : U ≤ W i) (hj : U ≤ W j) (hk : U ≤ W k) :
    resG Z (le_inf hi hj) (c i j) + resG Z (le_inf hj hk) (c j k) =
      resG Z (le_inf hi hk) (c i k) := by
  have e := congrArg (resG Z (le_inf (le_inf hi hj) hk)) (hc i j k)
  simp only [map_add (f := _), resG_resG'] at e
  exact e

theorem exists_coboundary_of_cmp_eq_zero (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R)
    (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i))
    (hWb : ∀ i i', IsAffineOpen (W i ⊓ W i')) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hc : IsCocycle W c) (h0 : cmp s W hW c = 0) :
    ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i',
      c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have h1 := restrict_cmp s W hW hc
  rw [h0, map_zero] at h1
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h1.symm
  let g' : ∀ V : Bas W, Γ(Z, V.1.1) := fun V ↦ g (Opposite.op V)
  have key : ∀ (V V' : Bas W) (h : V'.1.1 ≤ V.1.1),
      g' V' - resG Z h (g' V) =
        resG Z (le_inf (h.trans (le_idx V)) (le_idx V')) (c (idx V) (idx V')) := by
    intro V V' h
    exact congrFun (congrFun (congrFun hg (Opposite.op V)) (Opposite.op V'))
      (homOfLE (show V' ≤ V from h)).op
  let Ω : J → Bas W := fun i ↦ ⟨⟨W i, hWa i⟩, i, le_rfl⟩
  have hΩ : ∀ i, W i ≤ W (idx (Ω i)) := fun i ↦ le_idx (Ω i)
  let g₁ : ∀ i, Γ(Z, W i) := fun i ↦ g' (Ω i)
  refine ⟨fun i ↦ resG Z (le_inf le_rfl (hΩ i)) (c i (idx (Ω i))) - g₁ i, fun i i' ↦ ?_⟩
  let Ω₂ : Bas W := ⟨⟨W i ⊓ W i', hWb i i'⟩, i, inf_le_left⟩
  have hd : W i ⊓ W i' ≤ W (idx Ω₂) := le_idx Ω₂
  let g₂ : Γ(Z, W i ⊓ W i') := g' Ω₂
  have k1 : g₂ - resG Z inf_le_left (g₁ i) =
      resG Z (le_inf (inf_le_left.trans (hΩ i)) hd) (c (idx (Ω i)) (idx Ω₂)) :=
    key (Ω i) Ω₂ inf_le_left
  have k2 : g₂ - resG Z inf_le_right (g₁ i') =
      resG Z (le_inf (inf_le_right.trans (hΩ i')) hd) (c (idx (Ω i')) (idx Ω₂)) :=
    key (Ω i') Ω₂ inf_le_right
  have e1 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) (inf_le_left.trans (hΩ i)) hd
  have e2 := hc.res_on (inf_le_right : W i ⊓ W i' ≤ _) (inf_le_right.trans (hΩ i')) hd
  have e3 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right hd
  have e4 : resG Z (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right) (c i i') = c i i' := by
    have : (homOfLE (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right)).op = 𝟙 _ := rfl
    simp only [resG, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e4] at e3
  simp only [map_sub, resG_resG']
  linear_combination e3 - e1 + e2 - k1 + k2

end GlobalTheory.CechCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → ∀ (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → GlobalTheory.CechCmp.cmp s W hW c = 0 → ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | exact GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | (intros; apply GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_tr {A B : Scheme.{0}} (f : A ⟶ B) {O O' : B.Opens} {V V' : A.Opens} (h : O' ≤ O)
    (h' : V' ≤ V) (e : V ≤ f ⁻¹ᵁ O) (e' : V' ≤ f ⁻¹ᵁ O') (x : Γ(B, O)) :
    (f.appLE O' V' e').hom (resG B h x) = resG A h' ((f.appLE O V e).hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem ι_appLE_bijective_of_image {T : Scheme.{0}} (Vo O : T.Opens) (W : Vo.toScheme.Opens)
    (e : W ≤ Vo.ι ⁻¹ᵁ O) (hW : Vo.ι ''ᵁ W = O) : Function.Bijective (Vo.ι.appLE O W e).hom := by
  rw [Scheme.Opens.ι_appLE]
  have k : (homOfLE (Set.image_subset_iff.mpr e) : Vo.ι ''ᵁ W ⟶ O) = eqToHom hW := Subsingleton.elim _ _
  rw [k]
  exact (T.presheaf.mapIso (eqToIso hW).op).commRingCatIsoToRingEquiv.bijective

theorem exists_cech_ho1_cmp : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  intro X T p hp U J W hWa hWcov hWU
  have hsepV : (p ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    haveI : IsAffine U.1 := U.2
    constructor
    rw [← Limits.terminal.comp_from (p ∣_ U.1)]
    infer_instance
  have himg : ∀ O : T.Opens, O ≤ p ⁻¹ᵁ U.1 → (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) = O := by
    intro O hO
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hO
  let W' : J → (p ⁻¹ᵁ U.1).toScheme.Opens := fun i => (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ W i
  have hW' : ⨆ i, W' i = ⊤ := by
    simp only [W', ← Scheme.Hom.preimage_iSup, hWcov, Scheme.Opens.ι_preimage_self]
  have hWa' : ∀ i, IsAffineOpen (W' i) := fun i => by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι, himg _ (hWU i)]
    exact hWa i
  let τ : ∀ i i', Γ(T, W i ⊓ W i') →+* Γ((p ⁻¹ᵁ U.1).toScheme, W' i ⊓ W' i') := fun i i' =>
    ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom
  have hcoc : ∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) →
      IsCocycle W' (fun i i' => τ i i' (c i i')) := by
    intro c hc i i' i''
    have e := congrArg ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)).hom (hc i i' i'')
    rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)] at e
    exact e
  have hb2 : ∀ i i', Function.Bijective (τ i i') := fun i i' =>
    ι_appLE_bijective_of_image _ _ _ _ (himg _ (inf_le_left.trans (hWU i)))
  refine ⟨fun c => cmp ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) W' hW'
    (fun i i' => τ i i' (c i i')), ?_, ?_, ?_, ?_⟩
  · intro c hc N r e he
    have h1 := GlobalTheory.T.cechClassMap_sub_sum_const_linear Γ(X, U.1) _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW'
      (fun i i' => τ i i' (c i i')) (hcoc c hc) N r (fun k i i' => τ i i' (e k i i')) (fun k => hcoc _ (he k))
    refine Eq.trans ?_ h1
    dsimp only
    congr 1
    funext i i'

    simp only [map_sub, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec X T p U (W i ⊓ W i') _ (W' i ⊓ W' i') (fun _ hx => hx) (r k)
  · intro c hc h0
    haveI := hsepV
    obtain ⟨h'', hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero _ _ _ _ W' hW' hWa' (fun i i' => (hWa' i).inf (hWa' i')) _ (hcoc c hc) h0
    choose h hh1 using fun i => (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i) (W' i) le_rfl (himg _ (hWU i))).2 (h'' i)
    refine ⟨h, fun i i' => (hb2 i i').1 ?_⟩
    change ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (c i i') = ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (resG T inf_le_left (h i) - resG T inf_le_right (h i'))
    rw [map_sub, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i) (O' := W i ⊓ W i') (V := W' i) (V' := W' i ⊓ W' i') inf_le_left inf_le_left le_rfl (fun _ hx => hx), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i') (O' := W i ⊓ W i') (V := W' i') (V' := W' i ⊓ W' i') inf_le_right inf_le_right le_rfl (fun _ hx => hx), hh1, hh1]
    exact hh i i'
  · intro x
    haveI := hsepV
    obtain ⟨c', hc', hx⟩ := GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover _ _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW' hWa'
      (fun i i' => (hWa' i).inf (hWa' i')) (fun i i' i'' => ((hWa' i).inf (hWa' i')).inf (hWa' i'')) x
    choose c hc using fun i i' => (hb2 i i').2 (c' i i')
    refine ⟨c, ?_, ?_⟩
    · intro i i' i''
      apply (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)
        (himg _ (inf_le_left.trans (inf_le_left.trans (hWU i))))).1
      rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)]
      have e1 := hc i i'
      have e2 := hc i' i''
      have e3 := hc i i''
      simp only [τ] at e1 e2 e3
      rw [e1, e2, e3]
      exact hc' i i' i''
    · have e : (fun i i' => τ i i' (c i i')) = c' := funext fun i => funext fun i' => hc i i'
      change cmp _ W' hW' (fun i i' => τ i i' (c i i')) = x
      rw [e]
      exact hx
  · intro R' _ σ Y s' ι ι' hι w c hc hcob
    obtain ⟨h', hh'⟩ := hcob
    subst hι
    haveI := hsepV
    refine GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary _ _ _ _ W' hW' hWa' R' σ Y s' ι' w _ (hcoc c hc) ⟨h', fun i i' => ?_⟩
    refine Eq.trans ?_ (hh' i i')
    rw [← Scheme.Hom.appLE_comp_appLE ι' (p ⁻¹ᵁ U.1).ι _ (W' i ⊓ W' i')]
    all_goals rfl
end GlobalTheory.CechCmp
end
end
end
