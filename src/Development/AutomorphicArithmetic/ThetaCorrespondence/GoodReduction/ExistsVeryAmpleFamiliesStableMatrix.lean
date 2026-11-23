module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransferStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistedSectionsExtend
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpow

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPow

variable {X Y Z : Scheme.{0}}

theorem pull_pw_g (H : LB X) (g : Z ⟶ X) (n : ℤ) (i j : ((GlobalTheory.AbLaw.pw H n).pull g).ι) :
    ((GlobalTheory.AbLaw.pw H n).pull g).g i j = ((H.pull g).g i j) ^ n := by
  show (∏ k : PUnit, _) = (∏ k : PUnit, _) ^ n
  erw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

theorem div_pull_pw_g (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (n : ℤ)
    (p q : (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).ι) :
    (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).g p q =
      ((LB.div (H.pull g) (M.pull f)).g p q) ^ n := by
  simp only [LB.div, pull_pw_g]
  erw [map_zpow, map_zpow, ← inv_zpow, ← mul_zpow]
  rfl

def isoPow {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g)) (n : ℤ) :
    LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g) where
  s := fun p => (w.s p) ^ n

theorem isoPow_isGen {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g))
    (hw : w.IsGen) (n : ℤ) : (isoPow w n).IsGen := by
  intro p q
  rw [div_pull_pw_g]
  erw [map_zpow, map_zpow]
  erw [hw p q, mul_zpow]
  rfl

theorem exists_isGen_iso_pw : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ,
    ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen :=
  fun _ _ _ _ w _ _ hw n => ⟨isoPow w n, isoPow_isGen w hw n⟩

end GlobalTheory.PullPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpowStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ, ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen := by
  first | exact @GlobalTheory.PullPow.exists_isGen_iso_pw | exact GlobalTheory.PullPow.exists_isGen_iso_pw | (intros; apply GlobalTheory.PullPow.exists_isGen_iso_pw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvrStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_extension_of_genericFiber : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ N : LB (pullback G.hom (spMap (algebraMap W K'))), N.IsLB → ∃ (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), M.IsLB ∧ w.IsGen := by
  first | exact @GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | exact GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | (intros; apply GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianModeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.veryAmple_power_of_extension_genericFibre_abelianModel : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s → M.IsLB → w.IsGen → ∃ n : ℕ, 1 ≤ n ∧ ∃ (m' : ℕ) (t : Fin (m' + 1) → (GlobalTheory.AbLaw.pw M n).Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom (GlobalTheory.AbLaw.pw M n) t := by
  first | exact @GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic | exact GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic | (intros; apply GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsVeryAmpleFamiliesStableMatrix

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C2
open GlobalTheory

theorem appTop_cst' {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add (f := _)])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul' {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add', secPull_smul', ih]

theorem secMaps_sum_smul' {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add (f := _), map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem exists_veryAmple_families_stable_matrix : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (N : ℕ) (H : LB A.left) (s : Fin (N + 1) → H.Sec) (M : LB G.left) (t : Fin (N + 1) → M.Sec) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), H.IsLB ∧ M.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ σ ∈ D, ∃ h : Matrix (Fin (N + 1)) (Fin (N + 1)) W, g.map σ = h.map (algebraMap W K') * g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨H₀, hH₀, m₀, s₀, hs₀⟩ := GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A hA
  obtain ⟨M₀, w₀, hM₀, hw₀⟩ := GlobalTheory.T.exists_lineBundle_extension_of_genericFiber W K' G hG (H₀.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) (pull_isLB hH₀ _)
  obtain ⟨n, hn, m₂, t₀, ht₀⟩ := GlobalTheory.T.veryAmple_power_of_extension_genericFibre_abelianModel K W K' A hA G hG e H₀ m₀ s₀ M₀ w₀ hH₀ hs₀ hM₀ hw₀
  obtain ⟨m₁, s₁, hs₁⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw K A.left A.hom H₀ m₀ s₀ hH₀ hs₀ n hn
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow M₀ H₀ _ _ w₀ hM₀ hH₀ hw₀ n
  have hH := GlobalTheory.AbLaw.isLB_pw hH₀ n
  have hM := GlobalTheory.AbLaw.isLB_pw hM₀ n
  obtain ⟨N, t, ht, htb⟩ := GlobalTheory.T.exists_veryAmple_basis_sections_abelianScheme_over_dvr W G hG _ m₂ t₀ hM ht₀
  obtain ⟨s, g, hs, hg, hgw, huniq⟩ := GlobalTheory.T.abelian_scheme_iso_line_bundle_sections_transfer K W K' A hA G hG e _ m₁ s₁ _ w N t hH hs₁ hM hw htb
  refine ⟨N, _, s, _, t, w, g, hH, hM, hs, ht, hg, hgw, ?_⟩
  intro σ hσ
  have key : ∀ j, ∃ c : Fin (N + 1) → W, ∀ k, σ (g j k) = ∑ l, algebraMap W K' (c l) * g l k := by
    intro j
    obtain ⟨u', hu'⟩ := UpperTheory.Lit.Nos.C1.twisted_sections_extend K W K' D hD1 hD2 A hA G hG e he hφ _ _ w hH hM hw σ hσ (N + 1) s (t j) (g j) (hgw j)
    obtain ⟨c, hc, -⟩ := htb u'
    refine ⟨c, fun k => ?_⟩
    have h2 : Cartier.SecMaps w (Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
      have e2 : ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (c l)) • ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by

        simp only [appTop_cst' (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') pullback.condition, Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
        exact Finset.sum_comm
      rw [e2, hc, secPull_sum_smul']
      exact secMaps_sum_smul' w _ _ _ _ hgw
    have h3 := Cartier.SecMaps.eq (pull_isLB hM _) hu' h2
    exact congrFun (huniq _ _ h3) k
  choose c hc using key
  refine ⟨Matrix.of c, ?_⟩
  ext j k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, hc]

end UpperTheory.Lit.Nos.C2
end
end
end
