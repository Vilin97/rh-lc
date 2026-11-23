module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickeningStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFrames

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FramesBundle

theorem cg_cancel {G : Type} [CommGroup G] (a b c : G) : (a * b) * (a * c)⁻¹ = b * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_cocycle {G : Type} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_gen {G : Type} [CommGroup G] (a g c : G) : a⁻¹ = ((g * c) * a⁻¹ * g⁻¹) * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem frames_bundle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  intro X L hL n D hD τ hτ
  have hg : ∀ i j, ∃ s : Γ(X, D i ⊓ D j)ˣ, ∀ m,
      res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) s =
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) *
          (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j
    refine glue_unit (D i ⊓ D j) (fun m => D i ⊓ D j ⊓ L.U m) (fun m => inf_le_left) ?_ _ ?_
    · intro x hx
      obtain ⟨m, hm⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, ⟨hx, hm⟩⟩
    · intro m m' x hx
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, hτ j x m m' ⟨hx.1.1.2, hx.1.2⟩ ⟨hx.2.1.2, hx.2.2⟩,
        hτ i x m m' ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩, cg_cancel]
  choose g hg' using hg
  have key : ∀ i j m x, x ∈ D i ⊓ D j ⊓ L.U m →
      gm (𝟙 X) x (D i ⊓ D j) (g i j) = gm (𝟙 X) x (D j ⊓ L.U m) (τ j m) * (gm (𝟙 X) x (D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j m x hx
    rw [← gm_res _ x (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) hx, hg' i j m, map_mul, map_inv,
      gm_res _ x _ hx, gm_res _ x _ hx]
  refine ⟨g, ⟨hD, ?_, ?_⟩, ⟨⟨fun p => (τ p.1 p.2)⁻¹⟩, ?_⟩, hg'⟩
  · intro i
    apply unit_ext
    intro x hx
    rw [gm_res _ x _ hx, map_one]
    obtain ⟨m, hm⟩ := exists_chart hL x
    exact (key i i m x ⟨⟨hx, hx⟩, hm⟩).trans (mul_inv_cancel _)
  · intro i j k
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    obtain ⟨m, hm⟩ := exists_chart hL x
    have h1 := key i j m x ⟨⟨hx.1.1, hx.1.2⟩, hm⟩
    have h2 := key j k m x ⟨⟨hx.1.2, hx.2⟩, hm⟩
    have h3 := key i k m x ⟨⟨hx.1.1, hx.2⟩, hm⟩
    exact (congrArg₂ (· * ·) h1 h2).trans ((cg_cocycle _ _ _).trans h3.symm)
  · rintro ⟨i, m⟩ ⟨j, m'⟩
    apply unit_ext
    intro x hx
    have hx' : x ∈ D i ⊓ L.U m ⊓ (D j ⊓ L.U m') := hx
    have eL : ∀ h : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ L.U m,
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h (τ i m)⁻¹) = (gm (𝟙 X) x _ (τ i m))⁻¹ := by
      intro h
      rw [map_inv, map_inv, gm_res _ x _ hx']
    have eR : ∀ (h1 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ D j) (h2 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ L.U m ⊓ L.U m')
        (h3 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D j ⊓ L.U m'),
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h1 (g i j) * (res h2 (L.g m m'))⁻¹ * res h3 (τ j m')⁻¹) =
          gm (𝟙 X) x _ (g i j) * (gm (𝟙 X) x _ (L.g m m'))⁻¹ * (gm (𝟙 X) x _ (τ j m'))⁻¹ := by
      intro h1 h2 h3
      rw [map_mul, map_mul, map_inv, map_inv, map_inv, gm_res _ x _ hx', gm_res _ x _ hx', gm_res _ x _ hx']
    have h1 := key i j m x ⟨⟨hx'.1.1, hx'.2.1⟩, hx'.1.2⟩
    have h2 := hτ j x m m' ⟨hx'.2.1, hx'.1.2⟩ ⟨hx'.2.1, hx'.2.2⟩
    refine (eL _).trans (Eq.trans ?_ (eR _ _ _).symm)
    rw [h1, h2]
    exact cg_gen _ _ _

end GlobalTheory.FramesBundle
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFramesStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.cech_lineBundle_of_compatible_local_frames : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  first | exact @GlobalTheory.FramesBundle.frames_bundle | exact GlobalTheory.FramesBundle.frames_bundle | (intros; apply GlobalTheory.FramesBundle.frames_bundle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullbackStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  first | exact @GlobalTheory.FormalAlg.Charts.tower_preimage_germ | exact GlobalTheory.FormalAlg.Charts.tower_preimage_germ | (intros; apply GlobalTheory.FormalAlg.Charts.tower_preimage_germ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandard

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i
  have hu := fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandardStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | exact GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | (intros; apply GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull <;> assumption)
end
end
