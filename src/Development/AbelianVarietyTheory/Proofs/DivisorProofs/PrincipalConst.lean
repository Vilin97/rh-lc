module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystemStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  first | exact @GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | exact GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | (intros; apply GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

end Met

end GlobalTheory.CombChern
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerate

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.IdGenRat

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    ∃ r, Presents (l • A) (lbPow (toLB A) l) r := by
  have h := GlobalTheory.CombChern.presents_zpow (presents_toLB A) (l : ℤ)
  rw [natCast_zsmul] at h
  exact ⟨_, h⟩

theorem exists_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  intro X _ _ p hp A z hA
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1
    (GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed X p hp (toLB A) (Closeds.closure {z}) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  obtain ⟨r, κ, -, hz, hy⟩ := hl₁ l hl
  obtain ⟨ρ, hρ⟩ := presents_lbPow_toLB A l
  refine ⟨r, fun i => hρ.rat (κ i), fun i => hρ.rat_mem _, fun i => ?_, fun y hy' => ?_⟩
  · exact (hρ.vanishesAt_rat_iff _).2 (hz i z (subset_closure rfl))
  · have hyZ : y ∉ Closeds.closure ({z} : Set X) := fun h => hy' (specializes_iff_mem_closure.2 h)
    obtain ⟨i, hi⟩ := hy y hyZ
    exact ⟨i, (hρ.generatesAt_rat_iff _).2 hi⟩

end GlobalTheory.IdGenRat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerateStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  first | exact @GlobalTheory.IdGenRat.exists_sections_vanish_generate | exact GlobalTheory.IdGenRat.exists_sections_vanish_generate | (intros; apply GlobalTheory.IdGenRat.exists_sections_vanish_generate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalConst

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.GeneralLift

theorem unitAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0) (x : X) :
    GlobalTheory.Cartier.UnitAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.unitAt_fnOf (U := ⊤) trivial trivial
    (Units.map (algX p ⊤ : ℂ →+* Γ(X, ⊤)).toMonoidHom (Units.mk0 a ha))

theorem regAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (a : ℂ) (x : X) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial (algX p ⊤ a)

theorem principal_const {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0)
    (w : X.functionFieldˣ) (hw : (w : X.functionField) = GlobalTheory.Cartier.constFn p a) :
    GlobalTheory.Cartier.CartierDiv.principal w = 0 :=
  GlobalTheory.Cartier.CartierDiv.ext_of_isEqn fun x =>
    ⟨1, (GlobalTheory.Cartier.CartierDiv.isEqn_principal w x).iff_unitAt.2 (by
      rw [Units.val_one, one_div, hw]; exact (unitAt_constFn p ha x).inv),
      GlobalTheory.Cartier.CartierDiv.isEqn_zero x⟩

end GlobalTheory.GeneralLift


open GlobalTheory.GeneralLift in
theorem GlobalTheory.GeneralLift.exists_lift_klt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (z : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∀ f₀ ∈ (l • A).sections, ∃ u : X.functionField, u ∈ (l • A).sections ∧ (l • A).VanishesAt z u ∧ ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ y, ¬ z ⤳ y → ∀ a t : ℚ, 0 ≤ a → t < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + t • qWeil (GlobalTheory.Cartier.CartierDiv.principal g + l • A) 1) y := by
  intro hP X _ _ _ p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate X p hp A z hA
  refine ⟨l₁, fun l hl f₀ hf₀ => ?_⟩
  obtain ⟨r, κ, hκs, hκv, hκg⟩ := hl₁ l hl
  let s : Option (Fin r) → X.functionField := fun i => Option.elim i f₀ κ
  have hs : ∀ i, s i ∈ (l • A).sections := by
    rintro (_ | i)
    exacts [hf₀, hκs i]
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem hP X p n hp hn Δ D m G (l • A) (Option (Fin r)) s hm hG hD hs
  obtain ⟨v, hv⟩ : ∃ v : Option (Fin r) → ℂ, MvPolynomial.eval v (Q * MvPolynomial.X none) ≠ 0 := by
    by_contra h
    push_neg at h
    exact mul_ne_zero hQ (MvPolynomial.X_ne_zero _) (MvPolynomial.funext fun v => by rw [h v, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hv
  have hv0 : v none ≠ 0 := right_ne_zero_of_mul hv
  have hvQ : MvPolynomial.eval v Q ≠ 0 := left_ne_zero_of_mul hv
  refine ⟨∑ i : Fin r, GlobalTheory.Cartier.constFn p (v (some i) / v none) * κ i, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    exact GlobalTheory.Cartier.CartierDiv.mem_sections.2 fun x =>
      (GlobalTheory.Cartier.CartierDiv.mem_sections.1 (hκs i) x).regAt_mul (regAt_constFn p _ x)
  · refine Finset.sum_induction _ (fun f => (l • A).VanishesAt z f)
      (fun _ _ h h' => h.add h') ((l • A).vanishesAt_zero z) fun i _ => ?_
    obtain ⟨g, hg, hz⟩ := hκv i
    exact ⟨g, hg, by convert hz.mul (regAt_constFn p (v (some i) / v none) z) using 1; ring⟩
  · intro g hg y hy a t ha ht hk
    have hc : GlobalTheory.Cartier.constFn p (v none) ≠ 0 := (map_ne_zero _).2 hv0
    have key := hQe v hvQ (Units.mk0 _ hc * g) (by
      rw [Units.val_mul, Units.val_mk0, hg, Fintype.sum_option, mul_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hv0]
      rfl) y (have ⟨i, hi⟩ := hκg y hy; ⟨some i, hi⟩) a t ha ht hk
    rwa [GlobalTheory.Cartier.CartierDiv.principal_mul, principal_const p hv0 _ (Units.val_mk0 hc),
      zero_add] at key
end
end
