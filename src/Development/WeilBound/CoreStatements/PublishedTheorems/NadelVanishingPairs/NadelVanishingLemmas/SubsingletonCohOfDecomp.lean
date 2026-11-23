module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLatticeCohomologyVanish
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescentStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelUniqueInjective
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlasStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TopLogFormsCanonicalGenerator

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.Presents

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ}

def genChart (h : Presents D L r) : L.ι := (exists_chart h.isLB (genericPoint X)).choose

theorem gen_mem_genChart (h : Presents D L r) : genericPoint X ∈ L.U h.genChart :=
  (exists_chart h.isLB (genericPoint X)).choose_spec

def secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(LB.toMod L, U) →+ X.functionField :=
  AddMonoidHom.mk' (fun s => fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField)) fun s t => by
    rw [LB.coord_add, map_add (f := _), add_div]

theorem secVal_apply (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U)) :
    h.secVal U hU s = fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField) := rfl

theorem secVal_mul (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U))
    (i : L.ι) (hi : genericPoint X ∈ U ⊓ L.U i) :
    h.secVal U hU s * r i = fnOf _ hi (LB.coord s i) := by
  have h₀ := h.gen_mem_genChart
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U h.genChart := ⟨hi, h₀⟩
  have e := congrArg (fnOf _ hW) (LB.coord_rel s i h.genChart
    (inf_le_left : U ⊓ L.U i ⊓ L.U h.genChart ≤ U ⊓ L.U i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e
  rw [e, secVal_apply, h.isRatSec i h.genChart (memInf hi.2 h₀), mul_left_comm]
  exact congrArg _ (div_mul_cancel₀ _ (Units.ne_zero _))

theorem secVal_injective (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (h.secVal U hU) := fun s t e =>
  LB.sec_ext fun i => fn_ext fun hi => by rw [← h.secVal_mul U hU s i hi, ← h.secVal_mul U hU t i hi, e]

theorem mem_range_secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (f : X.functionField) :
    f ∈ (h.secVal U hU).range ↔ ∀ y ∈ U, D.RegularAt y f := by
  constructor
  · rintro ⟨s, rfl⟩ y hy
    obtain ⟨i, hi⟩ := exists_chart h.isLB y
    have hyi : y ∈ U ⊓ L.U i := ⟨hy, hi⟩
    refine (h.isEqn i y hi).regularAt_iff.2 ?_
    rw [h.secVal_mul U hU s i (gen_mem hyi)]
    exact regAt_fnOf hyi _ _
  · intro hf
    have key (i : L.ι) : ∃ a : Γ(X, U ⊓ L.U i), ∀ hi, fnOf _ hi a = f * r i := by
      by_cases hi : genericPoint X ∈ U ⊓ L.U i
      · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
          (h.isEqn i x hx.2).regularAt_iff.1 (hf x hx.1)
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h' => (hi h').elim⟩
    choose a ha using key
    have hmem : a ∈ secOn L U := fun i j => fn_ext fun hij => by
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha,
        h.isRatSec i j (memInf hij.1.2 hij.2), mul_left_comm]
    refine ⟨LB.mkSec a hmem, ?_⟩
    rw [secVal_apply, LB.coord_mkSec, ha]
    exact mul_div_cancel_right₀ _ (Units.ne_zero _)

def latModel (h : Presents D L r) :
    LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L) where
  val := h.secVal
  inj := h.secVal_injective
  range U hU := by
    ext f
    rw [h.mem_range_secVal U hU f]
    simp only [latSec, AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, CartierDiv.mem_secOn,
      Set.mem_singleton_iff, forall_eq]
  res U W e hW s := by
    rw [secVal_apply, secVal_apply, LB.coord_map, fnOf_resG]
  smul U hU a s := by
    rw [secVal_apply, secVal_apply, LB.coord_smul, map_mul, fnOf_resG, smul_eq_mul, mul_div_assoc]

end GlobalTheory.Cartier.Presents

theorem GlobalTheory.Cartier.nonempty_latModel_of_presents : ∀ (X : Scheme.{0}) [IsIntegral X] (D : CartierDiv X) (L : LB X)
    (r : L.ι → X.functionFieldˣ), Presents D L r →
    Nonempty (LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L)) :=
  fun _ _ _ _ _ h => ⟨h.latModel⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistDivisorRecursion

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem GlobalTheory.nat_mul_div_bounds_rounded_multiples (p r m : ℕ) (hp : 0 < p) (hr : 0 < r) :
    p * (m / r) ≤ p * m / r ∧ p * m / r + 1 ≤ p * (m / r) + p := by
  have h1 : p * m = p * (m % r) + r * (p * (m / r)) := by
    conv_lhs => rw [← Nat.mod_add_div m r]
    ring
  have h2 : p * m / r = p * (m % r) / r + p * (m / r) := by
    rw [h1, Nat.add_mul_div_left _ _ hr]
  have h4 : p * (m % r) < p * r := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp
  have h3 : p * (m % r) / r < p := (Nat.div_lt_iff_lt_mul hr).2 h4
  rw [h2]
  generalize p * (m % r) / r = q at h3 ⊢
  generalize p * (m / r) = s
  constructor <;> omega

theorem GlobalTheory.rounded_multiples_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  intro X _ p C _ E M Kc r b hp hr e
  have hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c) := fun c => by ring
  refine ⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩
  · intro c
    have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
    show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p
    rw [hm c]
    omega
  · have hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c)
        = (p ^ (e + 1) * b c / r) • E c + E c
          + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      intro c
      have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
      have hk : p * (p ^ e * b c / r) + p
          = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) := by
        rw [hm c]; omega
      rw [smul_add, ← mul_smul, ← add_smul]
      conv_lhs => rw [hk]
      rw [add_smul, add_smul, one_smul]
    have hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)
        = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c
          + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hc c)
    have hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c)
        = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) := by
      rw [pow_succ', mul_smul, smul_sub, smul_sub, smul_add]; abel
    beta_reduce
    rw [hs', hs]
    abel
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusTwistDivisorRecursion

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.frobenius_twist_divisor_recursion : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  first | exact @_root_.GlobalTheory.rounded_multiples_step | exact _root_.GlobalTheory.rounded_multiples_step | (intros; apply _root_.GlobalTheory.rounded_multiples_step <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TopLogFormsCanonicalGeneratorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.top_log_forms_canonical_generator : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  first | exact @_root_.GlobalTheory.LogDR.logAt_top_eq_canonical | exact _root_.GlobalTheory.LogDR.logAt_top_eq_canonical | (intros; apply _root_.GlobalTheory.LogDR.logAt_top_eq_canonical <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SubsingletonCohOfDecomp

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPVanish

theorem gen_mem_inter {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens)
    (h : ∀ i, genericPoint X ∈ U i) (s : Finset ι) : genericPoint X ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.inf_insert]; exact ⟨h i, ih⟩

theorem cechZero_of_forall_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (N : Finset ι → AddSubgroup E) (h : ∀ s, ∀ x ∈ N s, x = 0) (b : ℕ) : DI.CechZero N b := by
  intro c hc _
  refine ⟨0, ⟨rfl, fun s => zero_mem _, fun _ _ => rfl⟩, ?_⟩
  funext t
  simp only [DI.delta, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
  exact (h t _ (hc.2.1 t)).symm

theorem cechFam_eq_zero {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) (s : Finset ι) :
    ∀ x ∈ cechFam 𝒜 G a s, x = 0 := by
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ 𝒜.U i := by
    have : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  have hx' : x ∈ logAt (suppAll E) G a (genericPoint X) :=
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hx (genericPoint X)) (gen_mem_inter _ 𝒜.gen s)
  have hc := ((𝒜.chart i).chart _ hi).coord
  rw [logAt, spanForms_eq_bot_of_lt_card _ n (𝒜.x i) _ _ a hc ha] at hx'
  exact (AddSubgroup.mem_bot).1 hx'

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : X.IsSeparated := by
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver h
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

theorem twist_split {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (M K H : CartierDiv X) (r : ℕ) (b : C → ℕ) (hr : 0 < r) (key : r • (M - K) = ∑ c, b c • E c + H)
    (N : ℕ) :
    N • (M - K) - ∑ c, (N * b c / r) • E c - ∑ c, E c =
      (N / r) • H + ((N % r) • (M - K) - ∑ c, ((N % r) * b c / r) • E c - ∑ c, E c) := by
  conv_lhs => rw [← Nat.div_add_mod N r]
  generalize N / r = Q
  generalize N % r = ρ
  have hfl : ∀ c, (r * Q + ρ) * b c / r = ρ * b c / r + Q * b c := by
    intro c
    rw [show (r * Q + ρ) * b c = ρ * b c + r * (Q * b c) by ring, Nat.add_mul_div_left _ _ hr]
  simp only [hfl, add_smul, Finset.sum_add_distrib]
  rw [show r * Q = Q * r from mul_comm _ _, mul_smul, key]
  simp only [mul_smul, ← Finset.smul_sum, smul_add]
  abel

theorem subsingleton_coh_of_decomp : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → d < p →
    ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} [Fintype ι] [LinearOrder ι]
      (𝒜 : SncAtlas E d ι), Decomp p 𝒜 → ∀ (M H : CartierDiv X) (r : ℕ) (b : C → ℕ),
      IsAmpleLB (toLB H) → 0 < r → (∀ c, b c < r) → r • M = r • canonical f d + ∑ c, b c • E c + H →
      ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (toLB M)) q) := by
  intro p _ X _ f d _ hproj _ C _ E ι _ _ 𝒜 hdec M H r b hH hr hb hM q hq
  haveI : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  haveI : X.IsSeparated := isSeparated_of_isProjOver hproj
  let G : ℕ → CartierDiv X := fun e =>
    p ^ e • (M - canonical f d) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c
  let R : Fin r → CartierDiv X := fun j =>
    (j : ℕ) • (M - canonical f d) - ∑ c, ((j : ℕ) * b c / r) • E c - ∑ c, E c
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.T.serre_vanishing_snc_atlas (ZMod p) X f hproj E 𝒜 H r R hH
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : q₀ * r ≤ p ^ (q₀ * r) := by
    have := Nat.lt_pow_self hp1 (n := q₀ * r)
    omega
  have hQ : q₀ ≤ p ^ (q₀ * r) / r := (Nat.le_div_iff_mul_le hr).2 hpow
  have key : r • (M - canonical f d) = ∑ c, b c • E c + H := by
    rw [smul_sub, hM]; abel
  have hG : G (q₀ * r) = (p ^ (q₀ * r) / r) • H + R ⟨p ^ (q₀ * r) % r, Nat.mod_lt _ hr⟩ :=
    twist_split E M (canonical f d) H r b hr key _
  have hrec : ∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c :=
    GlobalTheory.T.frobenius_twist_divisor_recursion X p E M (canonical f d) r b (by omega) hr
  have hvan : ∀ a b' : ℕ, d < a + b' → DI.CechZero (cechFam 𝒜 (G (q₀ * r)) a) b' := by
    intro a b' hab
    rcases Nat.eq_zero_or_pos b' with rfl | hb'
    · exact cechZero_of_forall_eq_zero _ (cechFam_eq_zero 𝒜 _ (by omega)) 0
    · rw [hG]; exact hq₀ _ hQ _ a b' hb'
  have h0 := GlobalTheory.T.cech_vanishing_frobenius_descent p X E 𝒜 G hdec hrec (q₀ * r) hvan d q (by omega)
  have hG0 : G 0 = M - canonical f d - ∑ c, E c := by
    simp only [G, pow_zero, one_smul, one_mul, Nat.div_eq_of_lt (hb _), zero_smul,
      Finset.sum_const_zero, sub_zero]
  obtain ⟨ω₀, hω₀, htop⟩ := GlobalTheory.T.top_log_forms_canonical_generator p X f d E 𝒜
  let φ : X.functionField →ₗ[X.functionField] abelian₂ X.functionField :=
    LinearMap.toSpanSingleton _ _ ω₀
  have hφ : Function.Injective φ := fun c c' h => smul_left_injective _ hω₀ h
  have hD : canonical f d + ∑ c, E c + G 0 = M := by rw [hG0]; abel
  have hlat : logAt (suppAll E) (G 0) d =
      fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom := by
    funext y; ext η
    rw [htop, AddSubgroup.mem_map, hD]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.2 (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hc), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, CartierDiv.mem_secOn.1 hc y rfl, rfl⟩
  obtain ⟨L0⟩ := nonempty_latModel_of_presents X M (toLB M) _ (presents_toLB M)
  obtain ⟨L1⟩ := (GlobalTheory.T.lattice_model_unique_injective X _ (LB.toMod (toLB M)) (LB.toMod (toLB M)) φ hφ L0).1
  haveI := LB.isQuasicoherent_toMod (presents_toLB M).isLB
  refine (GlobalTheory.T.cech_lattice_cohomology_vanish X _ (LB.toMod (toLB M)) 𝒜.U L1 𝒜.affine 𝒜.gen 𝒜.cover q hq).1 ?_
  have hfam : cechFam 𝒜 (G 0) d = fun s =>
      latSec (fun y => ((M.secOn {y}).toAddSubgroup).map φ.toAddMonoidHom) (inter 𝒜.U s) := by
    funext s; simp only [cechFam, logSec]; rw [hlat]
  rwa [hfam] at h0

end GlobalTheory.CharPVanish
end
end
end
