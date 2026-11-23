module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFlatten
public import Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Properties
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

theorem chRing_mem {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {ι : Type} {J : ι → Ω} {d : ι}
    {S : Subring Ω} (ho : ∀ r : o, algebraMap o Ω r ∈ S) (h : ∀ q, J q / J d ∈ S) :
    ∀ a ∈ chRing o J d, a ∈ S := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact h q
  | algebraMap r => exact ho r
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem eq_of_units {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} {p q : Cpt M.ξ} (hp : InChart M.ξ x c p) (hq : InChart M.ξ x c q)
    (h : ∀ u ∈ chRing o x c, unitAt M.ξ p u ↔ unitAt M.ξ q u) : p = q := by
  have hle : ∀ {p q : Cpt M.ξ}, InChart M.ξ x c p → InChart M.ξ x c q →
      (∀ u ∈ chRing o x c, unitAt M.ξ p u → unitAt M.ξ q u) → regAt M.ξ p ≤ regAt M.ξ q := by
    intro p q hp hq h a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp).2 a).1 ha
    exact ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).2 _).2 ⟨u, hu, v, hv, h v hv hvu, rfl⟩
  have h1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p q).1 (hle hp hq fun u hu => (h u hu).1)
  have h2 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M q p).1 (hle hq hp fun u hu => (h u hu).2)
  exact Subtype.ext (h2.antisymm h1).eq

theorem isoAt_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M κ' _ w M' f hd p ⟨l, hl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hJ0 : joinCo (RingHom.id Ω) x w (c, l) ≠ 0 := mul_ne_zero hc.1 hl.1
  have ratio : ∀ j m, joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
      (x j / x c) * (w m / w l) := fun j m => by
    simp only [joinCo, RingHom.id_apply, mul_div_mul_comm]
  have hpJ : ∀ q, joinCo (RingHom.id Ω) x w q / joinCo (RingHom.id Ω) x w (c, l) ∈ regAt M.ξ p := by
    rintro ⟨j, m⟩
    rw [ratio]
    exact mul_mem (hc.2 j) (hl.2 m)
  have hAp := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).1
  have hctr : p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ :=
    ⟨(c, l), hJ0, chRing_mem (fun r => hAp _ (Subalgebra.algebraMap_mem _ r)) hpJ⟩
  obtain ⟨p', ⟨hle', hun'⟩, -, hch'⟩ :=
    PositivityTheory.HtPt.Mb.centre o Ω (κ × κ') (joinCo (RingHom.id Ω) x w) M' M.X Ω M.ξ (RingHom.id Ω) p hctr
  have hle : ∀ a ∈ regAt M'.ξ p', a ∈ regAt M.ξ p := hle'
  have hun : ∀ a ∈ regAt M'.ξ p', unitAt M.ξ p a → unitAt M'.ξ p' a := hun'
  have hp'c : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p' := hch' (c, l) hJ0 hpJ
  have dom := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω M'.ξ (RingHom.id Ω) f hd
  obtain ⟨h, hq1', hq2'⟩ := dom p'
  have hq1 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, a ∈ regAt M'.ξ p' := hq1'
  have hq2 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, unitAt M'.ξ p' a → unitAt M.ξ ⟨f p'.1, h⟩ a := hq2'
  have hx : ∀ j, x j / x c ∈ regAt M'.ξ p' := fun j => by
    have e : joinCo (RingHom.id Ω) x w (j, l) / joinCo (RingHom.id Ω) x w (c, l) = x j / x c := by
      rw [ratio, div_self hl.1, mul_one]
    rw [← e]
    exact hp'c.2 (j, l)
  obtain ⟨c₁, hc₁⟩ := M.tie.cover ⟨f p'.1, h⟩
  have hu : unitAt M.ξ ⟨f p'.1, h⟩ (x c / x c₁) :=
    hq2 _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, hq1 _ (hc₁.2 c), by rw [inv_div]; exact hx c₁⟩
  have hqc : InChart M.ξ x c ⟨f p'.1, h⟩ := ⟨hc.1, fun j => by
    have e : x j / x c = (x j / x c₁) * (x c / x c₁)⁻¹ := by
      have h1 := hc.1
      have h2 := hc₁.1
      field_simp
    rw [e]
    exact mul_mem (hc₁.2 j) hu.2.2⟩
  have hqp : (⟨f p'.1, h⟩ : Cpt M.ξ) = p := by
    refine eq_of_units M hqc hc fun u hu => ?_
    have uq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hqc).1 u hu
    exact ⟨fun k => ⟨k.1, hAp u hu, hle _ (hq1 _ k.2.2)⟩, fun k => hq2 u uq (hun u (hq1 u uq) k)⟩
  have e' : f p'.1 = p.1 := congrArg Subtype.val hqp
  rw [hqp] at hq1
  have hreg : regAt M'.ξ p' = regAt M.ξ p := le_antisymm hle hq1
  have uniq : ∀ p'' : Cpt M'.ξ, f p''.1 = p.1 → p'' = p' := by
    intro p'' e
    obtain ⟨h2, r1', r2'⟩ := dom p''
    have e2 : (⟨f p''.1, h2⟩ : Cpt M.ξ) = p := Subtype.ext e
    rw [e2] at r1' r2'
    have r1 : ∀ a ∈ regAt M.ξ p, a ∈ regAt M'.ξ p'' := r1'
    have r2 : ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p'' a → unitAt M.ξ p a := r2'
    have hch : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p'' := ⟨hJ0, fun q => r1 _ (hpJ q)⟩
    refine eq_of_units M' hch hp'c fun u hu => ?_
    have up' := (PositivityTheory.HtPt.Ma.regat_loc o Ω (κ × κ') _ M' (c, l) p' hp'c).1 u hu
    have up := hle u up'
    exact ⟨fun k => hun u up' (r2 u up k), fun k => ⟨k.1, r1 u up, r1 _ (hle _ k.2.2)⟩⟩
  refine ⟨⟨p', e', fun p'' e => uniq p'' e⟩, fun p'' e => ?_, hd⟩
  rw [uniq p'' e, hreg, Subring.map_id]

end PositivityTheory.HtPt.Mb.LJoinIso.JoinIso


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_iso : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinIso.JoinIso.isoAt_of_chart
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinMany

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {A : Type} [Fintype A] {κa : A → Type} (w : ∀ a, κa a → Ω)

theorem inChart_prod_of_forall (p : Cpt ξ) (h : ∀ a, ∃ l, InChart ξ (w a) l p) :
    ∃ c, InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p := by
  choose c hc using h
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => (hc a).1, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun a _ => (hc a).2 (c' a)

theorem inChart_of_inChart_prod [DecidableEq A] {p : Cpt ξ} {c : ∀ a, κa a}
    (h : InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p) (a : A) : InChart ξ (w a) (c a) p := by
  obtain ⟨h0, h1⟩ := h
  have hne : ∀ b, w b (c b) ≠ 0 := fun b => (Finset.prod_ne_zero_iff.1 h0) b (Finset.mem_univ b)
  refine ⟨hne a, fun l => ?_⟩
  have key : (∏ b, w b (Function.update c a l b)) / (∏ b, w b (c b)) = w a l / w a (c a) := by
    rw [← Finset.prod_div_distrib, Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Function.update_of_ne hb, div_self (hne b)]
  rw [← key]
  exact h1 _

end PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

namespace PositivityTheory.HtPt.Mb.LJoinMany

theorem join_finitely_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M A _ κa _ w hw
  classical
  haveI := Fintype.ofFinite A
  have hW : ∃ l : (∀ a, κa a), (∏ a, w a (l a)) ≠ 0 := by
    choose c hc using hw
    exact ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => hc a⟩
  have hcl : Subfield.closure (Set.range (RingHom.id Ω) ∪
      {z | ∃ l l' : (∀ a, κa a), z = (∏ a, w a (l a)) / ∏ a, w a (l' a)}) = ⊤ :=
    eq_top_iff.2 fun z _ => Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  obtain ⟨M', f, hf⟩ := PositivityTheory.HtPt.Mb.join_exists o Ω κ x M Ω (RingHom.id Ω) (∀ a, κa a)
    (fun c => ∏ a, w a (c a)) (fun _ => rfl) hW hcl
  refine ⟨κ × (∀ a, κa a), inferInstance, _, M', f, hf, ?_, ?_⟩
  · intro a p'
    obtain ⟨-, c, hc⟩ := PositivityTheory.HtPt.Mb.join_charts o Ω κ (∀ a, κa a) x Ω (RingHom.id Ω)
      (fun c => ∏ a, w a (c a)) M' (fun _ => rfl) p'
    exact ⟨c a, JoinMany.inChart_of_inChart_prod _ w hc a⟩
  · intro p hp
    exact PositivityTheory.HtPt.Mb.join_iso o Ω κ x M (∀ a, κa a) (fun c => ∏ a, w a (c a)) M' f hf p
      (JoinMany.inChart_prod_of_forall _ w p hp)

end PositivityTheory.HtPt.Mb.LJoinMany


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinMany.join_finitely_many
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPullEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPullEq

theorem pull_eq_pullLoc_of_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type)
    [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F]
    (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i →
      L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j f hL hd
  have dl := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ X' Ω' ξ' i f hd
  refine ⟨?_, fun p' => ?_⟩
  · funext p'
    obtain ⟨h, hc⟩ := dl p'
    rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j ⟨f p'.1, h⟩ p' hL hc]
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h, e, he, rfl⟩
  · obtain ⟨h, h1, -⟩ := dl p'
    obtain ⟨c, hc⟩ := M.tie.cover ⟨f p'.1, h⟩
    exact ⟨c, hc.1, fun a ha => h1 a (((M.tie.ring c hc.1) a).1 ha _ hc)⟩

end PositivityTheory.HtPt.Mb.LPullEq


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.pull_eq : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i → L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' :=
  @PositivityTheory.HtPt.Mb.LPullEq.pull_eq_pullLoc_of_dominates
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.MbLTopCommon

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LTopCommon

theorem exists_common_normal_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w B _ E _ _ L V _ hw hL hV
  choose κb hκb v hv0 hv1 hv2 using fun b => PositivityTheory.HtPt.Mb.flatten o Ω κ x M (E b) (L b) (V b) (hL b) (hV b)
  let κs : A ⊕ B → Type := fun s => match s with
    | .inl a => κa a
    | .inr b => κb b
  let ws : ∀ s, κs s → Ω := fun s => match s with
    | .inl a => w a
    | .inr b => v b
  haveI : ∀ s, Finite (κs s) := fun s => match s with
    | .inl a => inferInstanceAs (Finite (κa a))
    | .inr b => hκb b
  have hws : ∀ s, ∃ l, ws s l ≠ 0 := fun s => match s with
    | .inl a => hw a
    | .inr b => hv0 b
  obtain ⟨κ₁, _, y₁, M₁, f, hf, hch, hiso⟩ := PositivityTheory.HtPt.Mb.join_many o Ω κ x M (A ⊕ B) κs ws hws
  obtain ⟨κ₂, hκ₂, y₂, M₂, g, hg, hN, -, hnorm⟩ := PositivityTheory.HtPt.Mb.norm_exists o Ω κ₁ y₁ M₁ Ω
  replace hg : Dominates M₂.ξ M₁.ξ g (RingHom.id Ω) := hg
  replace hnorm : ∀ p, NormAt M₂.ξ g (RingHom.id Ω) p := hnorm
  have hgf : Dominates M₂.ξ M.ξ (g ≫ f) (RingHom.id Ω) := by
    unfold Dominates at *
    rw [← Category.assoc, hg, Category.assoc, hf]
    simp
  have hch₂ : ∀ s (p' : Cpt M₂.ξ), ∃ l, InChart M₂.ξ (ws s) l p' := by
    intro s p'
    obtain ⟨h, h1, -⟩ := PositivityTheory.HtPt.Mb.dom_local _ Ω M₁.ξ _ Ω M₂.ξ _ g hg p'
    obtain ⟨l, hl⟩ := hch s ⟨_, h⟩
    exact ⟨l, hl.1, fun c => h1 _ (hl.2 c)⟩
  refine ⟨κ₂, hκ₂, y₂, M₂, g ≫ f, hgf, hN, fun a => hch₂ (.inl a), fun b => ?_, fun p hp hfr => ?_⟩
  · obtain ⟨e, hc⟩ := PositivityTheory.HtPt.Mb.pull_eq o Ω κ x M (E b) (L b) _ Ω M₂.ξ _ (E b) (AddMonoidHom.id _) (g ≫ f) (hL b) hgf
    have key := hv2 b _ Ω M₂.ξ (RingHom.id Ω) (E b) (AddMonoidHom.id _) ⟨fun _ _ => rfl, fun _ _ h => h⟩
    have hu : {p' | p' ∈ ctrSet o x (RingHom.id Ω) M₂.ξ ∧ ∃ l, InChart M₂.ξ (fun l => RingHom.id Ω (v b l)) l p'}
        = Set.univ := Set.eq_univ_of_forall fun p' => ⟨hc p', hch₂ (.inr b) p'⟩
    have hs : Submodule.span Ω (AddMonoidHom.id (E b) '' (V b : Set (E b))) = V b := by simp
    rw [hu, hs] at key
    rw [e]
    exact key
  · refine (PositivityTheory.HtPt.Mb.iso_comp _ Ω M.ξ _ _ Ω (RingHom.id Ω) p).1 M₁.ξ M₂.ξ f g hg (hiso p ?_) fun p₁ _ => hnorm p₁
    rintro (a | b)
    · exact hp a
    · exact hv1 b p (hfr b)

end PositivityTheory.HtPt.Mb.LTopCommon


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.top_common : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LTopCommon.exists_common_normal_model
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  first | exact @PositivityTheory.HtPt.Mb.top_common | exact PositivityTheory.HtPt.Mb.top_common
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinementStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.flag_model_common_refinement : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | exact GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_model_common_refinement <;> assumption)
end
end
