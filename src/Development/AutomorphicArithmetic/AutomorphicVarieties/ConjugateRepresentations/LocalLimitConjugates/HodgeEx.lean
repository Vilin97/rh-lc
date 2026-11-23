module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HCobLim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CorrLim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ZigLim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConeConvex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DelLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.KugaSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasB

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H
open scoped ComplexOrder

theorem UpperTheory.V.Cj.H.casB :
    UpperTheory.V.Cj.H.CasB := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨c, hc⟩ := casXi E a n e he Ξ (-r)
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have hell : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), ell E a (toL (star X)) = ell E a (toL X) := fun X => by
    show (∑ w : InfinitePlace E, ∑ i, ((star X) i i w).re) / _ = (∑ w : InfinitePlace E, ∑ i, (X i i w).re) / _
    simp [Matrix.star_apply]
  have hS : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X))ᴴ * G = G * shift Ξ.dmat (-r) (toL (star X)) := fun X => by
    rw [shift_apply, shift_apply, hell, conjTranspose_add, add_mul, mul_add, hadj, conjTranspose_smul,
      conjTranspose_one, star_trivial (_ : ℝ), smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hQ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X) * shift Ξ.dmat (-r) (toL X))ᴴ * G =
        G * (shift Ξ.dmat (-r) (toL (star X)) * shift Ξ.dmat (-r) (toL (star X))) := fun X => by
    rw [conjTranspose_mul, mul_assoc, hS, ← mul_assoc, hS, mul_assoc]
  have h : (cas (shift Ξ.dmat (-r)) e)ᴴ * G = G * cas (shift Ξ.dmat (-r)) e := by
    unfold cas
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : star (e j).1 = (e j).1 := (e j).2
    have h2 : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
      rw [star_smul, h1]; simp
    have h3 : toL (-(Complex.I • (e j).1)) = -toL (Complex.I • (e j).1) := rfl
    rw [conjTranspose_sub, sub_mul, hQ, hQ, h1, h2, h3, map_neg, neg_mul_neg, mul_sub]
  rw [hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasCas
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PerLim

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.perLim :
    UpperTheory.V.Cj.H.PerLim := by
  intro E _ _ _ a U Ξ q ω hω h0 hl
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have key : ∀ k, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (ω k) w.1 ∧ (∀ γ, (geo ho U Ξ).act q γ w = w) ∧
      (geo ho U Ξ).dOm q w = 0 := fun k => by
    have hv : ∀ X, LeftInv (ω k X) ∧ RightInv U (ω k X) := fun X => (levelVal E a U Ξ _).1 ((hω k).val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q (ω k) (hω k).equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ (ω k) w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0 k] at h
    exact ⟨w', hw', fun γ => (corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ,
      (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)⟩
  choose w hw hi hd0 using key
  obtain ⟨c, hz, hlim⟩ := zigLim _ _ _ _ (geo ho U Ξ) hc hn q 0 (fun k _ => w k)
    (fun k => ⟨fun γ _ _ => (hi k γ).symm, fun x hx => by simp [hd, hx, Finset.sum_range_succ]⟩)
    (fun k _ _ => hd0 k) (fun _ _ => corrLim E a ho U Ξ q ω w hw hl)
  exact ⟨c, fun k => ⟨ho, w k, hw k, hz k⟩, fun x hx => hlim x (by omega)⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ExactLim

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.exactLim :
    UpperTheory.V.Cj.H.ExactLim := by
  intro E _ _ _ a ha U hU Ξ q β ω hβ dβ hω dω hl hex
  obtain ⟨c, hc⟩ := (perEx E a U Ξ q).1 β hβ dβ
  obtain ⟨cn, hcn, ht⟩ := perLim E a U Ξ q ω hω dω hl
  refine (perKer E a ha U hU Ξ q β c hβ hc).1
    (hCobLim _ _ _ _ (fun γ s => ⟨_, _, fun f => rfl⟩) q c cn (fun k => ?_) ht)
  have h1 := (perEx E a U Ξ q).2.2 β (ω k) c (cn k) 1 (-1) hc (hcn k)
  have h2 := (levLin E a U Ξ q).1 β (ω k) 1 (-1) hβ (hω k)
  have e1 : (1 : ℂ) • β + (-1 : ℂ) • ω k = β - ω k := by
    ext X
    simp [sub_eq_add_neg]
  have e2 : (1 : ℂ) • c + (-1 : ℂ) • cn k = c - cn k := by
    rw [one_smul, neg_smul, one_smul, sub_eq_add_neg]
  rw [e1] at h1 h2
  rw [e2] at h1
  exact (perKer E a ha U hU Ξ q _ _ h2 h1).2 (hex k)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ResExact

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.resExact :
    UpperTheory.V.Cj.H.ResExact := by
  intro E _ _ _ a ha n e he U Ξ r c hc q ω hω hd
  obtain ⟨k0, k1⟩ := kugaSm E a n e he Ξ r c hc
  cases q with
  | zero => exact ⟨k0 ω hω.equiv hd, fun _ _ => trivial⟩
  | succ q =>
    have hk := k1 q ω hω.equiv hd
    obtain ⟨d1, d2⟩ := delLev E a n e he U Ξ r q ω
    obtain ⟨l1, l2, -⟩ := levLin E a U Ξ q
    have hl := d1 hω
    refine ⟨⟨(-1 : ℂ) • del (smAdj Ξ r) e ω + (0 : ℂ) • del (smAdj Ξ r) e ω, l1 _ _ _ _ hl hl, ?_⟩, fun hs h0 => ?_⟩
    · rw [l2, hk, zero_smul, add_zero]
      exact AlternatingMap.ext fun X => neg_one_smul ℂ _
    · rw [hk, neg_eq_zero] at h0
      exact (sqOrth E a ha n e he Ξ r q).2 ω hs (d2 hs) h0
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HodgeEx

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem co_ext {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {α β : Co Ξ q} (h : ∀ X i, cmp i (α X) = cmp i (β X)) : α = β := by
  refine AlternatingMap.ext fun X => ?_
  rw [← sum_cmp (α X), ← sum_cmp (β X)]
  exact Finset.sum_congr rfl fun i _ => by rw [h X i]

private theorem app_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    (T : Module.End ℂ (Sm E a)) : app T (0 : Co Ξ q) = 0 :=
  AlternatingMap.ext fun X => by
    rw [app_apply, AlternatingMap.zero_apply, map_zero]

private theorem hasLev_of {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : ∀ u ∈ U, act (.fin u) φ = φ) : HasLev φ := by
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun x => k⁻¹ * x) ⁻¹' U, fun x hx => ?_,
    hU.preimage (continuous_const.mul continuous_id), by simp⟩
  have e1 : finRep E a (k⁻¹ * x) φ = φ := h _ hx
  have e2 : finRep E a k φ = φ := hk
  change finRep E a x φ = φ
  have e3 : x = k * (k⁻¹ * x) := by simp
  rw [e3, map_mul, Module.End.mul_apply, e1, e2]

private theorem locLim_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim f φ) : LocLim (fun k => f k - φ) 0 := by
  intro C hC
  have := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at this ⊢
  intro ε hε
  filter_upwards [this ε hε] with k hk x hx
  have e := hk x hx
  change dist (0 : ℂ) ((f k).1 x - φ.1 x) < ε
  rwa [dist_comm, dist_zero_right, ← dist_eq_norm, dist_comm]

theorem UpperTheory.V.Cj.H.hodgeEx :
    UpperTheory.V.Cj.H.HodgeEx := by
  intro E _ _ _ a ha n e he U hUo hUc Ξ r hr q α hα hd hs
  obtain ⟨c, hc⟩ := casB E a n e he Ξ r
  obtain ⟨N, P, Q, S, hN, hR⟩ := fnProj E a ha r n e he c
  obtain ⟨l1, -, l3, l4⟩ := levLin E a U Ξ q
  have l2 := (levLin E a U Ξ q).2.1
  have sub_eq : ∀ {p : ℕ} (x y : Co Ξ p), x - y = (1 : ℂ) • x + (-1 : ℂ) • y := fun x y => by
    refine AlternatingMap.ext fun X => ?_
    change x X - y X = (1 : ℂ) • x X + (-1 : ℂ) • y X
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  have lsub : ∀ x y : Co Ξ q, IsLev U Ξ x → IsLev U Ξ y → IsLev U Ξ (x - y) := fun x y hx hy => by
    rw [sub_eq]; exact l1 x y _ _ hx hy
  have dsub : ∀ x y : Co Ξ q, dCo (smLie Ξ) x = 0 → dCo (smLie Ξ) y = 0 → dCo (smLie Ξ) (x - y) = 0 := fun x y hx hy => by
    rw [sub_eq, l2, hx, hy, smul_zero, smul_zero, add_zero]
  have hV : Val N α := fun X i => by
    obtain ⟨p1, p2, p3⟩ := l3 α hα X i
    obtain ⟨R, hR'⟩ := hs
    refine hN.cpt _ p1 (hasLev_of hUo p2) (p3 r hr) ⟨R, fun g hg => ?_⟩
    rw [Pf.cmp_ev, hR' X g hg]; rfl
  have key : ∀ T, IsOp N T → IsLev U Ξ (app T α) ∧ Val N (app T α) ∧ Val (sqSub E a r) (app T α) ∧
      dCo (smLie Ξ) (app T α) = 0 := fun T hT => by
    obtain ⟨p1, p2, p3, p4⟩ := appFacts E a U Ξ r hr N hN T hT q α hα hV
    exact ⟨p1, p2, p3, by rw [p4, hd, app_zero']⟩
  obtain ⟨h1, h2, h3, h4⟩ := key P hR.opP
  refine ⟨app P α, h1, h4, (resExact E a ha n e he U Ξ r c hc q _ h1 h4).2 h3 (co_ext fun X i => ?_), h3,
    fun X i => hN.grow _ (h2 X i), ?_⟩
  · rw [l4, l4, hR.ker _ (hV X i), AlternatingMap.zero_apply, map_zero]
  · refine exactLim E a ha U hUc Ξ q _ (fun k => app (Q k) α - app P α) (lsub _ _ hα h1) (dsub _ _ hd h4)
      (fun k => lsub _ _ (key _ (hR.opQ k)).1 h1) (fun k => dsub _ _ (key _ (hR.opQ k)).2.2.2 h4) (fun X i => ?_) fun k => ?_
    · have := locLim_sub (hR.lim _ (hV X i))
      simpa only [AlternatingMap.sub_apply, map_sub, l4] using this
    · obtain ⟨s1, -, -, s4⟩ := key _ (hR.opS k)
      have e1 : α - app P α - (app (Q k) α - app P α) = app (casA r c e) (app (S k) α) := by
        rw [sub_sub_sub_cancel_right]
        refine co_ext fun X i => ?_
        rw [AlternatingMap.sub_apply, map_sub, l4, l4, l4, hR.res k _ (hV X i)]
      rw [e1]
      exact (resExact E a ha n e he U Ξ r c hc q _ s1 s4).1
end
end
