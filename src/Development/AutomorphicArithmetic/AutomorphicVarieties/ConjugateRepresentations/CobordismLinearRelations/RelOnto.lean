module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescFun
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltAddRadial
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BasicDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsLamEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsRapidAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G2Assumption
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsPbSz

section

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.pbSz :
    PbSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hAcd, C2, hC2⟩ := altSz V F q k (1 + c)
  obtain ⟨C1, hC1, hcomp1⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k (1 + c)
  obtain ⟨C3, hC3, hcomp3⟩ := compSz V (V →L[ℝ] V)
    ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  refine ⟨2 ^ k * (C3 * max C2 0) * C1, by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flowSz V k c W t p ht hW hWs
  have hg := hcomp1 w (UpperTheory.V.Lit.Geo.flow W t) p b hF1 hw
    (fun i h1 h2 => hF4 i h1 (by omega)) hws
  have hL : ‖fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    simpa using hF3 0 (Nat.zero_le _)
  have hA : Sz k _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p) (max C2 0) :=
    fun i hi => (hC2 _ hL i hi).trans (le_max_left _ _)
  have hf := hcomp3 _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t)) p (max C2 0) hF2
    hAcd.contDiffAt (fun i h1 h2 => hF3 i h2) hA
  have hprod := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).1 _ _ _ _
    (hAcd.contDiffAt.comp p hF2) (hw.comp p hF1) hf hg
  have e : 2 ^ k * (C3 * max C2 0) * C1 * b = 2 ^ k * (C3 * max C2 0) * (C1 * b) := by ring
  rw [e]
  exact hprod
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecP

section

@[expose] public section

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoRet

section

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.Cs.geoRet :
    GeoRet := by
  intro Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h
  have hB := fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1
  have hA := fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)
  have hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y := fun s => (hB s).1
  have hv := fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp
  have hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p =
      pull (l s) (extDeriv (z.1 s)) p := fun s p hp => by
    rw [G.dOm_apply _ s hp, ← (hB s).2 p hp]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy
  refine ⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_,
    fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]
      rfl
    · rw [((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]
  · rw [hv s p hp]
    exact (hA s q _).1 p hp v i hi
  · rw [hd s p hp]
    exact (hA s (q + 1) _).1 p hp v i hi
  · have hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0 := fun x hx => by
      rw [← G.dOm_apply w s hx, hw]
      rfl
    have hH := homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl
    have hpos := (hl.1 s).2.1 p hp
    have hm := hc _ hpos p hp
    rw [hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]
    unfold pull
    rw [← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSupp

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.supp :
    UpperTheory.V.Lit.Geo.Cs.Supp := by
  intro E _ _ _ a U Ξ f Y C c f₀ hs Φ hΦ q α w R hc hw
  refine ⟨Real.exp (|C| * (1 + |R|)), fun X g hg => ?_⟩
  have hf : R < f g := by
    by_contra hle
    have hle' : f g ≤ R := not_lt.1 hle
    have h1 : |C| * (1 + |R|) < Real.log (qht g) :=
      (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hg)).2 hg
    have h0 := hs.f_nonneg g
    have h2 : C * (1 + f g) ≤ |C| * (1 + |R|) :=
      mul_le_mul (le_abs_self C) (by linarith [le_abs_self R]) (by linarith) (abs_nonneg C)
    linarith [hs.le_f g]
  obtain ⟨y, x, rfl⟩ : ∃ y x, infGL E a y * finGL E a x = g := ⟨_, _, infGL_mul_finGL g⟩
  have hz := hw (x : GL (Fin a) (Af E) ⧸ U) _ (sand_mem_cone y hOne_mem_cone) (by rw [hΦ y x]; exact hf)
  have h := hc y x X
  rw [hz] at h
  have h2 := congrArg (fun z => Ξ.mat y⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] using h2.symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsLocBd

section

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr Filter Topology

theorem UpperTheory.V.Lit.Geo.Cs.locBd :
    LocBd := by
  intro E _ _ a p₀ hp
  obtain ⟨τ, h1, h2⟩ := locSec E a p₀ hp
  have c1 : ContinuousAt (fun p => toL (τ p).val) p₀ := h1.continuousAt
  have c1' : ContinuousAt (fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := c1
  have hi : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (τ p₀).val := by
    apply continuousAt_matrix_inv
    have := NormedRing.inverse_continuousAt (GeneralLinearGroup.det (τ p₀))
    simpa using this
  have c2' : ContinuousAt (fun p => (((τ p)⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := by
    have := ContinuousAt.comp (f := fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) hi c1'
    simpa only [Matrix.coe_units_inv, Function.comp_def] using this
  have c2 : ContinuousAt (fun p => toL ((τ p)⁻¹).val) p₀ := c2'
  refine ⟨max (‖toL (τ p₀).val‖ + 1) (‖toL ((τ p₀)⁻¹).val‖ + 1), ?_⟩
  filter_upwards [h2, c1.norm.eventually_lt_const (lt_add_one _), c2.norm.eventually_lt_const (lt_add_one _)]
    with p e b1 b2
  exact ⟨τ p, ⟨b1.le.trans (le_max_left _ _), b2.le.trans (le_max_right _ _)⟩, e⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Imports

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ImportsVariant

section

@[expose] public section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.g2 :
    G2 :=
  Cs.galois_twist_preserves_siegel_bound Cs.lamEx Cs.descEx Cs.descFun Cs.rapidAll Cs.corrSz Cs.decP Cs.decK Cs.loc Cs.geoSum Cs.geoRet Cs.supp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelOnto

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relOnto :
    UpperTheory.V.Cj.RelOnto := by
  intro hA E _ _ _ a ha σ Ξ Ξ' h hσ q M hM1 hM2 ω ⟨U, uo, uc, hω⟩ dω rω
  obtain ⟨α, a1, a2, a3, a4⟩ := UpperTheory.V.Lit.Geo.g2 E a ha U uo uc Ξ q ω hω dω rω
  obtain ⟨U', -, uo', uc', β, b1, b2, b3⟩ := hA E a ha U uo uc σ Ξ Ξ' h hσ q α a1 a2 a3
  have bL : Lev Ξ' β := ⟨U', uo', uc', b3.2.1⟩
  obtain ⟨β', hβ', hex⟩ := hM2 β bL b1 b2
  obtain ⟨R1, -, -, R4⟩ := UpperTheory.V.Cj.relFacts E a ha σ Ξ Ξ' h hσ q
  obtain ⟨-, -, L, L1, -⟩ := UpperTheory.V.Cj.levSub E a Ξ q
  obtain ⟨-, -, L', L1', -⟩ := UpperTheory.V.Cj.levSub E a Ξ' q
  obtain ⟨B, B1, -⟩ := UpperTheory.V.Cj.exactSub E a Ξ' q
  have dsub : ∀ (Θ : AlgRep E a) (x y : Co Θ q), dCo (smLie Θ) x = 0 → dCo (smLie Θ) y = 0 →
      dCo (smLie Θ) (x - y) = 0 := fun Θ x y hx hy => by
    have e : x - y = (-1 : ℂ) • y + x := by rw [neg_one_smul ℂ y]; abel
    rw [e, dCo_comb, hx, hy, smul_zero, add_zero]
  have hx : Exact Ξ' (β' - β) := (B1 _).1 (by rw [← neg_sub]; exact B.neg_mem ((B1 _).2 hex))
  have r1 : Rel σ h (ω - α) (β' - β) :=
    R4 _ _ ((L1 _).1 (L.sub_mem ((L1 _).2 ⟨U, uo, uc, hω⟩) ((L1 _).2 ⟨U, uo, uc, a1⟩)))
      ((L1' _).1 (L'.sub_mem ((L1' _).2 (hM1 _ hβ').1) ((L1' _).2 bL)))
      (dsub _ _ _ dω a2) (dsub _ _ _ (hM1 _ hβ').2 b1) ⟨U, uo, uc, a4⟩ hx
  have r2 := R1 1 _ _ _ _ r1 ⟨U', uo', uc', b3⟩
  rw [map_one, one_smul, one_smul, sub_add_cancel, sub_add_cancel] at r2
  exact ⟨β', hβ', r2⟩
end
end
