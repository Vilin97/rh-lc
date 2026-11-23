module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsIntSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHkSz

section

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHomSz

section

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecK

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
end
end
