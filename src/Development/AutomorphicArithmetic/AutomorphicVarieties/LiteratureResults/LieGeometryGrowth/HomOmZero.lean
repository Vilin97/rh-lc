module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCorrBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
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

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBd

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.pbBd :
    PbBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, hc⟩ := corrBd E a U Ξ C q
  obtain ⟨B₂, hB₂, hf⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * (2 * B₂) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (GlobalTheory.CuspRep.infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    rw [← hyx, ht, ← hY.left 1 t g, map_one, one_mul]
  obtain ⟨h, hh, h1, h2⟩ := hY.root g 1 (by simp)
  have hbd := hb h (by rw [hh, one_smul])
  have hpt := hflow y h x 1 (by rw [hYg]; exact hh)
  choose v' hv' hv'' using hf y x 1 (by simp)
  have hmem : sand y (hOne E a) ∈ (geo ho U Ξ).Y := sand_mem_cone y hOne_mem_cone
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).1 w _ _ hmem, pb_apply, hpt] at e1
  have e2 : (fun i => fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) 1) (sand y (hOne E a))
      ((2 : ℝ) • sand y (hv (X i)))) = fun i => sand y (v' ((2 : ℝ) • hv (X i))) := by
    funext i
    rw [← hv'', map_smul (sand y)]
  rw [e2] at e1
  have e3 := hc α w.1 hα hw g y h x M hyx h1 h2 hM hbd (fun i => v' ((2 : ℝ) • hv (X i)))
  have e4 : Ξ.mat y⁻¹ * Ξ.mat y = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [e1, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec, ← hyx] at e3
  refine e3.trans ?_
  have e5 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (2 * B₂) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i, (2 * B₂) * ‖hv (X i)‖ := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans (le_of_eq ?_)
          rw [norm_smul, Real.norm_ofNat]
          ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B₁ * M * ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ B₁ * M * ((2 * B₂) ^ q * ∏ i, ‖hv (X i)‖) :=
        mul_le_mul_of_nonneg_left e5 (mul_nonneg hB₁ hM)
    _ = _ := by ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.HomOmZero

section

@[expose] public section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem cone_open (E : Type) [Field E] [NumberField E] (a : ℕ) : IsOpen (cone E a) :=
  isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := UpperTheory.V.Lit.Dr.locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩

private theorem homOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : homOm G W (0 : G.Om (q + 1)) = 0 := by
  have e : (fun s => hom (W s) ((0 : G.Om (q + 1)).1 s)) = fun _ _ => 0 := by
    funext s p
    have : (fun t => hk (W s) t ((0 : G.Om (q + 1)).1 s) p) = fun _ => 0 := by
      funext t
      ext v
      simp [hk_apply]
    rw [hom, this, intervalIntegral.integral_zero]
  rw [homOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem d_step {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (hF : IsFlow G W) (q : ℕ) (w : G.Om q) :
    G.dOm q (pbOm G W w - homOm G W (G.dOm q w)) = G.dOm q w := by
  have hH := omHom _ _ _ _ G W hF
  have e := hH.2.2.2 q (G.dOm q w)
  rw [hH.2.1, homOm_zero, add_zero, sub_eq_iff_eq_add] at e
  rw [map_sub, hH.1, e, add_sub_cancel_left]

private theorem corr_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} {α β : Co Ξ q} {w w' : (geo ho U Ξ).Om q}
    (h : Corr U Ξ α w.1) (h' : Corr U Ξ β w'.1) : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← h g x X, ← h' g x X]
  rfl

theorem UpperTheory.V.Lit.Geo.oneStep :
    OneStep := by
  intro E _ _ _ a U Ξ Y C hY q
  have ho := cone_open E a
  obtain ⟨W, hW⟩ := fieldDef E a U Y C hY
  have hF := (fieldFlow E a ho U Ξ Y C hY W hW).1
  obtain ⟨B₁, hB₁, h₁⟩ := pbBd E a ho U Ξ Y C hY W hW q
  obtain ⟨B₂, hB₂, h₂⟩ := homBd E a ho U Ξ Y C hY W hW q
  refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun η hη => ?_⟩
  obtain ⟨w, hw, hg⟩ := (levGood E a ho U Ξ q).1 η hη
  have hO := omGood _ _ _ _ _ W hF q
  obtain ⟨gP, gD⟩ := hO.1 w hg
  have gH := hO.2.2 _ gD
  obtain ⟨α, cα, lα⟩ := (levGood E a ho U Ξ q).2 _ gP
  obtain ⟨β, cβ, lβ⟩ := (levGood E a ho U Ξ q).2 _ gH
  have cd := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q η w hw
  refine ⟨α - β, (levD E a U Ξ q α lα).2 β lβ, ?_, fun g M M' hM hM' H H' => ?_⟩
  · have c := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q _ _ (corr_sub ho U Ξ cα cβ)
    rw [d_step _ W hF] at c
    exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ (q + 1)).1 _ _ _ c cd
  · refine ((h₁ η α w hη hw cα g M hM H).sub
      (h₂ _ β _ (levD E a U Ξ q η hη).1 cd cβ g M' hM' H')).mono ?_
    nlinarith [mul_nonneg hB₁ hM', mul_nonneg hB₂ hM]
end
end
