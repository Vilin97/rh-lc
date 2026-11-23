module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot

section

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CxPts

namespace GlobalTheory.Mean4O.ReadsProj

section Local

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ)

def HalfWeight (L : HermLB p) (g : CxPts p σ → CxPts p σ → ℝ) : Prop :=
  ∀ x, ∃ i, x ∈ ptsIn p σ (L.B.U i) ∧ ∀ z, (L.φ σ).φ i z / 2 = g x z

variable {σ} {L L' : HermLB p} {g g' : CxPts p σ → CxPts p σ → ℝ}

theorem HalfWeight.congr (h : HalfWeight σ L g) (e : ∀ x z, g x z = g' x z) : HalfWeight σ L g' := by
  rwa [← show g = g' from funext₂ e]

theorem halfWeight_locPot (L : HermLB p) : HalfWeight σ L (L.φ σ).locPot.φ :=
  fun x => ⟨_, (L.φ σ).locPot.mem_U x, fun _ => rfl⟩

theorem halfWeight_triv : HalfWeight σ (HermLB.triv p) fun _ _ => 0 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => zero_div _⟩

theorem HalfWeight.tens (h : HalfWeight σ L g) (h' : HalfWeight σ L' g') :
    HalfWeight σ (L.tens L') fun x z => g x z + g' x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  obtain ⟨j, hj, e'⟩ := h' x
  exact ⟨(i, j), mem_ptsIn_inf.2 ⟨hi, hj⟩, fun z => (add_div _ _ _).trans (congrArg₂ (· + ·) (e z) (e' z))⟩

theorem HalfWeight.dual (h : HalfWeight σ L g) : HalfWeight σ L.dual fun x z => -g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  exact ⟨i, hi, fun z => (neg_div _ _).trans (congrArg (-·) (e z))⟩

theorem HalfWeight.pow (h : HalfWeight σ L g) (m : ℕ) : HalfWeight σ (L.pow m) fun x z => m * g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  refine ⟨fun _ => i, CxPts.mem_pow_iff.2 hi, fun z => ?_⟩
  refine (congrArg (· / 2) ((L.φ σ).zpow_φ m _ z)).trans ?_
  simp only [← e z, mul_div_assoc, Int.cast_natCast]

theorem HalfWeight.zp (h : HalfWeight σ L g) (n : ℤ) : HalfWeight σ (zp L n) fun x z => n * g x z :=
  ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun x z => by
    have e : ((n.toNat : ℤ) : ℝ) - ((-n).toNat : ℤ) = n := by exact_mod_cast Int.toNat_sub_toNat_neg n
    rw [← e]
    simp only [Int.cast_natCast]
    ring

theorem halfWeight_comb {ι : Type} [Fintype ι] {L : ι → HermLB p} {g : ι → CxPts p σ → CxPts p σ → ℝ}
    (h : ∀ i, HalfWeight σ (L i) (g i)) (n : ι → ℤ) :
    HalfWeight σ (ArInt.comb L n) fun x z => ∑ i, n i * g i x z := by
  have key (l : List ι) : HalfWeight σ (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p))
      fun x z => (l.map fun i => n i * g i x z).sum := by
    induction l with
    | nil => exact halfWeight_triv
    | cons i l ih => exact ((h i).zp (n i)).tens ih
  exact (key _).congr fun x z => Finset.sum_map_toList _ _

end Local

open ProjSpace

variable (N : ℕ)

end GlobalTheory.Mean4O.ReadsProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open scoped ContDiff

namespace GlobalTheory.Mean4O.ReadsProj

theorem hess_comb : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (σ : k →+* ℂ) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}, y ∈ c.e.source → ∀ (i : (ArInt.comb L n).B.ι), y ∈ ptsIn p σ ((ArInt.comb L n).B.U i) → ∀ (m : ∀ l, (L l).B.ι), (∀ l, y ∈ ptsIn p σ ((L l).B.U (m l))) → c.hess ((ArInt.comb L n).φ σ) i y = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y := by
  classical
  intro k _ X p ι _ L n σ D c y hy i hi m hm
  obtain ⟨i₀, hi₀, e₀⟩ := halfWeight_comb (fun l => halfWeight_locPot (σ := σ) (L l)) n y
  choose j hj ej using fun l => halfWeight_locPot (σ := σ) (L l) y
  set F : ι → ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun l v => ((L l).φ σ).φ (j l) (c.e.symm v) with hF
  have e : ∀ z, ((ArInt.comb L n).φ σ).φ i₀ z = ∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z := by
    intro z
    have h := e₀ z
    simp only [← ej] at h
    have h2 : ∑ l, (n l : ℝ) * (((L l).φ σ).φ (j l) z / 2) =
        (∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  set Ω := c.e.target ∩ c.e.symm ⁻¹' ⋂ l, ptsIn p σ ((L l).B.U (j l)) with hΩdef
  have hΩ : IsOpen Ω := ChartGlue.isOpen_over c.e (isOpen_iInter_of_finite fun l => isOpen_ptsIn _)
  have hmem : c.e y ∈ Ω := ChartGlue.mem_over c.e hy (Set.mem_iInter.2 hj)
  have hs : ∀ l, ContDiffOn ℝ ∞ (F l) Ω := fun l =>
    (contDiffOn_chart ((L l).cInf σ (j l)) c).mono fun v hv => ⟨hv.1, Set.mem_iInter.1 hv.2 l⟩
  have key : ∀ s : Finset ι,
      ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l ∈ s, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) =
        ∑ l ∈ s, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ (p := fun _ => (0 : ℝ))
        (q := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const 1 hmem
      simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h0
      simp only [Finset.sum_empty]
      exact left_eq_add.1 h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ
        (p := fun w => ∑ l ∈ s, (n l : ℝ) * F l w) (q := F a)
        (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hs l)) (hs a) (n a) hmem
      have h3 : (fun v => ((∑ l ∈ insert a s, (n l : ℝ) * F l v : ℝ) : ℂ)) =
          fun v => ((∑ l ∈ s, (n l : ℝ) * F l v + (n a : ℝ) * F a v : ℝ) : ℂ) := by
        funext v
        rw [Finset.sum_insert ha, add_comm]
      rw [h3, h1, ih, add_comm]
  calc c.hess ((ArInt.comb L n).φ σ) i y = c.hess ((ArInt.comb L n).φ σ) i₀ y :=
        c.hess_eq ((ArInt.comb L n).cInf σ) hy hi₀ hi
    _ = ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) := by
        simp only [AlgChart.hess, e, hF]
    _ = ∑ l, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := key _
    _ = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y :=
        Finset.sum_congr rfl fun l _ => by
          rw [← c.hess_eq ((L l).cInf σ) hy (hm l) (hj l)]
          rfl

end GlobalTheory.Mean4O.ReadsProj
end
end
