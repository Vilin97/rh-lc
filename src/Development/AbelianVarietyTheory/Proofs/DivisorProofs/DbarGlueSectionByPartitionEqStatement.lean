module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Covering.Basic
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

-- Source module: ReciprocityTheory.L2DbarEstimates.NormFibrations.NormFib

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ

theorem normFib : NormFibStatement.{u} := by
  intro n M _ z U hcov himg hfin hconn

  have hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard := by
    intro x
    obtain ⟨hd, W, hxW, hW, hzW, H, hH⟩ := hcov (z x) (himg x)
    have hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x}) :=
      fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩
    filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'
    exact Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  have hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard} := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
      rw [hx']
      exact hx
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx', hx]
  have hall := hS.eq_univ ⟨x0, rfl⟩
  refine ⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩
  rw [(hfin (z x0)).cast_ncard_eq]
  by_cases hy : ∃ x, z x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard := Set.eq_univ_iff_forall.1 hall x
    exact hx.le
  · have h0 : z ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hy ⟨x, h⟩
    rw [h0, Set.encard_empty]
    exact zero_le

end ReciprocityTheory.L2DbarEstimates
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.NormFibrations.NormOrd

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormOrdStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ) (x : M) (m : ℕ),
    IsLocalHomeomorph z → Holo n z f → VanishesBeyond n z f x m →
    Norm.VanishOrder n z f x (m + 1)

theorem normOrd : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy

end ReciprocityTheory.L2DbarEstimates
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

theorem norm (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by
  intro z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan
  have hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall himg
  have hz : IsLocalHomeomorph z := by
    have h := hcov.isLocalHomeomorphOn
    rw [hpre] at h
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h
  obtain ⟨δ, hδ⟩ := normFib.{u} n M z _ hcov himg hfin hconn
  have hΔ0 : Norm.polyAt n Δ 0 ≠ 0 := by
    have h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ := by
      rw [← MvPolynomial.eval_zero]
      rfl
    rw [h0]
    exact hΔ
  funext x
  exact Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr
    (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x

end ReciprocityTheory.L2DbarEstimates
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEq

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEqStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dbar_glueSectionByPartition_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  first | exact @GlobalTheory.glue_wdb_eq | exact GlobalTheory.glue_wdb_eq | (intros; apply GlobalTheory.glue_wdb_eq <;> assumption)
end
end
