module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HTIntLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichESymmApply
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichESymmApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.WeightPositive
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalTheoryWindows

section

@[expose] public section

attribute [local instance] Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult :
    ∀ (D : Formalism.BasicNotions.D7)
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (v : (Formalism.MainNotions.S.VS D).V),
        ∃ (n : ℤ),
          n ≠ (0 : ℤ) ∧
            (↑n : D.host.E) • v ∈
              Λ := by
  intro D Λ h v
  obtain ⟨⟨t, ht⟩, hv⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v
    (h.span_eq_top ▸ Submodule.mem_top)
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht
  refine ⟨n, hn, ?_⟩
  have hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t := by rw [mul_comm]; simpa using hc
  have e : (n : D.host.E) • v = c • t • v := by
    rw [smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]
  rw [Submodule.span_eq] at hv
  exact e ▸ Λ.smul_mem c hv
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CommonMult

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gen_red {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (hP : P.FG) (N : ℤ) (hN : N ≠ 0) :
    ∃ Rs : Set M, Rs.Finite ∧ ∀ x ∈ P, ∃ q ∈ P, ∃ ρ ∈ Rs, x = N • q + ρ := by
  obtain ⟨s, hs⟩ := hP
  refine ⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩
  intro x hx
  rw [← hs] at hx
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  refine ⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩
  · rw [← hs]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)
  · refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (f g) hN
      have h2 := Int.emod_lt (f g) hN
      omega
    · rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]
  · rw [← hf, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem int_mult (D : Formalism.BasicNotions.D7) (s : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k ∈ s, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨n, hn, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  exact ⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩

theorem lat_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (v : (VS D).V) : ∃ n : ℤ, n ≠ 0 ∧ (n : D.host.E) • v ∈ Λ := by
  exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D hΛ v

theorem common_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (vs : Finset (VS D).V) (ks : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ (∀ v ∈ vs, (n : D.host.E) • v ∈ Λ) ∧
      ∀ k ∈ ks, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ := by
    induction vs using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert v vs hv ih =>
      obtain ⟨n, hn, h⟩ := ih
      obtain ⟨m, hm, hmv⟩ := lat_mult D hΛ v
      refine ⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · have : ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul, mul_comm]
        rw [this]; exact smul_int_mem D ⟨n, by simp⟩ hmv
      · have : ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul]
        rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)
  obtain ⟨n, hn, h1⟩ := hv
  obtain ⟨m, hm, h2⟩ := int_mult D ks
  refine ⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩
  · have : ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v) := by
      rw [smul_smul, Int.cast_mul, mul_comm]
    rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)
  · obtain ⟨o, ho⟩ := h2 k hk
    refine ⟨(n : 𝓞 D.host.E) * o, ?_⟩
    rw [map_mul, ho, map_intCast]; push_cast; ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Stage1OfUnipotentIntegralIsGroup

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem stage1_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hL


theorem inW_neg (D : Formalism.BasicNotions.D7) {x : (VS D).V} (hx : InW D x) : InW D (-x) := by
  simpa using inW_smul D (-1) hx

theorem stage1_of_unipotentIntegralIsGroup (hN : UnipotentIntegralIsGroup) : Stage1 := by
  intro D T T' F0 Λ hF Z R hR
  have hF' := hF
  obtain ⟨hlat, hU, he, heΛ0, c0, hc0, hz⟩ := hF
  have heΛ : ∀ a, D.sp.hypE a ∈ Λ := fun a => by rw [← he]; exact heΛ0 a
  let : Submodule.IsLattice D.host.E Λ := hlat
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    ⟨stage1_span_eq_top_of_unimodular D hlat.fg hU⟩
  obtain ⟨d, hd0, hdv, hdk⟩ := common_mult D hfull
    (Finset.univ.image D.sp.hypF ∪ {((D.sp.T : D.host.E)⁻¹) • D.sp.zm})
    (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) ∪
      Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2))
  have hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ := fun a =>
    hdv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ := by
    rw [← smul_smul]; exact hdv _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hdR : ∀ b a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * R b a := fun b a =>
    hdk _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2)
      (Finset.mem_univ (b, a))))
  have hdP : ∀ b' b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * Pm D Z R b' b :=
    fun b' b => hdk _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2) (Finset.mem_univ (b', b))))
  have hd2 : ∀ v ∈ Λ, (d : D.host.E) ^ 2 • pW D v ∈ Λ := fun v hv => pW_lat D hU heΛ d hdF hdz hv
  have hdE : (d : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hd0
  have hd3 : (d : D.host.E) ^ 3 ≠ 0 := pow_ne_zero 3 hdE
  have hΛfg : (Λ.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hlat.fg

  let Sb : Fin (D.R.rS + 1) → Set (VS D).V := fun b =>
    {w | w ∈ Λ.restrictScalars ℤ ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = (d : D.host.E) ^ 6 * kap D T' Z R c0 b}
  have hSb : ∀ b, (Sb b).Finite := fun b => definite_finite D _ hΛfg _
  let Tset : Fin (D.R.rS + 1) → Set (VS D).V := fun b => (fun w => (((d : D.host.E) ^ 3)⁻¹) • w) '' Sb b

  have hLWfg : ((LamW D Λ).restrictScalars ℤ).FG := Submodule.FG.of_le hΛfg (fun y hy => hy.1)
  obtain ⟨Rs, hRs, hred⟩ := gen_red _ hLWfg (2 * d ^ 3) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hd0))
  refine ⟨(fun p : (Fin (D.R.rS + 1) → (VS D).V) × (Fin D.R.rS → (VS D).V) =>
      fun b => p.1 b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • p.2 a) ''
      (Set.pi Set.univ Tset ×ˢ Set.pi Set.univ (fun _ => Rs)), ?_, ?_⟩
  · exact ((Set.Finite.pi (fun b => (hSb b).image _)).prod (Set.Finite.pi (fun _ => hRs))).image _
  intro x hx
  have hbeta : ∀ (a : Fin D.R.rS) b, (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro a b
    have := hx.2.1 (Fin.castSucc a) b
    simpa [brS, FlagG.fvec, he, betaZ] using this

  have hw2 : ∀ b, (d : D.host.E) ^ 2 • pWf D x b ∈ LamW D Λ := fun b =>
    ⟨hd2 _ (hx.1 b), inW_smul D _ (inW_pW D _)⟩
  have hu : ∀ a, (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) ∈ (LamW D Λ).restrictScalars ℤ := by
    intro a
    have : (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) =
        ∑ b, ((d : D.host.E) * R b a) • ((d : D.host.E) ^ 2 • pWf D x b) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_smul, smul_smul]; ring_nf
    rw [Submodule.restrictScalars_mem, this]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ := hdR b a
    rw [← ho, algebraMap_smul]
    exact (LamW D Λ).smul_mem o (hw2 b)
  choose q hq ρ hρ hqρ using fun a => hred _ (hu a)
  obtain ⟨n, hn, hpW⟩ := eich_all hN D F0 Λ hF' (fun a => -q a) (fun a => inW_neg D (hq a).2)
    (fun a => Λ.neg_mem (hq a).1)
  refine ⟨n, hn, ⟨(tv D Z R x, ρ), ⟨fun b _ => ?_, fun a _ => hρ a⟩, ?_⟩⟩
  ·
    refine ⟨(d : D.host.E) ^ 3 • tv D Z R x b, ⟨?_, ?_, ?_, ?_, ?_⟩, inv_smul_smul₀ hd3 _⟩
    · rw [Submodule.restrictScalars_mem]
      have : (d : D.host.E) ^ 3 • tv D Z R x b =
          ∑ b', ((d : D.host.E) * Pm D Z R b' b) • ((d : D.host.E) ^ 2 • pWf D x b') := by
        rw [tv, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ => by rw [smul_smul, smul_smul]; ring_nf
      rw [this]
      refine Submodule.sum_mem _ fun b' _ => smul_int_mem D (hdP b' b) (hw2 b').1
    all_goals have hW : InW D ((d : D.host.E) ^ 3 • tv D Z R x b) :=
      inW_smul D _ (inW_sum D _ _ fun b' => inW_smul D _ (inW_pW D _))
    · exact hW.1
    · exact hW.2.1
    · exact hW.2.2
    · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
        star_pow, star_intCast]
      rw [tv_norm D T' F0 Λ Z R hR he hc0 hz hx b]
      ring
  ·
    funext b
    have h2q : ∀ a, (2 : D.host.E) • q a = (∑ b', R b' a • pWf D x b') - (((d : D.host.E) ^ 3)⁻¹) • ρ a := by
      intro a
      have e1 := hqρ a
      rw [← Int.cast_smul_eq_zsmul D.host.E] at e1
      have e2 : ((2 * d ^ 3 : ℤ) : D.host.E) • q a = (d : D.host.E) ^ 3 • (∑ b', R b' a • pWf D x b') - ρ a := by
        rw [e1]; abel
      have e3 : (2 : D.host.E) • q a = (((d : D.host.E) ^ 3)⁻¹) • (((2 * d ^ 3 : ℤ) : D.host.E) • q a) := by
        rw [smul_smul]; congr 1; push_cast; field_simp
      rw [e3, e2, smul_sub, inv_smul_smul₀ hd3]
    symm
    show pW D (fr D (act D n x) b) = tv D Z R x b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • ρ a
    rw [fr_act, hpW]
    have e4 : ∀ a, (VS D).hT (D.sp.hypE a) (fr D x b) • ((2 : D.host.E) • -q a) =
        -(betaZ D Z a b • (∑ b', R b' a • pWf D x b')) + (((d : D.host.E) ^ 3)⁻¹) • (betaZ D Z a b • ρ a) := by
      intro a
      rw [hbeta, smul_neg, h2q, smul_neg, smul_sub, smul_comm (betaZ D Z a b) (((d : D.host.E) ^ 3)⁻¹) (ρ a)]
      abel
    rw [Finset.sum_congr rfl fun a _ => e4 a, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [tv, Pm, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_smul,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a b' => (betaZ D Z a b * R b' a) • pWf D x b')]
    have e5 : ∀ b' a, (betaZ D Z a b * R b' a) • pWf D x b' = (R b' a * betaZ D Z a b) • pWf D x b' :=
      fun b' a => by rw [mul_comm]
    simp only [e5]
    show pW D (fr D x b) + _ = _
    have e6 : pWf D x b = pW D (fr D x b) := rfl
    rw [← e6]
    abel

end PI.UnitaryGroupMassFormula.CntFormula
end
end
end
