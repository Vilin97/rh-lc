module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.InfinityCoordAlgebraicIndependent
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResR
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TorusMemFldF
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TraceChart
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidChartPf

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

open Polynomial

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext_scale (A T : Subalgebra K R) (w : R) (hwA : w ∈ A)
    (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) (g : R) (hg : IsIntegral T g) :
    ∃ N : ℕ, IsIntegral A (w ^ N * g) := by
  obtain ⟨p, hpm, hp⟩ := hg
  have hmono : ∀ (x : R) (n m : ℕ), n ≤ m → w ^ n * x ∈ A → w ^ m * x ∈ A := by
    intro x n m hnm hx
    have : w ^ m * x = w ^ (m - n) * (w ^ n * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    exact A.mul_mem (A.pow_mem hwA _) hx
  have hc : ∀ i : ℕ, ∃ n : ℕ, w ^ n * ((p.coeff i : T) : R) ∈ A := fun i =>
    hscale _ (p.coeff i).2
  choose n hn using hc
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hcN : ∀ i ≤ p.natDegree, w ^ N * ((p.coeff i : T) : R) ∈ A := by
    intro i hi
    refine hmono _ (n i) N ?_ (hn i)
    exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set P : R[X] := p.map (algebraMap T R) with hP
  have hPm : P.Monic := hpm.map _
  have hPdeg : P.natDegree = p.natDegree := hpm.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i = ((p.coeff i : T) : R) := fun i => by
    rw [hP, coeff_map]; rfl
  set Q : R[X] := P.scaleRoots (w ^ N) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hPm
  have hQlift : Q ∈ lifts (algebraMap A R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have hmem : Q.coeff i ∈ A := by
      rw [hQ, coeff_scaleRoots, hPdeg, hPcoeff]
      rcases lt_trichotomy i p.natDegree with hlt | heq | hgt
      · have h1 : (w ^ N) ^ (p.natDegree - i) = (w ^ N) ^ (p.natDegree - i - 1) * w ^ N := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, mul_comm, mul_assoc]
        exact A.mul_mem (A.pow_mem (A.pow_mem hwA _) _) (hcN i hlt.le)
      · subst heq
        have : p.coeff p.natDegree = 1 := hpm.coeff_natDegree
        rw [this, Nat.sub_self, pow_zero, mul_one]
        exact A.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact A.zero_mem
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqQ, -, hqm⟩ := lifts_and_degree_eq_and_monic hQlift hQm
  refine ⟨N, q, hqm, ?_⟩
  rw [← eval_map, hqQ, hQ, scaleRoots_eval_mul, hP, eval_map, hp, mul_zero]

theorem chart_ext_pf (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := by
  classical
  obtain ⟨t, ht⟩ := hB0FG
  obtain ⟨s, hs⟩ := hBuFG
  have hkey : ∀ g : R, ∃ N : ℕ, g ∈ Bu → IsIntegral A (w ^ N * g) := by
    intro g
    by_cases hg : g ∈ Bu
    · obtain ⟨N, hN⟩ := chart_ext_scale A T w hwA hscale g (hBuInt g hg)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose N hN using hkey
  set u : Finset R := t ∪ s.image (fun g => w ^ N g * g) with hu
  set B' : Subalgebra K R := Algebra.adjoin K (u : Set R) with hB'
  have htB' : B0 ≤ B' := by
    rw [← ht, hB']
    exact Algebra.adjoin_mono (by rw [hu, Finset.coe_union]; exact Set.subset_union_left)
  have hwB' : w ∈ B' := htB' (hAB0 hwA)
  have hgen : ∀ g ∈ s, w ^ N g * g ∈ B' := by
    intro g hg
    apply Algebra.subset_adjoin
    rw [hu, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg))
  have hsBu : ∀ g ∈ s, g ∈ Bu := fun g hg => by
    rw [← hs]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hg)

  have hpow : ∀ b ∈ Bu, ∃ L : ℕ, w ^ L * b ∈ B' := by
    intro b hb
    rw [← hs] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨N x, hgen x (Finset.mem_coe.1 hx)⟩
    | algebraMap k => exact ⟨0, by rw [pow_zero, one_mul]; exact B'.algebraMap_mem k⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x + y) = w ^ L2 * (w ^ L1 * x) + w ^ L1 * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.add_mem (B'.mul_mem (B'.pow_mem hwB' _) h1) (B'.mul_mem (B'.pow_mem hwB' _) h2)
    | mul x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x * y) = (w ^ L1 * x) * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.mul_mem h1 h2
  refine ⟨B', htB', ⟨u, hB'.symm⟩, ?_, ?_⟩
  · intro b hb
    rw [hB'] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rw [hu, Finset.coe_union] at hx
      rcases hx with hx | hx
      · apply hB0Int
        rw [← ht]
        exact Algebra.subset_adjoin hx
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hN g (hsBu g hg)
    | algebraMap k =>
      have hk : algebraMap K R k ∈ A := A.algebraMap_mem k
      have : algebraMap K R k = algebraMap A R ⟨_, hk⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  · intro r
    obtain ⟨b, hb, b', hb', hb'0, hrb⟩ := hFrac r
    obtain ⟨L1, h1⟩ := hpow b hb
    obtain ⟨L2, h2⟩ := hpow b' hb'
    refine ⟨w ^ (L1 + L2) * b, ?_, w ^ (L1 + L2) * b', ?_, ?_, ?_⟩
    · have : w ^ (L1 + L2) * b = w ^ L2 * (w ^ L1 * b) := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h1
    · have : w ^ (L1 + L2) * b' = w ^ L1 * (w ^ L2 * b') := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h2
    · exact mul_ne_zero (pow_ne_zero _ hw0) hb'0
    · rw [← hrb]; ring

end CrystallineSemistableComparison.Pb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ChartExt

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b :=
  chart_ext_pf A T B0 Bu hAT hAB0 hB0 hTBu hB0FG hB0Int hBuFG hBuInt hFrac w hwA hw0 hscale

end CrystallineSemistableComparison.Pb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidStmt

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

theorem resid_alg : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R) :=
  by
  intro K _ _ n R _ _ _ t ht D hD B hTB hFG hInt hMono hFrac ω η hω hη heq
  have hne : ∀ i : Fin (n + 2), (Finset.univ.erase i).Nonempty := fun i => by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hune : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  have hfin : FiniteDimensional (fldF K t) (FractionRing R) :=
    fldF_findim t (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac
  obtain ⟨res, hres1, hres0, hresD⟩ := res_R t ht D hD

  let Φ : R →+ FractionRing R :=
    ((algebraMap (fldF K t) (FractionRing R)).toAddMonoidHom.comp
      (Algebra.trace (fldF K t) (FractionRing R)).toAddMonoidHom).comp
      (algebraMap R (FractionRing R)).toAddMonoidHom
  have hΦ : ∀ x, Φ x = algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) x)) := fun _ => rfl

  have hchart : ∀ i : Fin (n + 2), ∃ B' : Subalgebra K R, B (Finset.univ.erase i) ≤ B' ∧
      torusS K t (Finset.univ.erase i) ≤ B' ∧ B'.FG ∧
      (∀ b ∈ B', IsIntegral (torusS K t (Finset.univ.erase i)) b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := fun i => by
    obtain ⟨w, hwA, hw0, hscale⟩ := torus_scale (K := K) t i
    obtain ⟨B', hB', hFG', hInt', hFrac'⟩ := chart_ext (torusS K t (Finset.univ.erase i)) (torusS K t Finset.univ)
      (B (Finset.univ.erase i)) (B Finset.univ) (torusS_le_univ t _) (hTB _ (hne i)) (hMono i) (hTB _ hune)
      (hFG _ (hne i)) (hInt _ (hne i)) (hFG _ hune) (hInt _ hune) hFrac w hwA hw0 hscale
    exact ⟨B', hB', (hTB _ (hne i)).trans hB', hFG', hInt', hFrac'⟩

  have hω' : ∀ i, ∃ a : R, Φ (ω i) = algebraMap R (FractionRing R) a ∧ res a = 0 := by
    intro i
    obtain ⟨B', hB', hTB', hFG', hInt', hFrac'⟩ := hchart i
    induction i using Fin.cases with
    | zero =>
      obtain ⟨y', hy', hyeq⟩ := jacobian_infinityDerivation t D (B (Finset.univ.erase 0)) (ω 0) (hω 0)
      obtain ⟨hinj, hloc⟩ := infinityCoord_localization t ht
      obtain ⟨a', ha'S, ha'⟩ := trace_chart t (Finset.univ.erase 0) (fun k => ⟨u0 t k, infinityCoord_mem_torus t k⟩) hinj hloc
        (torusS_frac t _ (hne 0)) B' hTB' hFG' hInt' hFrac' (infinityDerivation t D) (fun k j => infinityDerivation_coord t D hD k j) id
        Function.injective_id y' (jacS_mono _ _ hB' _ _ hy')
      set c : R := -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) with hc
      have hcT : c ∈ torusS K t Finset.univ := neg_mem (pow_mem (inv_mem_univ t 0) _)
      let cF : fldF K t := ⟨algebraMap R (FractionRing R) c, torus_mem_fldF t Finset.univ c hcT⟩
      refine ⟨c * a', ?_, ?_⟩
      · rw [hΦ, hyeq, RingHom.map_mul (algebraMap R (FractionRing R)) c y']
        have h1 : algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) y' =
            cF • algebraMap R (FractionRing R) y' := rfl
        rw [h1, LinearMap.map_smul, smul_eq_mul, RingHom.map_mul, ha', RingHom.map_mul]
        rfl
      · rw [hc, neg_mul, map_neg, hres0 _ (infinityCoord_span_residue_ne t a' ha'S), neg_zero]
    | succ k =>
      have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
        Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
      obtain ⟨hinj, hloc⟩ := torusS_loc t ht _ h0
      obtain ⟨a, haS, ha⟩ := trace_chart t (Finset.univ.erase k.succ)
        (fun k => ⟨t k, t_mem_torusS t _ h0 k⟩) hinj hloc
        (torusS_frac t _ (hne _)) B' hTB' hFG' hInt' hFrac' D (fun k j => hD k j) id
        Function.injective_id (ω k.succ) (jacS_mono _ _ hB' _ _ (hω k.succ))
      exact ⟨a, ha, hres0 _ (torusS_succ_span t k a haS)⟩

  have hη' : ∀ k, ∃ b : R, Φ (D k (η k)) = algebraMap R (FractionRing R) b ∧ res b = 0 := by
    intro k
    obtain ⟨hinj, hloc⟩ := torusS_loc t ht Finset.univ (Finset.mem_univ 0)
    obtain ⟨b, hbT, hb⟩ := trace_chart t Finset.univ (fun k => ⟨t k, t_mem_torusS t _ (Finset.mem_univ 0) k⟩)
      hinj hloc (torusS_frac t _ hune) (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac D
      (fun k j => hD k j) (Fin.succAbove k) Fin.succAbove_right_injective (η k) (hη k)
    have hDc : ∀ j, D k (t j : R) ∈ Set.range (algebraMap K R) := fun j => by
      rw [hD]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    exact ⟨D k b, trace_deriv t (D k) hDc (η k) b hbT hb, hresD k b hbT⟩
  choose a ha using hω'
  choose b hb using hη'

  have : Module.Free (fldF K t) (FractionRing R) := Module.Free.of_divisionRing _ _
  have hp : (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := prod_inv_mem t
  let pF : fldF K t := ⟨algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R), torus_mem_fldF t _ _ hp⟩
  have hsign : ∀ (k : Fin (n + 1)) (x : R), (-1 : R) ^ (k : ℕ) * x = ((-1 : ℤ) ^ (k : ℕ)) • x := fun k x => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hrel : Module.finrank (fldF K t) (FractionRing R) • (((∏ k, t k)⁻¹ : Rˣ) : R) =
      ∑ i, a i + ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • b k := by
    apply IsFractionRing.injective R (FractionRing R)
    have h1 := congrArg Φ heq

    simp only [map_add (f := _), map_sum, hsign] at h1

    rw [map_nsmul, map_add (f := _), map_sum, map_sum]
    simp only [map_zsmul]
    simp only [map_zsmul, fun i => (ha i).1, fun k => (hb k).1] at h1
    rw [← h1, hΦ]
    have h2 : algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R) =
        algebraMap (fldF K t) (FractionRing R) pF := rfl
    rw [h2, Algebra.trace_algebraMap, map_nsmul]
  have hres := congrArg res hrel

  rw [map_nsmul, hres1, map_add (f := _), map_sum, map_sum] at hres
  simp only [map_zsmul, fun i => (ha i).2, fun k => (hb k).2, smul_zero, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one] at hres
  rw [Nat.cast_eq_zero] at hres
  exact (Module.finrank_pos (R := fldF K t) (M := FractionRing R)).ne' hres

end CrystallineSemistableComparison.Pb
end
end
end
