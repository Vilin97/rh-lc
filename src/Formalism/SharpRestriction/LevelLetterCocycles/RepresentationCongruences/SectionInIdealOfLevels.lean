module

public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Mathlib.Algebra.Order.Star.Int

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPartitionOfLPowLevels

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def LetterCoprime (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, lA W ^ m = r * x + s * z

theorem l_pow_mem_invariants (m : ℕ) : lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

theorem Coprime_symm {x z : LetA O n} (h : LetterCoprime W x z) : LetterCoprime W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

theorem Coprime_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : LetterCoprime W x z) (h2 : LetterCoprime W y z) : LetterCoprime W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (l_pow_mem_invariants W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

theorem Coprime_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h : LetterCoprime W x z) : ∀ N : ℕ, LetterCoprime W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact Coprime_mul W (W.AΔ.pow_mem hx N) hz ih h

theorem Coprime_prod (s : Finset ℕ) (x : ℕ → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, LetterCoprime W (x i) z) :
    LetterCoprime W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact Coprime_mul W (W.AΔ.prod_mem fun i _ => hx i) hz
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s))

theorem level_mem_invariants (s : ℕ) : ps W s ∈ W.AΔ :=
  Formalism.MainNotions.UnusedSlot80.UnivC.ps_mem W s

theorem exists_partition_of_l_pow_levels (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (N : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ m : ℕ, ∃ ε : ℕ → LetA O n, (∀ s, ε s ∈ W.AΔ) ∧
      (∀ s ∈ S, ∃ r ∈ W.AΔ, ε s = (∏ t ∈ S.erase s, ps W t ^ N) * r) ∧
      ∑ s ∈ S, ε s = lA W ^ m := by
  have hps := level_mem_invariants W
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with h0 | hne
    · subst h0
      refine ⟨0, fun _ => 1, fun _ => W.AΔ.one_mem, fun t ht => ⟨1, W.AΔ.one_mem, ?_⟩, ?_⟩
      · have h1 : t = a := by simpa using ht
        subst h1; simp
      · simp
    obtain ⟨m, ε, hεΔ, hεd, hsum⟩ := ih hne
    set P := ∏ t ∈ s, ps W t ^ N with hP
    have hPΔ : P ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) N
    have hcop : LetterCoprime W (ps W a ^ N) P := by
      refine Coprime_symm W (Coprime_prod W s _ (fun t => W.AΔ.pow_mem (hps t) N)
        (W.AΔ.pow_mem (hps a) N) fun t ht => ?_)
      have hta : t ≠ a := fun h => ha (h ▸ ht)
      obtain ⟨κ, x, hx, y, hy, hxy⟩ := hC t a hta
      have h1 : LetterCoprime W (ps W t) (ps W a) := ⟨κ, x, hx, y, hy, hxy⟩
      have h2 := Coprime_pow W (hps t) (hps a) h1 N
      exact Coprime_symm W
        (Coprime_pow W (hps a) (W.AΔ.pow_mem (hps t) N) (Coprime_symm W h2) N)
    obtain ⟨m', r, hr, q, hq, he⟩ := hcop
    refine ⟨m + m', fun t => if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N, ?_, ?_, ?_⟩
    · intro t
      by_cases h : t = a
      · simp only [h, if_true]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (l_pow_mem_invariants W m) hq) hPΔ
      · simp only [h, if_false]
        exact W.AΔ.mul_mem (W.AΔ.mul_mem (hεΔ t) hr) (W.AΔ.pow_mem (hps a) N)
    · intro t ht
      by_cases h : t = a
      · subst h
        refine ⟨lA W ^ m * q, W.AΔ.mul_mem (l_pow_mem_invariants W m) hq, ?_⟩
        simp only [if_true, Finset.erase_insert ha]
        ring
      · have hts : t ∈ s := by
          rcases Finset.mem_insert.1 ht with h' | h'
          · exact absurd h' h
          · exact h'
        obtain ⟨r₁, hr₁, he₁⟩ := hεd t hts
        refine ⟨r₁ * r, W.AΔ.mul_mem hr₁ hr, ?_⟩
        have hat : a ∉ s.erase t := fun h' => ha (Finset.mem_of_mem_erase h')
        simp only [h, if_false, Finset.erase_insert_of_ne (Ne.symm h), Finset.prod_insert hat, he₁]
        ring
    · rw [Finset.sum_insert ha]
      simp only [if_true]
      have hs2 : ∑ t ∈ s, (if t = a then lA W ^ m * q * P else ε t * r * ps W a ^ N) =
          ∑ t ∈ s, ε t * r * ps W a ^ N :=
        Finset.sum_congr rfl fun t ht => by
          have : t ≠ a := fun h' => ha (h' ▸ ht)
          simp [this]
      rw [hs2, ← Finset.sum_mul, ← Finset.sum_mul, hsum, pow_add, he]
      ring

theorem isUnit_algebraMap_ps_of_ringP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨h3, h6⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_qpow W h3 h6 s)
  simpa [ps, qA, lA] using this

theorem toNat_add_neg_identity (x : ℤ) (N : ℕ) :
    (x + N).toNat + (-x).toNat = x.toNat + N + (-(x + N)).toNat := by
  omega

theorem inId_shift_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : ZMod n} {e s N : ℕ}
    (hs : s < e) {α : ℕ → ℤ} {g : W.EE} (hg : InId W a e α g) {x : LetA O n} (hx : x ∈ W.AΔ) :
    InId W a e (fun t => if t = s then α t else α t + N)
      (algebraMap (LetA O n) W.EE ((∏ t ∈ (Finset.range e).erase s, ps W t ^ N) * x) * g) := by
  obtain ⟨u, hu, he⟩ := hg
  set α' : ℕ → ℤ := fun t => if t = s then α t else α t + N with hα'
  set D := ∏ t ∈ Finset.range e, ps W t ^ (-(α t)).toNat with hD
  set Nm := ∏ t ∈ Finset.range e, ps W t ^ (α t).toNat with hNm
  set D' := ∏ t ∈ Finset.range e, ps W t ^ (-(α' t)).toNat with hD'
  set Nm' := ∏ t ∈ Finset.range e, ps W t ^ (α' t).toNat with hNm'
  set Pz := ∏ t ∈ (Finset.range e).erase s, ps W t ^ N with hPzDef
  have hδ : ∏ t ∈ Finset.range e, ps W t ^ (if t = s then 0 else N) = Pz := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs)]
    simp only [if_true, pow_zero, one_mul]
    exact Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  have key : Nm' * D = Nm * Pz * D' := by
    rw [← hδ, hNm', hD, hNm, hD', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    simp only [hα']
    by_cases h : t = s
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
      exact toNat_add_neg_identity (α t) N
  have hDU : IsUnit (algebraMap (LetA O n) W.EE D) := by
    rw [hD, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun t _ => by
      rw [map_pow]; exact (isUnit_algebraMap_ps_of_ringP W hR t).pow _
  show ∃ u ∈ W.AΔ, algebraMap (LetA O n) W.EE D' * (algebraMap (LetA O n) W.EE (Pz * x) * g) =
    algebraMap (LetA O n) W.EE (letE a * Nm' * u)
  refine ⟨x * u, W.AΔ.mul_mem hx hu, ?_⟩
  apply hDU.mul_left_cancel
  have e1 : algebraMap (LetA O n) W.EE D * (algebraMap (LetA O n) W.EE D' *
      (algebraMap (LetA O n) W.EE (Pz * x) * g)) =
      algebraMap (LetA O n) W.EE D' * algebraMap (LetA O n) W.EE (Pz * x) *
        (algebraMap (LetA O n) W.EE D * g) := by ring
  rw [e1, he]
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  linear_combination (-(letE a * x * u)) * key

end Core

end Formalism.MainNotions.N.Ln17
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SectionInIdealOfLevels

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem section_in_ideal_of_levels (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hC : Formalism.MainNotions.UnusedSlot80.KL.PsCoprime W)
    (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (he : 1 ≤ e) {d : ℕ} (b : Fin d → W.DD T)
    (h : Fin d → W.EE)
    (hlev : ∀ s < e, ∃ κ : ℕ, SecIn W a e
      (fun α c₀ => dvO W T e b c₀ ∈ FilS W T a s (-(α s))) (fun k => lE W κ * h k))
    (hlow : ∀ t < e, ∃ U : ℤ, ∀ u ≤ U, ∀ c₀ : Fin d → O, dvO W T e b c₀ ∈ FilS W T a t u) :
    ∃ κ : ℕ, SecIn W a e (condNN W T a e b) (fun k => lE W κ * h k) := by
  have hlev' : ∀ s : ℕ, ∃ κ : ℕ, ∃ I : ℕ, ∃ g : Fin I → W.EE, ∃ c₀ : Fin I → Fin d → O,
      ∃ α : Fin I → ℕ → ℤ, s < e →
        (∀ i, InId W a e (α i) (g i) ∧ dvO W T e b (c₀ i) ∈ FilS W T a s (-(α i s))) ∧
        ∀ k, lE W κ * h k = ∑ i, g i * algebraMap O W.EE (c₀ i k) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨κ, I, g, c₀, α, h1, h2⟩ := hlev s hs
      exact ⟨κ, I, g, c₀, α, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun h' => absurd h' hs⟩
  choose κs I g c₀ α hsec using hlev'
  have hlow' : ∀ t : ℕ, ∃ U : ℤ, t < e → ∀ u ≤ U, ∀ c : Fin d → O, dvO W T e b c ∈ FilS W T a t u := by
    intro t
    by_cases ht : t < e
    · obtain ⟨U, hU⟩ := hlow t ht
      exact ⟨U, fun _ => hU⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose U hU using hlow'
  set N : ℕ := ∑ s ∈ Finset.range e, ∑ i : Fin (I s), ∑ t ∈ Finset.range e,
    ((U t).natAbs + (α s i t).natAbs) with hN
  set κ : ℕ := ∑ s ∈ Finset.range e, κs s with hκ
  obtain ⟨m, ε, -, hεd, hsum⟩ :=
    exists_partition_of_l_pow_levels W hC N (Finset.range e) ⟨0, Finset.mem_range.2 (by omega)⟩
  choose! r hr hεr using hεd
  have hlE : ∀ j, lE W j = algebraMap (LetA O n) W.EE (lA W ^ j) := by
    intro j; simp [lE, lA]
  have hκs : ∀ s < e, κs s ≤ κ := fun s hs =>
    Finset.single_le_sum (f := κs) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  let σ := Σ s : Fin e, Fin (I s)
  let eqv := Fintype.equivFin σ
  let G' : σ → W.EE := fun p => algebraMap (LetA O n) W.EE
    ((∏ t ∈ (Finset.range e).erase (p.1 : ℕ), ps W t ^ N) * (r p.1 * lA W ^ (κ - κs p.1))) * g p.1 p.2
  let C' : σ → Fin d → O := fun p => c₀ p.1 p.2
  let A' : σ → ℕ → ℤ := fun p t => if t = (p.1 : ℕ) then α p.1 p.2 t else α p.1 p.2 t + N
  have hmono : ∀ p : σ, InId W a e (A' p) (G' p) ∧ condNN W T a e b (A' p) (C' p) := by
    rintro ⟨⟨s, hs⟩, i⟩
    have hx : r s * lA W ^ (κ - κs s) ∈ W.AΔ :=
      W.AΔ.mul_mem (hr s (Finset.mem_range.2 hs)) (l_pow_mem_invariants W _)
    refine ⟨inId_shift_levels W hR hs ((hsec s hs).1 i).1 hx, fun t ht => ?_⟩
    by_cases hts : t = s
    · subst hts
      simp only [A', if_true]
      exact ((hsec t hs).1 i).2
    · simp only [A', hts, if_false]
      refine hU t ht _ ?_ _
      have h1 : (U t).natAbs + (α s i t).natAbs ≤
          ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) :=
        Finset.single_le_sum (f := fun t' => (U t').natAbs + (α s i t').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 ht)
      have h2 : ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i t').natAbs) ≤
          ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) :=
        Finset.single_le_sum (f := fun i' => ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 : ∑ i' : Fin (I s), ∑ t' ∈ Finset.range e, ((U t').natAbs + (α s i' t').natAbs) ≤ N :=
        Finset.single_le_sum (f := fun s' => ∑ i' : Fin (I s'), ∑ t' ∈ Finset.range e,
          ((U t').natAbs + (α s' i' t').natAbs)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
      have hN' : (((U t).natAbs : ℕ) : ℤ) + (((α s i t).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast h1.trans (h2.trans h3)
      rw [Int.natCast_natAbs, Int.natCast_natAbs] at hN'
      have e1 := neg_abs_le (U t)
      have e2 := neg_abs_le (α s i t)
      linarith
  refine ⟨m + κ, Fintype.card σ, fun j => G' (eqv.symm j), fun j => C' (eqv.symm j),
    fun j => A' (eqv.symm j), fun j => hmono (eqv.symm j), fun k => ?_⟩
  rw [Equiv.sum_comp eqv.symm (fun p => G' p * algebraMap O W.EE (C' p k)), Fintype.sum_sigma]
  calc lE W (m + κ) * h k
      = (∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s)) * (lE W κ * h k) := by

        rw [← map_sum, hsum, ← hlE, lE, lE, lE, pow_add]; ring
    _ = ∑ s ∈ Finset.range e, algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : lE W κ = lE W (κ - κs s) * lE W (κs s) := by
          rw [lE, lE, lE, ← pow_add, Nat.sub_add_cancel (hκs s (Finset.mem_range.1 hs))]
        rw [this]; ring
    _ = ∑ s : Fin e, ∑ i : Fin (I s), G' ⟨s, i⟩ * algebraMap O W.EE (C' ⟨s, i⟩ k) := by
        rw [Finset.sum_range (fun s => algebraMap (LetA O n) W.EE (ε s) * lE W (κ - κs s) *
          (lE W (κs s) * h k))]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [(hsec s s.2).2 k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [G', C']
        rw [hεr s (Finset.mem_range.2 s.2), hlE]
        simp only [map_mul]
        ring

end Core

end Formalism.MainNotions.N.Ln17
end
end
end
