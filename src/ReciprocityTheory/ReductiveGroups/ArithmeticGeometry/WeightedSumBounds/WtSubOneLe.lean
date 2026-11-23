module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CardToMultisetEqDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.RingTheory.PowerSeries.Expand
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem geom_sum_root {p : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ m) ^ j = if p ∣ m then (p : C) else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · have hne : ζ ^ m ≠ 1 := fun h1 => h (hζ.dvd_of_pow_eq_one m h1)
    rw [geom_sum_eq hne, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem exists_average (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {ζ : C}
    (hζ : IsPrimitiveRoot ζ p) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    ∃ δ : Fin d → PowerSeries C, IsCurve v δ ∧ ∀ c j, PowerSeries.coeff j (G.lgCurve δ c) =
      (p : C) * PowerSeries.coeff (p * j) (G.lgCurve ga c) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0 := fun b => (hga b).1
  have hζv : ∀ j : ℕ, IsIntV v (ζ ^ j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one (v := v) hp0
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])]

  obtain ⟨g, hgdef⟩ : ∃ g : Fin p → Fin d → PowerSeries C,
      ∀ u, g u = rescaleCurve (ζ ^ (u : ℕ)) ga := ⟨fun u => rescaleCurve (ζ ^ (u : ℕ)) ga, fun u => rfl⟩
  have hg : ∀ u, IsCurve v (g u) := fun u => by
    rw [hgdef]
    exact isCurve_rescale (hζv u) hga
  obtain ⟨ε, hεdef⟩ : ∃ ε : Fin d → PowerSeries C, ε = G.sumF g := ⟨_, rfl⟩
  have hε : IsCurve v ε := by
    rw [hεdef]
    exact isCurve_sumF G g hg
  have hεc : ∀ b, PowerSeries.constantCoeff (ε b) = 0 := fun b => (hε b).1
  have hsum : ∀ m : ℕ, ∑ u : Fin p, (ζ ^ (u : ℕ)) ^ m = if p ∣ m then (p : C) else 0 := by
    intro m
    rw [← geom_sum_root hζ m, Fin.sum_univ_eq_sum_range (fun j => (ζ ^ j) ^ m) p]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hlgε : ∀ c m, PowerSeries.coeff m (G.lgCurve ε c) =
      if p ∣ m then (p : C) * PowerSeries.coeff m (G.lgCurve ga c) else 0 := by
    intro c m

    rw [hεdef, lgCurve_sumF G g hg c, map_sum]
    simp only [hgdef, lgCurve_rescale G _ h0, PowerSeries.coeff_rescale]
    rw [← Finset.sum_mul, hsum m]
    split_ifs <;> simp

  have hinv : ∀ a, rescaleCurve ζ ε a = ε a := by
    have hζ1 : IsIntV v ζ := by simpa using hζv 1
    have hεζc : ∀ b, PowerSeries.constantCoeff (rescaleCurve ζ ε b) = 0 :=
      fun b => (isCurve_rescale hζ1 hε b).1
    intro a
    have hdvd : ∀ N, (PowerSeries.X : PowerSeries C) ^ N ∣ rescaleCurve ζ ε a - ε a := fun N =>
      dvd_of_lgCurve_low G hεζc hεc N (fun a' j _ => by
        rw [lgCurve_rescale G ζ hεc, PowerSeries.coeff_rescale, hlgε]
        split_ifs with h
        · obtain ⟨k, rfl⟩ := h
          rw [pow_mul, hζ.pow_eq_one, one_pow, one_mul]
        · rw [mul_zero]) a
    rw [← sub_eq_zero]
    ext m
    have := (PowerSeries.X_pow_dvd_iff.mp (hdvd (m + 1))) m (Nat.lt_succ_self m)
    simpa using this
  have hoff : ∀ a m, ¬ p ∣ m → PowerSeries.coeff m (ε a) = 0 := by
    intro a m hm
    have h1 := congrArg (PowerSeries.coeff m) (hinv a)
    simp only [rescaleCurve, PowerSeries.coeff_rescale] at h1
    have hne : ζ ^ m ≠ 1 := fun h => hm (hζ.dvd_of_pow_eq_one m h)
    have h2 : (ζ ^ m - 1) * PowerSeries.coeff m (ε a) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

  obtain ⟨δ, hδdef⟩ : ∃ δ : Fin d → PowerSeries C,
      ∀ a, δ a = PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a) :=
    ⟨fun a => PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a), fun a => rfl⟩
  have hexpand : ∀ (f : PowerSeries C) (m : ℕ), PowerSeries.coeff m (PowerSeries.expand p hp0 f) =
      if p ∣ m then PowerSeries.coeff (m / p) f else 0 := by
    intro f m
    have h := coeff_expand_rescale p hp0 1 f m
    rw [PowerSeries.rescale_one, RingHom.id_apply] at h
    rw [h]
    split_ifs <;> simp
  have hexp : ∀ a, PowerSeries.expand p hp0 (δ a) = ε a := by
    intro a
    ext m
    rw [hexpand]
    split_ifs with h
    · rw [hδdef, PowerSeries.coeff_mk, Nat.mul_div_cancel' h]
    · exact (hoff a m h).symm
  have hδ : IsCurve v δ := fun a => by
    refine ⟨?_, fun j => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hδdef, PowerSeries.coeff_mk, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hεc a
    · rw [hδdef, PowerSeries.coeff_mk]
      exact (hε a).2 (p * j)
  have hεδ : expC p δ = ε := funext fun a => by
    rw [expC_apply hp0]
    exact hexp a
  refine ⟨δ, hδ, fun c j => ?_⟩
  have h1 := lgCurve_expC G hp0 (fun b => (hδ b).1) c
  rw [hεδ] at h1
  have h2 := congrArg (PowerSeries.coeff (p * j)) h1
  rw [hlgε, if_pos (dvd_mul_right p j), hexpand, if_pos (dvd_mul_right p j),
    Nat.mul_div_cancel_left j hp.pos] at h2
  exact h2.symm

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb

noncomputable section

theorem pt6' : TypicalCurveRebasing := by
  unfold TypicalCurveRebasing
  intro C _ _ _ v p hp hv d m G γ x hc hx
  dsimp only
  have hcr : ∀ u, IsCurve v (rescaleCurve (x u) (γ u)) := fun u => isCurve_rescale (hx u) (hc u)
  have hγ' : IsCurve v (G.sumF fun u => rescaleCurve (x u) (γ u)) := isCurve_sumF G _ hcr
  have hlc : ∀ (k : ℕ) (a : Fin d),
      PowerSeries.coeff k (G.lgCurve (G.sumF fun u => rescaleCurve (x u) (γ u)) a) =
        ∑ u, x u ^ k * PowerSeries.coeff k (G.lgCurve (γ u) a) := by
    intro k a

    rw [lgCurve_sumF G _ hcr a, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [lgCurve_rescale G (x u) (fun b => (hc u b).1) a, PowerSeries.coeff_rescale]
  have hL : ∀ n : ℕ, G.lc p (G.sumF fun u => rescaleCurve (x u) (γ u)) n =
      ∑ u, x u ^ p ^ n • G.lc p (γ u) n := by
    intro n
    funext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, LogFGL.lc]
    exact hlc (p ^ n) a
  refine ⟨hγ', ?_, hL, ?_⟩
  · rw [tangent_eq_lc_zero G p (fun b => (hγ' b).1), hL 0]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tangent_eq_lc_zero G p (fun b => (hc u b).1), pow_zero, pow_one]
  · intro hT
    unfold LogFGL.IsPTypical at hT ⊢
    intro a k hk
    rw [hlc k a]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [hT u a k hk, mul_zero]

theorem pt5' : TypicalCurveStructureConstants := by
  intro C _ _ _ v p hp hv d h ty G γ hB
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (tmat γ).det = 0 := hdet
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  choose δ hδc hδlg using fun a => exists_average G hp hζ (hγ a)
  have hlcδ : ∀ a n, G.lc p (δ a) n = (p : C) • G.lc p (γ a) (n + 1) := by
    intro a n
    funext c
    simp only [LogFGL.lc, Pi.smul_apply, smul_eq_mul]
    rw [hδlg, pow_succ']
  have hδt : ∀ a, G.IsOfType p ty (ty a + 1) (δ a) := by
    intro a
    refine ⟨fun c j hj => ?_, fun n c hc => ?_⟩
    · rw [hδlg, (hγty a).1 c (p * j) (fun k hk => ?_), mul_zero]
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hk)
      · exact hj k (by rw [pow_succ'] at hk; exact Nat.eq_of_mul_eq_mul_left hp.pos hk)
    · rw [hlcδ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [(hγty a).2 (n + 1) c (by intro e; apply hc; rw [e]; push_cast; ring), mul_zero]
  refine ⟨fun s b a => ptx G p γ (δ a) s b,
    fun s b a => ptx_int G hp hγ (fun b => (hγty b).1) hdet' (δ a) (hδc a) (hδt a).1 s b,
    fun s b a hne => ?_, fun a n => ?_⟩
  · rw [ptx_type ty G hp hγ hdet' hγty (δ a) _ (hδt a) s b hne]
    ring
  · rw [← hlcδ a n, ptx_rel G p hγ hdet' (δ a) n]
    refine (Finset.sum_range_reflect _ (n + 1)).symm.trans ?_
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    dsimp only
    rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn]

theorem wt_sub_one_le {r : ℝ} {y : WithTop ℝ} (h : (r : WithTop ℝ) ≤ 1 + y) :
    ((r - 1 : ℝ) : WithTop ℝ) ≤ y := by
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    have h1 : ((1 : WithTop ℝ) + (a : WithTop ℝ)) = ((1 + a : ℝ) : WithTop ℝ) := by
      norm_cast
    rw [h1, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (by linarith)

private theorem le_valuation_finset_sum {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
    {ι : Type} (s : Finset ι) (f : ι → C) (g : WithTop ℝ) (h : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih h
  rw [Finset.sum_insert hi]
  exact le_trans (le_min (h i (Finset.mem_insert_self i s))
    (ih fun j hj => h j (Finset.mem_insert_of_mem hj))) (AddValuation.map_add v _ _)

theorem pt5v' : TypicalCurveValuationBounds := by
  unfold TypicalCurveValuationBounds
  intro C _ _ _ v p hp hv d h ty G γ hB a
  obtain ⟨sc, hsc, -, hrec⟩ := pt5' C v p hp hv d h ty G γ hB
  obtain ⟨hcur, -, hdet⟩ := hB
  have H1 : ∀ (n : ℕ) (b c : Fin d), (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ b) n c) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b c
    rcases n with _ | n
    · rw [← tangent_eq_lc_zero G p (fun e => (hcur b e).1)]
      have h0 : (0 : WithTop ℝ) ≤ v (tangent (γ b) c) := (hcur b c).2 1
      have e0 : (((-((0 : ℕ) : ℝ)) : ℝ) : WithTop ℝ) = 0 := by simp
      rw [e0]
      exact h0
    · have hr := congrFun (hrec b n) c
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
      have hge : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ b) (n + 1) c) := by
        rw [hr]
        apply le_valuation_finset_sum
        intro m hm
        apply le_valuation_finset_sum
        intro e _
        rw [AddValuation.map_mul, AddValuation.map_pow]
        have hm' : m < n + 1 := Finset.mem_range.mp hm
        have h1 : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (n - m) e b) := nsmul_nonneg (hsc _ _ _) _
        have h2 := ih m hm' e c
        have h3 : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hm'
          linarith
        calc (((-(n : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(n : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (n - m) e b) + v (G.lc p (γ e) m c) := add_le_add h1 (h3.trans h2)
      rw [AddValuation.map_mul, hv] at hge
      have := wt_sub_one_le hge
      convert this using 2
      push_cast
      ring
  refine ⟨fun n c => H1 n a c, ?_⟩
  intro h1 n c hn
  have hne : Matrix.det (Matrix.of fun a b => tangent (γ a) b) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    simp at hdet
  have hs0 : ∀ e, sc 0 e a = 0 := by
    have hr := hrec a 0
    simp only [zero_add] at hr
    rw [h1, smul_zero, Finset.sum_range_one] at hr
    simp only [tsub_zero, pow_zero, pow_one] at hr
    have hM : Matrix.vecMul (fun e => sc 0 e a) (Matrix.of fun e b => tangent (γ e) b) = 0 := by
      funext b
      have hb := congrFun hr b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      refine Eq.trans ?_ hb.symm
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [tangent_eq_lc_zero G p (fun f => (hcur e f).1)]
    intro e
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hne hM) e
  obtain _ | _ | k := n
  · omega
  · have h10 : G.lc p (γ a) (0 + 1) c = 0 := by simp [h1]
    rw [h10, AddValuation.map_zero]
    exact le_top
  · have hr := congrFun (hrec a (k + 1)) c
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
    have hge : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ a) (k + 1 + 1) c) := by
      rw [hr]
      apply le_valuation_finset_sum
      intro m hm
      apply le_valuation_finset_sum
      intro e _
      have hm' : m < k + 1 + 1 := Finset.mem_range.mp hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | heq
      · rw [AddValuation.map_mul, AddValuation.map_pow]
        have h1' : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (k + 1 - m) e a) := nsmul_nonneg (hsc _ _ _) _
        have h2 := H1 m e c
        have h3 : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp hlt
          linarith
        calc (((-(k : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(k : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (k + 1 - m) e a) + v (G.lc p (γ e) m c) := add_le_add h1' (h3.trans h2)
      · subst heq
        rw [Nat.sub_self, hs0 e, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul, AddValuation.map_zero]
        exact le_top
    rw [AddValuation.map_mul, hv] at hge
    have := wt_sub_one_le hge
    convert this using 2
    push_cast
    ring

end

end ReciprocityTheory.ChartRestriction.G.Sh
end
end
