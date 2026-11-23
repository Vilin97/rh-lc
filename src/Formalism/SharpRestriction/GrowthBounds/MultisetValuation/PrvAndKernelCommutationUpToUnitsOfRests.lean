module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AofUpdate
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CommonEigenvectorThird
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbBrJet
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FirstTheoremPlaceBound
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeConditionOfAdm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LiftBoundOfIntegrality
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RelativePresentationOfD7
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelProductForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestrictedHeckeIntegralOfEdges
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulPsiGUp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem Tm_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tm v i J (F + F') = X.Tm v i J F + X.Tm v i J F' := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (F c + F' c) L =
    (X.Pj J).Tminus (X.vJ J v) i (F c) L + (X.Pj J).Tminus (X.vJ J v) i (F' c) L
  rw [tm_eq, tm_eq, tm_eq, ← Finset.sum_add_distrib]
  rfl

theorem Tm_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tm v i J (a • F) = a • X.Tm v i J F := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (a • F c) L = a • (X.Pj J).Tminus (X.vJ J v) i (F c) L
  rw [tm_eq, tm_eq, Finset.smul_sum]
  rfl

theorem Tt_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tt v i J (F + F') = X.Tt v i J F + X.Tt v i J F' := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_add, smul_add]

theorem Tt_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tt v i J (a • F) = a • X.Tt v i J F := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_smul, smul_comm]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_PhAt_const (hbe : BeProp p Y.be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (Y.PhAt j v) = 0 := by
  unfold Pend.PhAt

  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

theorem kernel_product_form (D : Formalism.BasicNotions.D7) : KernelProductForm X Y D := by
  intro hA j hj La La' h1 h2 φ
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p Y.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, Y.PhAt j v := by
    unfold Pend.PhAt
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, Y.PhAt j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-(Ph - ∑ v, Y.PhAt j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, Y.PhAt j v))) = expK (inParam p (-(Ph - ∑ v, Y.PhAt j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) Y.Kc, ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact Y.witt_mem_integers_Cp _
  · have e2 : -Ph = ∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-Y.PhAt j v)) * expS p (-(Ph - ∑ v, Y.PhAt j v)) := by
      have a1 : expK (∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)) =
          expK (∑ v, (-Y.PhAt j v)) * expK (-(Ph - ∑ v, Y.PhAt j v)) :=
        expK_add (by

          rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-Y.PhAt j v)) = ∏ v, expK (-Y.PhAt j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

theorem restPlaces (D : Formalism.BasicNotions.D7) : RestPlaces X Y D := restPlaces_of D (kernel_product_form X Y D)

theorem restEnt_of (D : Formalism.BasicNotions.D7) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D) (hA : admitted D X Y) : EntCondition X Y :=
  restEnt_of_rest D (restPlaces X Y D) h2 hB hA

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TsumRatTail

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

theorem tsum_rat_tail (g : ℕ → ℚ) (hs : Summable (fun e => (g e : ℝ))) (E N : ℕ) (Q : ℚ) (hQ1 : 1 < Q)
    (h4 : ∀ e, E ≤ e → g (e + N) = g e / Q) : ∃ q : ℚ, ∑' e, (g e : ℝ) = q := by
  have hsE : Summable (fun i => (g (i + E) : ℝ)) := (summable_nat_add_iff E).2 hs
  have h1 := hsE.sum_add_tsum_nat_add N
  have h2 : ∀ i, (g (i + N + E) : ℝ) = (g (i + E) : ℝ) / Q := by
    intro i
    rw [show i + N + E = i + E + N by omega, h4 (i + E) (by omega)]
    push_cast
    try rfl
  simp only [h2] at h1
  rw [tsum_div_const] at h1
  have h0 := hs.sum_add_tsum_nat_add E
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hQ1' : (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hT : ∑' i, (g (i + E) : ℝ) = (∑ i ∈ range N, (g (i + E) : ℝ)) * Q / (Q - 1) := by
    rw [eq_div_iff hQ1']
    field_simp at h1
    linarith
  refine ⟨∑ i ∈ range E, g i + (∑ i ∈ range N, g (i + E)) * Q / (Q - 1), ?_⟩
  rw [← h0, hT]
  push_cast
  ring

def fqT (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) : ℚ :=
  if 2 * e + 1 ∈ Ds then 0 else max ((α : ℚ) / (P : ℚ) ^ (2 * e + 1) - (c e : ℚ)) 0

theorem fqT_cast (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) :
    (if 2 * e + 1 ∈ Ds then (0 : ℝ) else max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) =
      (fqT P α c Ds e : ℝ) := by
  unfold fqT
  split_ifs
  · simp
  · push_cast
    try rfl

theorem tsum_rat (P N : ℕ) (hP : 2 ≤ P) (hN : 0 < N) (α : ℤ) (c : ℕ → ℤ) (hc : ∀ e, c (e + N) = c e)
    (Ds : Finset ℕ) :
    ∃ q : ℚ, ∑' e : ℕ, (if 2 * e + 1 ∈ Ds then (0 : ℝ) else
      max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) = q := by
  simp_rw [fqT_cast]
  by_cases hs : Summable (fun e => (fqT P α c Ds e : ℝ))
  swap
  · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs]; simp⟩
  have hP0 : (0 : ℚ) < P := by exact_mod_cast (by omega : 0 < P)
  have h1 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 2 * e + 1 ∉ Ds := fun e he hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have h2 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ)| * 2 < (P : ℚ) ^ (2 * e + 1) := by
    intro e he
    have a1 : α.natAbs * 2 < P ^ (2 * e + 1) :=
      calc α.natAbs * 2 < 2 * e + 1 := by omega
        _ < 2 ^ (2 * e + 1) := Nat.lt_two_pow_self
        _ ≤ P ^ (2 * e + 1) := Nat.pow_le_pow_left hP _
    have a2 : ((α.natAbs : ℕ) : ℚ) = |(α : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← a2]
    exact_mod_cast a1
  have h2' : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ) / (P : ℚ) ^ (2 * e + 1)| < 1 / 2 := by
    intro e he
    have hpos : (0 : ℚ) < (P : ℚ) ^ (2 * e + 1) := pow_pos hP0 _
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith [h2 e he]
  have hcK : ∀ k e, c (e + k * N) = c e := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih => intro e; rw [Nat.succ_mul, ← add_assoc, hc, ih]
  have h3 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 0 ≤ c e := by
    intro e0 he0
    by_contra hneg
    have hneg : c e0 ≤ -1 := by omega
    have tend := hs.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hge : M ≤ e0 + M * N := by nlinarith
    have hlt : (fqT P α c Ds (e0 + M * N) : ℝ) < 1 / 2 := hM _ hge
    have hlt' : fqT P α c Ds (e0 + M * N) < 1 / 2 := by
      have : (fqT P α c Ds (e0 + M * N) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hlt
      exact Rat.cast_lt.1 this
    have hE1 : Ds.sup id + α.natAbs + 1 ≤ e0 + M * N := le_trans he0 (Nat.le_add_right _ _)
    unfold fqT at hlt'
    rw [if_neg (h1 _ hE1), hcK] at hlt'
    have b1 := abs_lt.1 (h2' _ hE1)
    have b2 : ((c e0 : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hneg
    have b3 := le_max_left ((α : ℚ) / (P : ℚ) ^ (2 * (e0 + M * N) + 1) - (c e0 : ℚ)) 0
    linarith [b1.1]
  have h4 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e →
      fqT P α c Ds (e + N) = fqT P α c Ds e / (P : ℚ) ^ (2 * N) := by
    intro e he
    have he' : Ds.sup id + α.natAbs + 1 ≤ e + N := le_trans he (Nat.le_add_right _ _)
    unfold fqT
    rw [if_neg (h1 _ he), if_neg (h1 _ he'), hc]
    have hQ : (0 : ℚ) < (P : ℚ) ^ (2 * N) := pow_pos hP0 _
    rcases (h3 e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp only [Int.cast_zero, sub_zero]
      have : (α : ℚ) / (P : ℚ) ^ (2 * (e + N) + 1) = (α : ℚ) / (P : ℚ) ^ (2 * e + 1) / (P : ℚ) ^ (2 * N) := by
        rw [div_div, ← pow_add]
        congr 2
        ring
      rw [this, ← max_div_div_right hQ.le, zero_div]
    · have b2 : (1 : ℚ) ≤ ((c e : ℤ) : ℚ) := by exact_mod_cast h0
      have c1 := abs_lt.1 (h2' _ he)
      have c2 := abs_lt.1 (h2' _ he')
      rw [max_eq_right (by linarith [c2.2]), max_eq_right (by linarith [c1.2]), zero_div]
  have hQ1 : (1 : ℚ) < (P : ℚ) ^ (2 * N) := by
    have : (1 : ℚ) < P := by exact_mod_cast (by omega : 1 < P)
    exact one_lt_pow₀ this (by omega)
  exact tsum_rat_tail _ hs _ N _ hQ1 h4

theorem gA_rat {n' k1 : ℕ} (p t : ℕ) (hp : 2 ≤ p) (hn : 0 < n') (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ∃ q : ℚ, gA p t TT lam0 w j = q := by
  have h1 : ∀ s : Fin n', ∃ q : ℚ, ∑' e : ℕ,
      (if 2 * e + 1 ∈ dSet TT s then (0 : ℝ) else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) = q := by
    intro s
    apply tsum_rat p n' hp hn (al TT lam0 s) (fun e => cap t TT lam0 w j (posAdd s (2 * e + 1))) _ (dSet TT s)
    intro e
    have : posAdd s (2 * (e + n') + 1) = posAdd s (2 * e + 1) := by
      unfold posAdd
      apply Fin.ext
      show (s.val + (2 * (e + n') + 1)) % n' = (s.val + (2 * e + 1)) % n'
      have : s.val + (2 * (e + n') + 1) = s.val + (2 * e + 1) + 2 * n' := by ring
      rw [this, Nat.add_mul_mod_self_right]
    simp only [this]
  choose q hq using h1
  refine ⟨∑ s ∈ TT, q s - (∑ s : Fin n', ((NN k1 t j : ℚ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℚ) * (NN k1 t j : ℚ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℚ)) ^ 2), ?_⟩
  unfold gA de
  simp only [hq]
  push_cast
  ring

theorem restRat {p : ℕ} [Fact p.Prime] (X : Sys p) : RatCondition X := by
  intro v j
  have h := X.std v
  exact gA_rat p X.t (by have := h.five_le; omega) (by have := h.two_le; omega) _ _ _ j

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrvAndKernelCommutationUpToUnitsOfRests

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem linD (X : Sys p) : LinD X :=
  { Tt_add := Tt_add X
    Tt_smul := Tt_smul X
    yv_add := fun v F F' => (yvLin X v).map_add F F'
    yv_smul := fun v a F => (yvLin X v).map_smul a F
    yv_comm := fun v v' F =>
      funext fun i => Formalism.MainNotions.G.LatticeSystems.ef_yv_comm X.G.P v v' (F i) }

variable {X : Sys p}

theorem vGe_of_eO_zero (he : X.eO = 0) {j : ℕ} {F : X.Fm j} {g g' : ℝ} (h : X.vGe j F g) : X.vGe j F g' := by
  unfold Sys.vGe Sys.vsc at h ⊢
  simpa [he] using h

theorem low_term_bound_of_eO_eq_zero_of_aux0 (D : Formalism.BasicNotions.D7) (Y : Pend X) (he : X.eO = 0) (h0 : Conclusion0 D X) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV _ _ _ _ F hFm
  have hPl : ∀ _ : X.Pl, False := fun v => by have := eO_pos X v; omega
  have hFint : F ∈ X.Int 0 := by
    unfold Sys.Iprod at hFm
    refine (Submodule.span_le.2 ?_) hFm
    rintro F' ⟨BB, _, Lv, _, _, F0, hF0, rfl⟩
    have hLv : Lv = [] := by
      cases Lv with
      | nil => rfl
      | cons v _ => exact (hPl v).elim
    subst hLv
    have h1 : F0 ∈ scale (1 : X.G.Kf) (X.Int 0) := by simpa [he] using hF0
    rw [scale_one] at h1
    exact h1
  have key : ∀ m' ≤ X.mm, X.chainK m' F ∈ X.Int m' := by
    intro m'
    induction m' with
    | zero => intro _; exact hFint
    | succ n ih =>
      intro h
      have := h0 n (by omega) _ (ih (by omega))
      exact (vGe_zero_iff X).1 (vGe_of_eO_zero he this)
  exact vGe_of_eO_zero he ((vGe_zero_iff X).2 (key X.mm le_rfl))

structure Rests (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Prop where

  S1 : Conclusion1 D X Y

  allPlacesExpansion : ExpansionsMultiply D X Y

  U2 : VolumeRatio₂ D X Y

  Ent : EntCondition X Y

theorem prv_and_kernel_commutation_up_to_units_of_rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) (R : Rests D X Y) :
    Conclusion₂ D X Y ∧ KernelCommutationUpToUnits D X := by
  have hF : FormB X Y := formB D X Y hA
  have hH : RestHecke X := heckeCondition_of_adm D X Y hA countLoc (restTmFQ X)
  obtain ⟨_, _, _, _, h3, h3b, _, _, _, _, _, h8, _⟩ := hA
  have p2b := hecke_integral_of_forms D hF R.Ent R.U2
  have p3 := latticeChain_succ_of_partial D hF R.Ent R.U2 (restricted_hecke_integral X)
  have pAlt := alternate_expansion_of_relations X D hH (restTmFQ X) h3b p3 p2b
  have p4 := theorem_of_alternate_form X D pAlt
  have p5D : LowTermBound D X Y := by
    rcases Nat.eq_zero_or_pos X.eO with he | he
    · exact low_term_bound_of_eO_eq_zero_of_aux0 D Y he (form_valuation_of_bound D hF h3)
    · exact lift_bound_of_integrality D (isFractionRing_of_pos_eO Y he) (pKf_ne Y) (linD X) hF R.Ent p4
        (fun v F hFm => h8.2 v F hFm)
  exact ⟨⟨form_valuation_of_bound D hF h3, R.S1, R.allPlacesExpansion, slopeEstimate_of_lemmaB_slopeLine D hF R.Ent R.U2, theorem_A_entries_of_corollary D R.Ent (restRat X) R.U2, R.U2, p2b, p3, p4,
    ramifiedLattice_of_chain_estimates D R.U2 p5D, p5D⟩, pAlt⟩

theorem rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Rests D X Y :=
  { S1 := theta_kernel_expansion D X Y hA
    allPlacesExpansion := expansions_multiply D X Y hA
    U2 := auxU_of_firstTheoremPlaceBound D (first_theorem_place_bound X Y D (restGc p) (eb_brJet X)) hA
    Ent := restEnt_of X Y D (second_lemma_place_bound X Y D (restGc p) (eb_brJet X))
      (hecke_place_bound X Y D (restGc p) (eb_brJet X)) hA }

theorem packet_statements_hold (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Conclusion₂ D X Y :=
  (prv_and_kernel_commutation_up_to_units_of_rests D Y hA (rests D Y hA)).1

theorem stmt_proved (D : Formalism.BasicNotions.D7) : Stmt D :=
  ⟨fun _ _ _ Y hA => packet_statements_hold D Y hA, relative_presentation_of_d7 D⟩

theorem stmtAt_proved (D : Formalism.BasicNotions.D7) : ErrorExponentStatement D :=
  fun _ _ _ _ _ Y _ hA => packet_statements_hold D Y hA

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
end
