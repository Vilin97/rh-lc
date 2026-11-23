module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfParts
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.RemovableFinset
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Sheets
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Linter.Style

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.EsymmZero

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem esymmZero : esymmZeroStatement := by
  intro s hs a ha
  have h := Multiset.prod_X_add_C_eq_sum_esymm s
  have hR : ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j)
      = Polynomial.X ^ s.card := by
    rw [Finset.sum_eq_single 0]
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro j _ hj
      rw [hs j (Nat.one_le_iff_ne_zero.mpr hj)]
      simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  rw [hR] at h
  have h2 := congrArg (Polynomial.eval (-a)) h
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_pow, Polynomial.eval_X] at h2
  have h3 : (Multiset.map (Polynomial.eval (-a))
      (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s)).prod = 0 := by
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨a, ha, by simp⟩
  rw [h3] at h2
  exact neg_eq_zero.mp (pow_eq_zero_iff'.mp h2.symm).1

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.LineFinite

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem eval_line (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) (t : ℂ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ).eval t =
      polyAt n Δ (t • w) := by
  unfold polyAt
  induction Δ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.aeval_X,
      MvPolynomial.eval_X]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp
    ring

theorem lineFinite : lineFiniteStatement := by
  intro n Δ w h0
  have hne : MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ ≠ 0 := by
    intro hz
    apply h0
    have := eval_line n Δ w 0
    rw [hz] at this
    simpa using this.symm
  refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_line]
  exact ht

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.Section

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem holoSection : holoSectionStatement.{u} := by
  intro n M _ z f hz hf s w hs hzs
  obtain ⟨e, hxe, rfl⟩ := hz (s w)
  have hchart : IsChart n e e := fun _ _ => rfl
  have hw : e (s w) = w := hzs.self_of_nhds
  have htarget : e.target ∈ 𝓝 w := by
    rw [← hw]
    exact e.open_target.mem_nhds (e.map_source hxe)
  have hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source := hs (e.open_source.mem_nhds hxe)
  have heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s := by
    filter_upwards [hsrc, hzs] with v h1 h2
    simp only [Function.comp_apply]
    rw [show e.symm v = s v by rw [← e.left_inv h1, h2]]
  exact ((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmDiff_of_holoSection (hsec : holoSectionStatement.{u}) : symmDiffStatement.{u} := by
  intro n M _ z U u hcov hU hfinU hholo k w hw
  have hloc : IsLocalHomeomorph z := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have := hcov.isLocalHomeomorphOn
    rwa [Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)] at this
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w hw (hfinU w hw)
  have hWn : W ∈ 𝓝 w := hW.mem_nhds hwW
  have hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w := fun i =>
    hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn)
      (Filter.eventually_of_mem hWn (hzs i))
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  exact DifferentiableAt.fun_sum fun t _ => hprod t

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmGrowth

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmGrowth : symmGrowthStatement.{u} := by
  intro n M z u R δ hR hdeg k w
  have hfin : (z ⁻¹' {w}).Finite := Set.finite_of_encard_le_coe (hdeg w)
  have hcard : hfin.toFinset.card ≤ δ := by
    have := hdeg w
    rw [← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  unfold fiberSymm fiberVals
  rw [dite_eq_left hfin, Finset.esymm_map_val]
  have hB : 0 ≤ max (R w) 0 := le_max_right _ _
  have hu : ∀ y ∈ hfin.toFinset, ‖u y‖ ≤ max (R w) 0 := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    have hy' : z y = w := hy
    calc ‖u y‖ ≤ R (z y) := hR y
      _ = R w := by rw [hy']
      _ ≤ max (R w) 0 := le_max_left _ _
  calc ‖∑ t ∈ hfin.toFinset.powersetCard k, t.prod u‖
      ≤ ∑ t ∈ hfin.toFinset.powersetCard k, ‖t.prod u‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ hfin.toFinset.powersetCard k, (max (R w) 0) ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_powersetCard] at ht
        rw [norm_prod]
        calc ∏ y ∈ t, ‖u y‖ ≤ ∏ _y ∈ t, max (R w) 0 :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun y hy => hu y (ht.1 hy))
          _ = (max (R w) 0) ^ k := by rw [Finset.prod_const, ht.2]
    _ = ((hfin.toFinset.powersetCard k).card : ℝ) * (max (R w) 0) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ δ * (max (R w) 0) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB k)
        rw [Finset.card_powersetCard]
        have h1 := Nat.choose_le_two_pow hfin.toFinset.card k
        have h2 : 2 ^ hfin.toFinset.card ≤ 2 ^ δ := Nat.pow_le_pow_right (by norm_num) hcard
        exact_mod_cast h1.trans h2

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmVanish : symmVanishStatement.{u} := by
  intro n M _ z U u w₀ N hcov hw₀ hfin hvan k
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w₀ hw₀ hfin
  have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hwW
  have hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N := by
    intro i
    have hx : z (s i w₀) = w₀ := hzs i w₀ hwW
    have h1 := IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)
    refine h1.congr' (Eventually.of_forall fun v => rfl) ?_
    filter_upwards [hWn] with v hv
    simp only [Function.comp_apply, hzs i v hv, hx]
  have hprod : ∀ t : Finset (Fin d),
      (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))
    | insert a t ha ih =>
      have hc : (insert a t).card = t.card + 1 := by
        exact Finset.card_insert_of_notMem ha
      simp only [Finset.prod_insert ha]
      rw [hc]
      exact ((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl)
        (Eventually.of_forall fun v => by
          show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)
          rw [← pow_add]; congr 1; ring)
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w₀] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)
  refine IsBigO.fun_sum fun t ht => ?_
  have := hprod t
  rwa [(Finset.mem_powersetCard.mp ht).2] at this

end ReciprocityTheory.L2DbarEstimates.Norm
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
end
end
