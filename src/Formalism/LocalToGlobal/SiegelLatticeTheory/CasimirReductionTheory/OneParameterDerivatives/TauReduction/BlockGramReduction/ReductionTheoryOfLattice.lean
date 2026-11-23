module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ExistsMulMulConjTransposeEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.FreeQuotientRank
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Imports
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeFinitelyGeneratedOfCommensurable
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfFinitelyGenerated
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.PacketConditionsClosed
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.KsetInvMem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeVectorsBoundedBelow

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem one_le_norm_embedding_alt (I : AutInst) (a : 𝓞 I.E) (ha : a ≠ 0) :
    ∃ v, 1 ≤ ‖I.φ v (a : I.E)‖ := by
  set β : I.E := (a : I.E) * star (a : I.E) with hβ
  have hfix : star β = β := by simp [hβ, mul_comm]
  obtain ⟨γ, hγ⟩ := (I.cm.fixed β).1 hfix
  have haI : IsIntegral ℤ (a : I.E) := a.2
  have hsI : IsIntegral ℤ (star (a : I.E)) := IsIntegral.map I.cm.sig haI
  have hβI : IsIntegral ℤ β := haI.mul hsI
  have hγI : IsIntegral ℤ γ := by
    rw [← isIntegral_algebraMap_iff (B := I.E), hγ]
    exact hβI
  have ha0 : (a : I.E) ≠ 0 := by simpa using ha
  have hβ0 : β ≠ 0 := mul_ne_zero ha0 (star_ne_zero.2 ha0)
  let g : 𝓞 I.F := ⟨γ, hγI⟩
  have hg0 : g ≠ 0 := by
    intro h
    apply hβ0
    rw [← hγ]
    have : γ = 0 := congrArg Subtype.val h
    simp [this]
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace I.F, 1 ≤ w (g : I.F) := by
    by_contra h
    push Not at h
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w₀) hg0 (fun z _ => h z)) (not_le.2 (h w₀))
  refine ⟨w, ?_⟩
  have e : w (g : I.F) = ‖I.φ w (a : I.E)‖ ^ 2 := by
    rw [← InfinitePlace.norm_embedding_eq, show (g : I.F) = γ from rfl, ← I.φ_over, hγ, hβ, map_mul,
      I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj, sq]
  rw [e] at hw
  by_contra h
  push Not at h
  nlinarith [norm_nonneg (I.φ w (a : I.E))]

theorem lattice_common_denominator (I : AutInst) : ∃ b : 𝓞 I.E, b ≠ 0 ∧
    ∀ y ∈ I.L, ∀ i, ∃ c : 𝓞 I.E, (c : I.E) = (b : I.E) * y i := by
  first | exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator .. | (apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator I

theorem invertible_matrix_lower_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : Fin n → ℂ) (i : Fin n), ‖w i‖ ^ 2 ≤ C * ∑ k, ‖(A *ᵥ w) k‖ ^ 2 := by
  obtain ⟨U, rfl⟩ := hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  refine ⟨∑ i, ∑ k, ‖B i k‖ ^ 2 + 1, by positivity, fun w i => ?_⟩
  set z := (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w
  have hw : w = B *ᵥ z := by
    simp only [z, B, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : ‖w i‖ ≤ ∑ k, ‖B i k‖ * ‖z k‖ := by
    rw [hw]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 : ‖w i‖ ^ 2 ≤ (∑ k, ‖B i k‖ ^ 2) * ∑ k, ‖z k‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ k, ‖B i k‖ ^ 2 ≤ ∑ i, ∑ k, ‖B i k‖ ^ 2 + 1 := by
    have := Finset.single_le_sum (f := fun i => ∑ k, ‖B i k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))

theorem lattice_vectors_bounded_below (h0 : LatticeCommensurable) : LatticeVectorsBoundedBelow := by
  intro I x
  obtain ⟨m, hm1, hm, -⟩ := h0 I x
  obtain ⟨b, hb0, hb⟩ := lattice_common_denominator I
  have hC : ∀ v, ∃ C : ℝ, 0 < C ∧ ∀ (u : Fin I.n → I.E) (i : Fin I.n),
      ‖I.φ v (u i)‖ ^ 2 ≤ C * ∑ k, ‖coordV I x v u k‖ ^ 2 := fun v => by
    have hU : IsUnit (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) :=
      (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
    obtain ⟨C, hC, hCw⟩ := invertible_matrix_lower_bound _ hU
    exact ⟨C, hC, fun u i => hCw (fun i => I.φ v (u i)) i⟩
  choose C hCpos hCb using hC
  set K : ℝ := ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v :=
      Finset.sum_nonneg fun w _ => by have := hCpos w; positivity
    linarith
  refine ⟨1 / K, by positivity, ?_⟩
  intro u hu hu0
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨c, hc⟩ := hb _ (hm u hu) i
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0' : (b : I.E) ≠ 0 := by simpa using hb0
  have hc0 : c ≠ 0 := by
    intro h
    have : (c : I.E) = 0 := by simp [h]
    rw [hc, Pi.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero hb0' (mul_ne_zero hm0 hi) this
  obtain ⟨v, hv⟩ := one_le_norm_embedding_alt I c hc0
  have e : ‖I.φ v (c : I.E)‖ = ‖I.φ v (b : I.E)‖ * (m : ℝ) * ‖I.φ v (u i)‖ := by
    rw [hc, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_natCast, norm_mul, norm_mul,
      Complex.norm_natCast, mul_assoc]
  set S := ∑ w, ∑ k, ‖coordV I x w u k‖ ^ 2
  have hSv : ∑ k, ‖coordV I x v u k‖ ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => ∑ k, ‖coordV I x w u k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ v)
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := by
    have : 1 ≤ ‖I.φ v (c : I.E)‖ ^ 2 := by nlinarith
    rw [e] at this
    nlinarith
  have h2 : ‖I.φ v (u i)‖ ^ 2 ≤ C v * S := (hCb v u i).trans
    (mul_le_mul_of_nonneg_left hSv (hCpos v).le)
  have h3 : ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v ≤ K := by
    have := Finset.single_le_sum (f := fun w => ‖I.φ w (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C w)
      (fun w _ => by have := hCpos w; positivity) (Finset.mem_univ v)
    linarith
  have h4 : 1 ≤ K * S := by
    have hbm : 0 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 := by positivity
    calc 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := h1
      _ ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * (C v * S) := mul_le_mul_of_nonneg_left h2 hbm
      _ = (‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v) * S := by ring
      _ ≤ K * S := mul_le_mul_of_nonneg_right h3 hS0
  rw [div_le_iff₀ hK0]
  linarith

end Formalism.L2.SG.Pf.Tau
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T7

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Formalism.L2.SG.Pf.Tau

theorem t7 : InfimumContinuousFamily := by
  intro X _ S g hne hpos hloc
  have hbdd : ∀ x, BddBelow (Set.range (g x)) := fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩
  have hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s := fun x => by
    haveI := hne x
    exact le_ciInf fun s => hpos x s
  have key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s := by
    intro x y r hr h
    haveI := hne x
    rw [Real.mul_iInf_of_nonneg hr]
    exact le_ciInf fun s => by
      obtain ⟨s', hs'⟩ := h s
      exact (ciInf_le (hbdd y) s').trans hs'
  have hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b := by
    intro a b r hr hb hab
    rcases le_total b (1 / 2) with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hab
    · rw [min_eq_left h]
      nlinarith [min_le_left (1 / 2 : ℝ) a]
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hr : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [hloc x (1 + ε) hr] with x' hx'
  have h1 := hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)
  have h2 := hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)
  have hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2 := min_le_left _ _
  have hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s) := le_min (by norm_num) (hinf_nonneg x)
  have hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s) := le_min (by norm_num) (hinf_nonneg x')
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end Formalism.L2.SG.Pf.Tau
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ThirdEstimateOfFirstTwo

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.ReductionTauOf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem reductionTau_of (h3 : SubmoduleExists) (h6 : SizesLocallyComparable) (h7 : InfimumContinuousFamily)
    (h8 : MinkowskiSubmodule) (h9 : LatticeVectorsBoundedBelow) (h10 : HeightsPositive) : ReductionTau := by
  unfold Formalism.L2.SG.LitS.ReductionTau
  intro I hn
  refine ⟨?_, fun x => ?_⟩
  · exact h7 I.GA (Sub I) (fun x s => size I s) (fun x => h3 I hn x)
      (fun x s => Real.rpow_nonneg (h10 I x s).le _) (fun x r hr => h6 I x r hr)
  · obtain ⟨c, hc, hc8⟩ := h8 I
    obtain ⟨l, hl, hl9⟩ := h9 I x
    have hδ : ∀ s : Sub I x, Real.sqrt (l / c) ≤ size I s := by
      intro s
      obtain ⟨u, huB, hu0, hsum⟩ := hc8 x s
      have h1 := hl9 u (s.B_lat huB) hu0
      have hs0 : 0 ≤ size I s := Real.rpow_nonneg (h10 I x s).le _
      exact Real.sqrt_le_iff.2 ⟨hs0, (div_le_iff₀ hc).2 (by linarith)⟩
    haveI := h3 I hn x
    exact ⟨lt_min (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 (div_pos hl hc)) (le_ciInf hδ)),
      min_le_left _ _⟩

end Formalism.L2.SG.Pf.Tau
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ReductionTheoryOfLattice

section

@[expose] public section

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reduction_theory_of_lattice (h0 : LatticeCommensurable) (h8 : MinkowskiSubmodule) : ReductionTau :=
  reductionTau_of (third_estimate_of_first_two h0 (lattice_finitelyGenerated_of_commensurable h0)) (sizes_locally_comparable t4 t5) t7 h8 (lattice_vectors_bounded_below h0) (packet_conditions_closed (lattice_finitelyGenerated_of_commensurable h0) t2)

theorem reductionTau_of_minkowskiSubmodule (h8 : MinkowskiSubmodule) : ReductionTau :=
  reduction_theory_of_lattice t0 h8

end Formalism.L2.SG.Pf.Tau
end
end
