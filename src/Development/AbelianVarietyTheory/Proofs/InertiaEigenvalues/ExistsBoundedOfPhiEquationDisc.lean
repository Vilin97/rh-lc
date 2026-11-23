module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmall
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmallStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  first | exact @GlobalTheory.BSP.norm_toDisc_J_pow_small | exact GlobalTheory.BSP.norm_toDisc_J_pow_small | (intros; apply GlobalTheory.BSP.norm_toDisc_J_pow_small <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStep

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem norm_pow_mul_eq_of_norm_mul_eq {R : Type*} [NormedRing R] (E : R) (q : ℝ)
    (hE : ∀ y, ‖E * y‖ = q * ‖y‖) (h : ℕ) (y : R) : ‖E ^ h * y‖ = q ^ h * ‖y‖ := by
  induction h generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, hE, pow_succ]; ring

theorem exists_discStep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  intro l _ K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV ρ ρ' hρ₀ hρ1 hρ' R R' hR hR' U C hC hU hRU hUC
  obtain ⟨-, -, ⟨hρ₀pos, hρ₀1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hρpos : 0 < ρ := hρ₀pos.trans_le hρ₀
  have hρ'pos : 0 < ρ' := by
    rcases (show (0 : ℝ≥0) ≤ ρ' from zero_le).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow (by omega)] at hρ'
      exact absurd hρ' hρpos.ne
    · exact h0
  have hρ'1 : ρ' < 1 := by
    by_contra hh
    push_neg at hh
    have h2 := one_le_pow₀ hh (n := l)
    rw [hρ'] at h2
    exact absurd hρ1 (not_lt.2 h2)
  have hρρ' : ρ ≤ ρ' := by rw [← hρ']; exact pow_le_of_le_one zero_le hρ'1.le (by omega)

  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A φ (s X) (s X) ρ ρ' l hρ'pos (by rw [hφ]) hρ'.le
  have hc1 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) ρ' bk.ρ₀ φ (RingHom.id A) Φ' R' hΦ' hR'
  have hc2 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) bk.ρ₀ bk.ρ₀ (RingHom.id A) φ R Φ hR hΦ
  rw [RingHom.id_comp] at hc1
  rw [RingHom.comp_id] at hc2
  have hcomm : ∀ x, R' (Φ' x) = Φ (R x) := fun x => RingHom.congr_fun (hc1.unique hc2) x
  haveI : IsUltrametricDist (Disc l (s X) ρ') := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').1
  haveI : NonarchimedeanAddGroup (Disc l (s X) ρ') := IsUltrametricDist.nonarchimedeanAddGroup

  have hUn : Filter.Tendsto (fun i => ‖U i‖) Filter.cofinite (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.1 hU
  have hTle : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ * ‖toDisc l (s X) ρ' (c i j)‖ := fun i j =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hΦ'.norm_le _) (norm_nonneg _))
  have hTle' : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ := fun i j =>
    (hTle i j).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_toDisc_le _))
  have hsum : ∀ j, Summable fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j) := fun j =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (squeeze_zero_norm (fun i => hTle' i j) hUn)
  set Z : κ → Disc l (s X) ρ' := fun j => ∑' i, Φ' (U i) * toDisc l (s X) ρ' (c i j) with hZdef
  have hZC : ∀ j, ‖Z j‖ ≤ C := fun j =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun i => (hTle' i j).trans (hUC i)
  have hR'c : Continuous R' :=
    AddMonoidHomClass.continuous_of_bound R' 1 fun y => (hR'.norm_le y).trans (one_mul _).ge
  have hRZ : ∀ j, R' (Z j) = toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j := fun j => by
    have h1 := (hsum j).hasSum.map R' hR'c
    have h2 : (R' ∘ fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j)) =
        fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j) := by
      funext i
      simp only [Function.comp_apply, map_mul, hcomm, hRU, hR'.ext, RingHom.id_apply]
    rw [h2] at h1
    exact h1.unique (hV j)

  have hsmall : ∀ r : ℝ, 0 < r → {j | r < ‖Z j‖}.Finite := by
    intro r hr
    have hF : {i | r < ‖U i‖}.Finite := by
      have := Filter.eventually_cofinite.1 (hUn.eventually (ge_mem_nhds hr))
      simpa only [not_le] using this
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small l K bk A s ρ' hρ'pos hρ'1 (r / (C + 1)) (by positivity)
    refine (hF.biUnion fun i _ => hc i n).subset ?_
    intro j hj
    by_contra hj'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hj'
    refine (not_le.2 (show r < ‖Z j‖ from hj)) ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr.le fun i => ?_
    by_cases hi : r < ‖U i‖
    · refine (hTle i j).trans ((mul_le_mul (hUC i) (hn _ (hj' i hi)) (norm_nonneg _) hC).trans ?_)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    · exact (hTle' i j).trans (not_lt.1 hi)
  have hZ : Filter.Tendsto Z Filter.cofinite (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_cofinite.2 ((hsmall (ε / 2) (by linarith)).subset ?_)
    intro j hj
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hj ⊢
    linarith

  obtain ⟨hnorm', hdiv'⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb ρ' (hρ₀.trans hρρ') hρ'1
  obtain ⟨hnorm₀, -⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb bk.ρ₀ le_rfl hρ₀1
  choose U' hU' using fun j => hdiv' R' hR' h (Z j) ⟨V j, hRZ j⟩
  have hq : (0 : ℝ) < (ρ' : ℝ) ^ (bk.Ep.natDegree * h) := by positivity
  have hnZ : ∀ j, ‖Z j‖ = (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ := fun j => by
    rw [hU' j, norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm' h, pow_mul]
  refine ⟨U', ?_, ?_, fun j => (hnZ j).symm.trans_le (hZC j)⟩
  · have he : ∀ j, ‖U' j‖ = ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹ * ‖Z j‖ := fun j => by
      rw [hnZ j, inv_mul_cancel_left₀ hq.ne']
    refine squeeze_zero_norm (fun j => (he j).le) ?_
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hZ).const_mul ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹
  · intro j
    have h1 : toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * (R' (U' j) - V j) = 0 := by
      have h2 := hRZ j
      rw [hU' j, map_mul, map_pow, hR'.ext, RingHom.id_apply] at h2
      rw [mul_sub, h2, sub_self]
    have h3 := congrArg norm h1
    rw [norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm₀ h, norm_zero] at h3
    have h4 : (0 : ℝ) < ((bk.ρ₀ : ℝ) ^ bk.Ep.natDegree) ^ h := by positivity
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4.ne'))

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStepStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_phiContraction_disc_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  first | exact @GlobalTheory.BSP.exists_discStep | exact GlobalTheory.BSP.exists_discStep | (intros; apply GlobalTheory.BSP.exists_discStep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_root_radii (l : ℕ) (hl : 2 ≤ l) (ρ₀ : ℝ≥0) (h0 : 0 < ρ₀) (h1 : ρ₀ < 1) :
    ∃ r : ℕ → ℝ≥0, r 0 = ρ₀ ∧ (∀ n, r (n + 1) ^ l = r n) ∧ (∀ n, ρ₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      ∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ n, ρ₁ ≤ r n := by
  have hl0 : l ≠ 0 := by omega
  let r : ℕ → ℝ≥0 := fun n => ρ₀ ^ (((l ^ n : ℕ) : ℝ)⁻¹)
  have hp : ∀ n, r n ^ (l ^ n) = ρ₀ := fun n => NNReal.rpow_inv_natCast_pow _ (pow_ne_zero _ hl0)
  have hlt : ∀ n, r n < 1 := fun n => by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := l ^ n)
    rw [hp] at this
    exact absurd h1 (not_lt.2 this)
  refine ⟨r, by simpa using hp 0, fun n => ?_, fun n => ?_, hlt, fun ρ₁ h => ?_⟩
  · refine (pow_left_inj₀ zero_le zero_le (pow_ne_zero n hl0)).1 ?_
    rw [← pow_mul, ← pow_succ', hp, hp]
  · rw [← hp n]
    exact pow_le_of_le_one zero_le (hlt n).le (pow_ne_zero _ hl0)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 h
    refine ⟨n, le_of_lt (lt_of_pow_lt_pow_left₀ (l ^ n) zero_le ?_)⟩
    rw [hp]
    exact (pow_le_pow_of_le_one zero_le h.le (Nat.lt_pow_self (by omega)).le).trans_lt hn

theorem norm_l_pow_mul_disc (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (k : ℕ)
    (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) ^ k * y‖ = ‖y‖ / (l : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A u ρ).2.1, ih, div_div, pow_succ]

theorem exists_bounded_of_phi_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  intro l hl K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV hs
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl2 := hl.out.two_le
  obtain ⟨r, r0, rs, rle, rlt, rlim⟩ := exists_root_radii l hl2 bk.ρ₀ h0 h1
  have rpos : ∀ n, 0 < r n := fun n => h0.trans_le (rle n)
  have hR : ∀ n, ∃ R : Disc l (s X) (r n) →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R := fun n =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A (RingHom.id A) (s X) (s X) (r n) bk.ρ₀ 1 h0 (by simp) (by simpa using rle n)
  choose R hR using hR
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖V j‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto_cofinite hV)
    exact ⟨max C 0, le_max_right _ _, fun j => (hC _ ⟨j, rfl⟩).trans (le_max_left _ _)⟩
  set m := bk.Ep.natDegree * h with hm
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have key : ∀ n, ∃ U : κ → Disc l (s X) (r n), Filter.Tendsto U Filter.cofinite (nhds 0) ∧
      (∀ j, R n (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((r n : ℝ) / bk.ρ₀) ^ m := by
    intro n
    induction n with
    | zero =>
      have gen : ∀ (ρ : ℝ≥0) (R₀ : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀), ρ = bk.ρ₀ →
          IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R₀ → ∃ U : κ → Disc l (s X) ρ, Filter.Tendsto U Filter.cofinite (nhds 0) ∧
          (∀ j, R₀ (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((ρ : ℝ) / bk.ρ₀) ^ m := by
        rintro ρ R₀ rfl hR₀
        refine ⟨V, hV, fun j => ?_, fun j => ?_⟩
        · rw [hR₀.unique (isDiscMap_id l (s X) bk.ρ₀)]; rfl
        · rw [div_self h0'.ne', one_pow, mul_one]; exact hC j
      exact gen _ _ r0 (hR 0)
    | succ n ih =>
      obtain ⟨U, hU, hRU, hn⟩ := ih
      obtain ⟨U', hU', hRU', hn'⟩ := GlobalTheory.T.exists_phiContraction_disc_step l K bk A s ι tb φ hφ Φ hΦ κ c hc h V hs (r n) (r (n + 1))
        (rle n) (rlt n) (rs n) (R n) (R (n + 1)) (hR n) (hR (n + 1)) U _ (by positivity) hU hRU hn
      refine ⟨U', hU', hRU', fun j => ?_⟩
      have hp : (0 : ℝ) < r (n + 1) := rpos _
      have hle : (r n : ℝ) ≤ r (n + 1) * r (n + 1) := by
        have : r n ≤ r (n + 1) ^ 2 := by
          rw [← rs n]; exact pow_le_pow_of_le_one zero_le (rlt _).le hl2
        rw [← sq]; exact_mod_cast this
      refine le_of_mul_le_mul_left ((hn' j).trans ?_) (pow_pos hp m)
      rw [mul_left_comm, ← mul_pow, ← mul_div_assoc]
      gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (1 / (bk.ρ₀ : ℝ)) ^ m)
    (show (1 : ℝ) < l by exact_mod_cast hl.out.one_lt)
  have hlk : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hl.out.pos) k
  have hv : ∀ j, ∃ a, toDisc l (s X) bk.ρ₀ a = (l : Disc l (s X) bk.ρ₀) ^ k * V j := fun j =>
    GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one l K bk A s ι tb bk.ρ₀ h0 h1 _ fun ρ₁ hρ₁ => by
      obtain ⟨n, hn⟩ := rlim ρ₁ hρ₁
      obtain ⟨U, -, hRU, hU⟩ := key n
      refine ⟨r n, R n, (l : Disc l (s X) (r n)) ^ k * U j, hn, rle n, rlt n, hR n, ?_, ?_⟩
      · rw [map_mul, map_pow, map_natCast, hRU]
      · rw [norm_l_pow_mul_disc, div_le_one hlk]
        refine (hU j).trans (le_trans ?_ hk.le)
        have : (r n : ℝ) ≤ 1 := (rlt n).le
        gcongr
  choose v hv using hv
  refine ⟨k, v, hv, fun n => ?_⟩
  obtain ⟨ε, hε, hJ⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι tb bk.ρ₀ h0 h1).2.1 n
  have ht : Filter.Tendsto (fun j => (l : Disc l (s X) bk.ρ₀) ^ k * V j) Filter.cofinite (nhds 0) := by
    simpa using hV.const_mul ((l : Disc l (s X) bk.ρ₀) ^ k)
  have he := Filter.eventually_cofinite.1 (ht.eventually (Metric.closedBall_mem_nhds 0 hε))
  refine he.subset fun j hj hj' => hj (hJ _ ?_)
  rw [hv]
  simpa using hj'

end GlobalTheory.BSP
end
end
