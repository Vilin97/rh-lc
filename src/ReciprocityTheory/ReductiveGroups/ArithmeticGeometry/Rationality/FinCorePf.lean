module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscPf
public import ReciprocityTheory.SemistableReduction.ExistsTorusPointOneLeNormSum
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.UnitPointLiftBall

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall

open MvPolynomial ReciprocityTheory.MultiplicativeHeights

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι]

lemma lift_ball (P : MvPolynomial ι K) (hP : ∀ μ, ‖AddMonoidAlgebra.coeff P μ‖ ≤ 1) :
    ∃ PO : MvPolynomial ι (unitBallRing K), MvPolynomial.map (unitBallRing K).subtype PO = P := by
  have hmem : P ∈ Set.range (MvPolynomial.map (unitBallRing K).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨μ, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    refine ⟨⟨AddMonoidAlgebra.coeff P μ, ?_⟩, rfl⟩
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact_mod_cast hP μ
  obtain ⟨PO, hPO⟩ := hmem
  exact ⟨PO, hPO⟩

lemma eval_lift (PO : MvPolynomial ι (unitBallRing K)) (σ : ι → unitBallRing K) :
    eval (fun i => (σ i : K)) (MvPolynomial.map (unitBallRing K).subtype PO) =
      ((eval σ PO : unitBallRing K) : K) := by
  induction PO using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem exists_unit_point (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K))
    (P δ : MvPolynomial ι K) (hP : ∀ μ, ‖AddMonoidAlgebra.coeff P μ‖ ≤ 1) (hP1 : ∃ μ, ‖AddMonoidAlgebra.coeff P μ‖ = 1)
    (hδ : ∀ μ, ‖AddMonoidAlgebra.coeff δ μ‖ ≤ 1) (hδ1 : ∃ μ, ‖AddMonoidAlgebra.coeff δ μ‖ = 1) :
    ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ = 1) ∧ ‖eval x P‖ = 1 ∧ ‖eval x δ‖ = 1 := by
  classical
  obtain ⟨PO, hPO⟩ := lift_ball P hP
  obtain ⟨δO, hδO⟩ := lift_ball δ hδ
  have mem_le : ∀ a : unitBallRing K, ‖(a : K)‖ ≤ 1 := fun a => by
    have h := a.2
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply] at h
    exact_mod_cast h
  have unit_of_norm : ∀ a : unitBallRing K, ‖(a : K)‖ = 1 → IsUnit a := by
    intro a ha
    have ha0 : (a : K) ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (a : K)⁻¹ ∈ unitBallRing K := by
      rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
      have h1 : ‖(a : K)⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      exact_mod_cast h1.le
    have hm : a * ⟨_, hinv⟩ = 1 := Subtype.ext (by simp [ha0])
    first
      | exact IsUnit.of_mul_eq_one _ hm
      | exact IsUnit.of_mul_eq_one hm
      | exact ⟨⟨a, ⟨_, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have norm_of_unit : ∀ a : unitBallRing K, IsUnit a → ‖(a : K)‖ = 1 := by
    intro a ha
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have h1 : (a : K) * (b : K) = 1 := by
      have := congrArg (fun z : unitBallRing K => (z : K)) hb
      simpa using this
    have hn : ‖(a : K)‖ * ‖(b : K)‖ = 1 := by rw [← norm_mul, h1, norm_one]
    have ha1 := mem_le a
    have hb1 := mem_le b
    refine le_antisymm ha1 ?_
    nlinarith [norm_nonneg (a : K), norm_nonneg (b : K)]
  have hcoeff : ∀ (Q : MvPolynomial ι (unitBallRing K)) (R : MvPolynomial ι K),
      MvPolynomial.map (unitBallRing K).subtype Q = R → ∀ μ, ((AddMonoidAlgebra.coeff Q μ : unitBallRing K) : K) = AddMonoidAlgebra.coeff R μ := by
    intro Q R hQR μ
    rw [← hQR, MvPolynomial.coeff_map]
    rfl
  have hres_eval : ∀ (Q : MvPolynomial ι (unitBallRing K)) (u : ι → unitBallRing K),
      IsLocalRing.residue (unitBallRing K) (eval u Q) =
        eval (fun i => IsLocalRing.residue (unitBallRing K) (u i))
          (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) Q) := by
    intro Q u
    induction Q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hbar : ∀ (Q : MvPolynomial ι (unitBallRing K)) (R : MvPolynomial ι K),
      MvPolynomial.map (unitBallRing K).subtype Q = R → (∃ μ, ‖AddMonoidAlgebra.coeff R μ‖ = 1) →
        MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) Q ≠ 0 := by
    intro Q R hQR hR h0
    obtain ⟨μ, hμ⟩ := hR
    have h := congrArg (AddMonoidAlgebra.coeff · μ) h0
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
      (unit_of_norm _ (by rw [hcoeff Q R hQR μ]; exact hμ)) h
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
      MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO ≠ 0 :=
    mul_ne_zero (hbar PO P hPO hP1) (hbar δO δ hδO hδ1)
  obtain ⟨S0, hS0T, hS0c⟩ := (infinite_residues K₀ hK₀).exists_subset_card_eq
    ((MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
      MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO).totalDegree + 1)
  have hex : ∃ y : ι → IsLocalRing.ResidueField (unitBallRing K), (∀ i, y i ∈ S0) ∧
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) PO *
        MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) δO) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => S0)
      (fun i => lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree _ i) (by rw [hS0c]; omega)) hcon)
  obtain ⟨y, hyS, hyQ⟩ := hex
  have hlift : ∀ i, ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧
      IsLocalRing.residue (unitBallRing K) x = y i := fun i => hS0T (Finset.mem_coe.2 (hyS i))
  choose u hu0 hu1 hu2 using hlift
  have hy : (fun i => IsLocalRing.residue (unitBallRing K) (u i)) = y := funext hu2
  rw [map_mul] at hyQ
  refine ⟨fun i => (u i : K), fun i => ⟨hu0 i, hu1 i⟩, ?_, ?_⟩
  · rw [← hPO, eval_lift]
    apply norm_of_unit
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres_eval, hy]
    exact left_ne_zero_of_mul hyQ
  · rw [← hδO, eval_lift]
    apply norm_of_unit
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres_eval, hy]
    exact right_ne_zero_of_mul hyQ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCorePf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finCore_holds : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖AddMonoidAlgebra.coeff p μ‖ ∧
        AddMonoidAlgebra.coeff p μ ≠ 0 ∧ ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖AddMonoidAlgebra.coeff p ν‖) hne
    have hc : AddMonoidAlgebra.coeff p μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : AddMonoidAlgebra.coeff p ν = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖AddMonoidAlgebra.coeff p μ‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p ν‖
          ≤ ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p μ‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = AddMonoidAlgebra.coeff p μ *
        MvPolynomial.eval x (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push Not at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
end
