module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHom

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHomStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  first | exact @GlobalTheory.Katz.LawMonoid.mon | exact GlobalTheory.Katz.LawMonoid.mon | (intros; apply GlobalTheory.Katz.LawMonoid.mon <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMul

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :
    nmul μ 0 = fun _ => 0 := rfl

theorem nmul_succ' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem nmul_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul_zero']
  | succ n ih =>
    rw [nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ n) (fun i => X i) (fun _ => 0) ih
      (fun i => constantCoeff_X i) (fun _ => map_zero _)).1

theorem nmul_add (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nmul_zero']
    exact ((GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun _ => 0) (fun _ => 0)
      (nmul_const μ hμ m) (fun _ => map_zero _) (fun _ => map_zero _)).2.2.2.1).symm
  | succ n ih =>
    rw [← Nat.add_assoc, nmul_succ', ih, nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (nmul μ n) (fun i => X i)
      (nmul_const μ hμ m) (nmul_const μ hμ n) (fun i => constantCoeff_X i)).2.1

theorem nmul_one (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) :
    nmul μ 1 = fun i => X i := by
  rw [nmul_succ', nmul_zero']
  have h := GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (fun i => X i) (fun _ => 0) (fun _ => 0)
    (fun i => constantCoeff_X i) (fun _ => map_zero _) (fun _ => map_zero _)
  rw [← h.2.2.1, h.2.2.2.1]

theorem nmul_mul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    ∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i) := by
  have ha : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero (nmul_const μ hμ n)
  induction m with
  | zero =>
    intro i
    rw [Nat.zero_mul, nmul_zero']
    exact (map_zero (substAlgHom (R := R) ha)).symm.trans (by rw [coe_substAlgHom])
  | succ m ih =>
    intro i
    rw [Nat.succ_mul, nmul_add μ hμ, nmul_succ']
    rw [(GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun i => X i) (fun _ => 0)
      (nmul_const μ hμ m) (fun i => constantCoeff_X i) (fun _ => map_zero _)).2.2.2.2
      (Fin d) (nmul μ n) (nmul_const μ hμ n) i]
    have e1 : (fun j => subst (nmul μ n) (nmul μ m j)) = nmul μ (m * n) := funext fun j => (ih j).symm
    have e2 : (fun j => subst (nmul μ n) ((X j : MvPowerSeries (Fin d) R))) = nmul μ n :=
      funext fun j => subst_X ha j
    rw [e1, e2]

theorem nmul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧
      nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧
      (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i :=
  fun _ _ _ μ hμ m n => ⟨nmul_const μ hμ n, nmul_add μ hμ m n, nmul_mul μ hμ m n, nmul_one μ hμ⟩

end GlobalTheory.NMul
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLawsStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧ nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧ (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i := by
  first | exact @GlobalTheory.NMul.nmul_laws | exact GlobalTheory.NMul.nmul_laws | (intros; apply GlobalTheory.NMul.nmul_laws <;> assumption)
end
end
