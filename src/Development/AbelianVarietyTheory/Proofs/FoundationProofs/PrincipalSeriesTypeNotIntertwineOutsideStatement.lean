module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbation
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruence

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem corner_val_le_one {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) : valuation k (g.val i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hg
  exact (g.val i j).2

theorem corner_mem_KO {g : GL (Fin n) k} (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) :
    g ∈ KO k (Fin n) := by
  let N : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix N = g.val := rfl
  have hu : IsUnit N.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

end

theorem corner_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  intro k _ _ _ _ n ψ hord x hx a b hab hnt htr
  have hnt' := hnt
  unfold Triv at hnt'
  push_neg at hnt'
  obtain ⟨u, hu, hle, hne⟩ := hnt'
  have hx0 : x.val a b ≠ 0 := fun h0 => hnt (h0 ▸ triv_zero _)
  set s : k := ((u : k) - 1) / x.val a b with hs
  have hsx : s * x.val a b = (u : k) - 1 := div_mul_cancel₀ _ hx0
  have hs1 : valuation k s ≤ 1 := by
    rw [hs, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j) := fun i j => by
    rw [map_mul]
    exact mul_le_of_le_one_left' hs1
  let M : Matrix (Fin n) (Fin n) k := 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)
  have hdet : M.det = (u : k) := by
    simp only [M]
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]
    ring
  let j : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)
  have hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a) := rfl
  have hjK : j ∈ KO k (Fin n) := by
    refine corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)
    rw [hj, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.vecMulVec_apply, Pi.single_apply]
      split_ifs
      · exact (hsm _ _).trans (corner_val_le_one hx _ _)
      · simp
  refine ⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩
  · rw [hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      exact triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))
    · rw [zero_mul]; exact triv_zero _
  · intro h
    apply hne
    simp [h]
  · refine theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h, hsx]
    · simp
  · exact mul_mem (mul_mem hx hjK) (inv_mem hx)
  · have hxx : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
    congr 2
    · ext i
      simp [Matrix.mulVec_single, mul_comm]
    · ext l
      have := congrFun (congrFun hxx a) l
      rw [Matrix.mul_apply] at this
      rw [Matrix.vecMul, dotProduct]
      rw [Pi.single_apply, this, Matrix.one_apply]
      simp [eq_comm]

end GlobalTheory.PsType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruenceStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  first | exact @GlobalTheory.PsType.corner_rankOne | exact GlobalTheory.PsType.corner_rankOne | (intros; apply GlobalTheory.PsType.corner_rankOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbationStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_rankOne | exact GlobalTheory.PsType.theta_rankOne | (intros; apply GlobalTheory.PsType.theta_rankOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutside

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem not_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  intro k _ _ _ _ n ψ hord y hy hny
  classical

  have hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b) := by
    by_contra h
    push_neg at h
    exact hny ⟨hy, fun i j hij => h i j hij⟩
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, h⟩ := hbad
    exact ⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩
  set a := S.min' hS with ha_def
  have haS : a ∈ S := S.min'_mem hS
  have hamin : ∀ i ∈ S, a ≤ i := fun i hi => S.min'_le i hi
  let T : Finset (Fin n) := Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hT : T.Nonempty := by
    have := haS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by simp [T]; exact hb⟩
  set b := T.max' hT with hb_def
  have hbT : b ∈ T := T.max'_mem hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT
  obtain ⟨hab, hbad_ab⟩ := hbT
  have hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j) := by
    intro j hj
    by_contra hc
    have : j ∈ T := by simp [T]; exact ⟨lt_trans hab hj, hc⟩
    exact absurd (T.le_max' j this) (not_le.mpr hj)
  obtain ⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩ :=
    GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence k n ψ hord y hy a b hab hbad_ab hbmax
  have hprops := GlobalTheory.PsType.triv_ev_props k
  refine ⟨j, hj, ⟨hKO, ?_⟩, ?_⟩
  · intro i i' hii'
    rw [hval]
    by_cases hi' : i' = a
    · subst hi'
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one,
        if_neg (ne_of_lt hii'), zero_add]

      have hiS : i ∉ S := fun h => absurd (hamin i h) (not_le.mpr hii')
      have hib : Triv (ψ i / ψ b) (y.val i b) := by
        by_contra hc
        exact hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)
      have h2 : Triv (ψ i / ψ a) (y.val i b) := hord i i a b le_rfl hii'.le hab.le _ hib
      refine hprops.1 _ _ _ ?_ h2
      rw [map_mul]
      first
        | exact mul_le_of_le_one_left' hs
        | exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)
        | exact mul_le_of_le_one_left (zero_le _) hs
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero,
        if_neg (ne_of_lt hii'), add_zero]
      exact hprops.2.2.1 _
  · have hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ) := by
      refine GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_
      intro i
      by_cases hi : i = a
      · subst hi; simp [hsu]
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [hθj, hθ]
    intro h
    exact hne (Units.ext h).symm

end GlobalTheory.PsType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutsideStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesType_not_intertwine_outside : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  first | exact @GlobalTheory.PsType.not_intertwine | exact GlobalTheory.PsType.not_intertwine | (intros; apply GlobalTheory.PsType.not_intertwine <;> assumption)
end
end
