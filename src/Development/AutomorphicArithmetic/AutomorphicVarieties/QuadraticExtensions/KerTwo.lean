module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Mathlib.GroupTheory.IndexNormal

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SubqLen

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.subqLen :
    ∀ (l : ℕ) [Fact l.Prime] (N : Submodule ℤ_[l] (QZ l)) (Q P : Type) [AddCommGroup Q] [Module ℤ_[l] Q] [AddCommGroup P] [Module ℤ_[l] P] (π : N →ₗ[ℤ_[l]] Q) (j : P →ₗ[ℤ_[l]] Q),
      Function.Surjective π → Function.Injective j → (∀ x : P, (l : ℤ_[l]) • x = 0) → Module.length ℤ_[l] P ≤ 1 := by
  intro l _ N Q P _ _ _ _ π j hπ hj htor
  have key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
    have step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
      intro x y h
      by_cases hy : y = 0
      · subst hy
        refine ⟨0, ?_⟩
        rw [norm_zero] at h
        rw [norm_le_zero_iff.mp h, zero_smul]
      · refine ⟨⟨x / y, ?_⟩, ?_⟩
        · rw [PadicInt.mem_subring_iff, norm_div]
          exact div_le_one_of_le₀ h (norm_nonneg _)
        · show x = (x / y) * y
          rw [div_mul_cancel₀ _ hy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · obtain ⟨c, hc⟩ := step x y h
      exact ⟨c, Or.inl (by rw [hc]; rfl)⟩
    · obtain ⟨c, hc⟩ := step y x h
      exact ⟨c, Or.inr (by rw [hc]; rfl)⟩
  have hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := hπ q1
    obtain ⟨n2, rfl⟩ := hπ q2
    obtain ⟨c, h | h⟩ := key (n1 : QZ l) (n2 : QZ l)
    · refine ⟨c, Or.inl ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
    · refine ⟨c, Or.inr ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
  have hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x} := by
    intro x y hx
    obtain ⟨c, h | h⟩ := hQ (j y) (j x)
    · rw [← map_smul] at h
      rw [hj h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · rw [← map_smul] at h
      have hxy := hj h
      by_cases hc : IsUnit c
      · obtain ⟨u, rfl⟩ := hc
        have hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by
          rw [hxy, smul_smul, Units.inv_mul, one_smul]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · exfalso
        have hn : ‖c‖ < 1 := PadicInt.mem_nonunits.mp hc
        obtain ⟨d, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd c).mp hn
        apply hx
        rw [hxy, mul_comm, mul_smul, htor, smul_zero]
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · rw [Module.length_eq_zero]
    exact zero_le
  · haveI : IsSimpleModule ℤ_[l] P := by
      rw [isSimpleModule_iff]
      refine IsSimpleOrder.mk (fun S => ?_)
      by_cases hS : S = ⊥
      · exact Or.inl hS
      · right
        obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hS
        rw [eq_top_iff]
        intro y _
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)
    rw [Module.length_eq_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.KerTwo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem gen_of_dvd_two {Q : Type} [Group Q] (H : Subgroup Q) (h : H.index ∣ 2) :
    H.Normal ∧ ∃ γ : Q, ∀ u : Q, u ∈ H ∨ u * γ ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact ⟨inferInstance, 1, fun u => Or.inl trivial⟩
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
    exact ⟨Subgroup.normal_of_index_eq_two h2, a, fun u => (ha u).or.symm⟩

theorem UpperTheory.V.Two.kerTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Representation ℤ_[2] Γ (QZ 2)) (U' U : Subgroup Γ) (h : U' ≤ U), ContAction ρ → U'.relIndex U ∣ 2 → Module.length ℤ_[2] (LinearMap.ker (resU ρ h)) ≤ 1 := by
  intro Γ _ _ _ ρ U' U h hρ hd
  obtain ⟨hN, γ, hγ⟩ := gen_of_dvd_two (U'.subgroupOf U) hd
  have hcl : U ≤ (Subgroup.zpowers γ.1 ⊔ U').topologicalClosure := by
    refine le_trans (fun u hu => ?_) (Subgroup.le_topologicalClosure _)
    rcases hγ ⟨u, hu⟩ with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · have h2 : u * γ.1 ∈ Subgroup.zpowers γ.1 ⊔ U' := Subgroup.mem_sup_right h1
      exact (Subgroup.mul_mem_cancel_right _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).1 h2
  have hstab : ∀ m ∈ H0U ρ U', ρ γ m - m ∈ H0U ρ U' := by
    intro m hm
    refine Submodule.sub_mem _ ?_ hm
    intro u
    have h1 : γ⁻¹ * ⟨u.1, h u.2⟩ * γ⁻¹⁻¹ ∈ U'.subgroupOf U :=
      hN.conj_mem _ (by simp [Subgroup.mem_subgroupOf]) _
    have h2 : γ.1⁻¹ * u.1 * γ.1 ∈ U' := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : ρ (γ.1⁻¹ * u.1 * γ.1) m = m := hm ⟨_, h2⟩
    show ρ u.1 (ρ γ m) = ρ γ m
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  let T : H0U ρ U' →ₗ[ℤ_[2]] H0U ρ U' := (ρ γ - LinearMap.id).restrict (p := H0U ρ U') (q := H0U ρ U') hstab
  obtain ⟨φ, hφ⟩ := kerResGen1 _ Γ _ ρ hρ U' U h γ γ.2 hcl T fun _ => rfl
  refine subqLen 2 (H0U ρ U') _ _ (LinearMap.range T).mkQ φ (Submodule.mkQ_surjective _) hφ fun x => ?_
  obtain ⟨k, hk⟩ := hd
  have h1 := kerResSmul _ Γ _ ρ U' U h x.1 x.2
  refine Subtype.ext ?_
  show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
  have h2 : (U'.relIndex U * k) • x.1 = 0 := by rw [mul_comm, mul_smul, h1, smul_zero]
  rw [← hk] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2
end
end
