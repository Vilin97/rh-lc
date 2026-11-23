module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevelStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentsPeriodSpacesAnyLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_coeff_idempotents_any_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ _ _ hA c
  obtain rfl : σ₀ = (KA l).val.toRingHom := RingHom.ext hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)

    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentsPeriodSpacesAnyLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompRat.exists_coeff_idempotents_any_level | exact GlobalTheory.CompRat.exists_coeff_idempotents_any_level | (intros; apply GlobalTheory.CompRat.exists_coeff_idempotents_any_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodSpacePermOfComplexAut

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutesAnyLevel

open GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : ∀ x : KA l, σ x = (x : ℂ)) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ x : KA l, τ (x : ℂ) = x) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := RingHom.ext fun x => by
    show τ (σ x) = σ x
    rw [hA, hτ]
  have hon : ∀ i P, IsPeriod (F.Di i) ty P → ∃ i' P', IsPeriod (F.Di i') ty P' ∧
      F.u i' P' = spMap (τ : ℂ →+* ℂ) ≫ F.u i P := fun i P hP =>
    F.onto _ (by rw [Category.assoc, F.over_σ i P hP, ConjPermutes.spMap_comp, hτσ])
  choose P₀ hP₀ using exists_period F hty
  choose π P₁ hP₁ hu₁ using fun i => hon i (P₀ i) (hP₀ i)
  refine ⟨π, fun i P hP => ?_⟩
  obtain ⟨i', P', hP', hu'⟩ := hon i P hP
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel E H D l Xo σ g ty F hD hσ hty hA c₀
  obtain ⟨e, he, hv⟩ := hc (π i)
  let j : c.F →+* ℂ := (τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom
  have hj : (τ : ℂ →+* ℂ).comp j = c.F.val.toRingHom := RingHom.ext fun a => τ.apply_symm_apply _
  have hjσ : σ = j.comp (IntermediateField.inclusion c.le).toRingHom := RingHom.ext fun x => by
    rw [hA]
    exact (τ.symm_apply_eq.2 (hτ x).symm).symm
  have w : ∀ Q, IsPeriod (F.Di i) ty Q →
      F.u i Q ≫ Xo.s = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun Q hQ => by
    rw [F.over_σ i Q hQ, ConjPermutes.spMap_comp, ← hjσ]
  have key : ∀ Q (hQ : IsPeriod (F.Di i) ty Q) k Q', IsPeriod (F.Di k) ty Q' →
      F.u k Q' = spMap (τ : ℂ →+* ℂ) ≫ F.u i Q →
      τ (valAt' (X := Xo.XF c) (pullback.lift _ _ (w Q hQ)) ⊤ e) = if k = π i then 1 else 0 := by
    intro Q hQ k Q' hQ' h
    rw [← hv k Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift _ _ (w Q hQ))
      (by rw [Category.assoc, pullback.lift_fst, h]) (by rw [Category.assoc, pullback.lift_snd, ConjPermutes.spMap_comp, hj]),
      valAt'_spMap_comp]
    rfl
  have hconst := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F hD hσ hty c j e {0, 1} (Set.toFinite _)
    (fun x _ => valAt'_idem x he) i P (P₀ i) hP (hP₀ i) (pullback.lift _ _ (w P hP))
    (pullback.lift _ _ (w _ (hP₀ i))) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have h₁ := key P hP i' P' hP' hu'
  rw [hconst, key _ (hP₀ i) (π i) (P₁ i) (hP₁ i) (hu₁ i), if_pos rfl] at h₁
  obtain rfl : i' = π i := by
    by_contra hne
    rw [if_neg hne] at h₁
    exact one_ne_zero h₁
  exact ⟨P', hP', hu'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm (fun x => τ.symm_apply_eq.2 (hτ x).symm)
  have hinv : Function.LeftInverse π' π := fun i => by
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨P', hP', h'⟩ := hπ i P hP
    obtain ⟨P'', hP'', h''⟩ := hπ' (π i) P' hP'
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
    have e' : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id (CommRingCat.of ℂ)
    rw [← h', ← Category.assoc, ConjPermutes.spMap_comp, e, e', Category.id_comp] at h''
    exact (F.disj _ _ _ _ hP hP'' h'').symm
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinv.injective), hπ⟩

end GlobalTheory.ConjPermutesAnyLevel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodSpacePermOfComplexAutStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_periodSpace_perm_of_complexAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ τ : ℂ ≃+* ℂ, (∀ x : KA l, τ (x : ℂ) = x) → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  first | exact @GlobalTheory.ConjPermutesAnyLevel.exists_perm | exact GlobalTheory.ConjPermutesAnyLevel.exists_perm | (intros; apply GlobalTheory.ConjPermutesAnyLevel.exists_perm <;> assumption)
end
end
