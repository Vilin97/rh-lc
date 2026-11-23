module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardNonisometricCmTorusDataLeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Tactic.Lemma
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpacesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  first | exact @GlobalTheory.card_comp_le_periodSpaces | exact GlobalTheory.card_comp_le_periodSpaces | (intros; apply GlobalTheory.card_comp_le_periodSpaces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FamilyUnifIndexEqOfMarkedLatticeIsometry

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma isPeriod_comp_symm {D' D'' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D'.La ≃ₗ[𝓞 E] D''.La) (hg : ∀ a b, D''.EF (gam a) (gam b) = D'.EF a b)
    {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsPeriod D'' ty (P.comp gam.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  have hP' : ∀ x, (P.comp gam.symm.toLinearMap.toAddMonoidHom) x = P (gam.symm x) := fun _ => rfl
  have hr : (P.comp gam.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨gam.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨gam x, by rw [hP', LinearEquiv.symm_apply_apply]⟩
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x k
    rw [hP', hP', map_smul, h1]
  · intro x y hxy
    exact gam.symm.injective (h2 hxy)
  · rw [hr]; exact h3
  · have : Set.range (P.comp gam.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
      have := congrArg (fun s : AddSubgroup (Fin g → ℂ) => (s : Set (Fin g → ℂ))) hr
      simpa only [AddMonoidHom.coe_range] using this
    rw [this, h4]
  · intro x y
    rw [hP', hP', hE, ← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

lemma isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {P : (U.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) := by
  have h := (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  intro V f
  obtain ⟨ho, hd⟩ := h V f
  have hc : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have h3 := ho.preimage hc.continuous
    have h4 : {b ∈ Set.univ | ⊤ ≤ (U.ex i P b).left ⁻¹ᵁ V} =
        (fun z : Fin g → ℂ => ((0, z) : (Fin 0 → ℂ) × (Fin g → ℂ))) ⁻¹'
          {b ∈ Set.univ ×ˢ Set.univ | ⊤ ≤ (U.ex i P b.2).left ⁻¹ᵁ V} := by
      ext z
      exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    exact h4 ▸ h3
  · refine hd.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) hc.differentiableOn ?_
    intro z hz
    exact ⟨⟨trivial, trivial⟩, hz.2⟩

theorem index_eq_of_isometry : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (i j : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ a b, (U.Di j).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a, ∃ e, gam (U.t i a) = U.t j a + l.M' • e) → i = j := by
  intro hT hL E _ _ _ H D l Xo σ g ty hr hσ hty U i j gam hg ht
  obtain ⟨-, P, hP⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (U.Di i) g ty
    (by rw [(U.sig i).1, (U.sig i).2]; exact hty)
  have hP' := isPeriod_comp_symm gam hg hP
  refine U.disj i j P _ hP hP' ?_
  refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H D l Xo σ g ty hr hσ hty (U.Di i) (U.Di j)
    (U.t i) (U.t j) P _ _ _ (U.ex i P) (U.ex j _)
    ⟨U.over_σ i P hP, hP, ⟨U.ex_add i P hP, U.ex_onto i P hP, isHolTo_ex U i hP, U.ex_diff i P hP⟩,
      U.ex_ker i P hP, U.ex_lin i P hP, U.ex_weil i P hP, U.ex_eta i P hP, U.ex_etaA i P hP⟩
    ⟨U.over_σ j _ hP', hP', ⟨U.ex_add j _ hP', U.ex_onto j _ hP', isHolTo_ex U j hP', U.ex_diff j _ hP'⟩,
      U.ex_ker j _ hP', U.ex_lin j _ hP', U.ex_weil j _ hP', U.ex_eta j _ hP', U.ex_etaA j _ hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hg, fun a _ => ?_, fun a => ?_, fun a => ?_⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · change P (gam.symm (gam a)) = P a
    rw [LinearEquiv.symm_apply_apply]

end GlobalTheory.UnifMatch
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FamilyUnifIndexEqOfMarkedLatticeIsometryStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (i j : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ a b, (U.Di j).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a, ∃ e, gam (U.t i a) = U.t j a + l.M' • e) → i = j := by
  first | exact @GlobalTheory.UnifMatch.index_eq_of_isometry | exact GlobalTheory.UnifMatch.index_eq_of_isometry | (intros; apply GlobalTheory.UnifMatch.index_eq_of_isometry <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardPeriodSpacesFamilyUniformisationLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace PeriodSpaceCount

theorem exists_injective_pi {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ φ : M →ₗ[R] (Fin r → R), Function.Injective φ := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  have h3 : ∀ m : M, (c • (LinearMap.id : M →ₗ[R] M)) m ∈ Submodule.span R (Set.range v) := fun m => by
    have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h3
  refine ⟨(Module.Basis.span hv).equivFun.toLinearMap ∘ₗ LinearMap.codRestrict _ _ h3,
    (Module.Basis.span hv).equivFun.injective.comp fun x y h => ?_⟩
  exact smul_right_injective M (nonZeroDivisors.ne_zero hc0) (congrArg Subtype.val h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_generators (D : Datum H) {k : ℕ} (hk : 0 < k) :
    ∃ x : Fin (D.p + D.q) → D.La, ∀ m : D.La, ∃ (c : Fin (D.p + D.q) → 𝓞 E) (m' : D.La),
      m = ∑ i, c i • x i + k • m' := by
  have := D.fin
  have := D.proj
  obtain ⟨φ, hφ⟩ := exists_injective_pi D.rank
  obtain ⟨x, hx⟩ := BoundedBasis.exists_generators_mod_smul (a := (k : 𝓞 E))
    (Nat.cast_ne_zero.2 hk.ne') _ D.La φ hφ
  refine ⟨x, fun m => ?_⟩
  obtain ⟨c, m', h⟩ := hx m
  exact ⟨c, m', by rw [h, Nat.cast_smul_eq_nsmul]⟩

def Isometric (D D' : Datum H) : Prop :=
  ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b

theorem Isometric.refl (D : Datum H) : Isometric D D := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Isometric.symm {D D' : Datum H} (h : Isometric D D') : Isometric D' D := by
  obtain ⟨gam, h⟩ := h
  exact ⟨gam.symm, fun a b => by rw [← h]; simp⟩

theorem Isometric.trans {D D' D'' : Datum H} (h : Isometric D D') (h' : Isometric D' D'') :
    Isometric D D'' := by
  obtain ⟨gam, h⟩ := h
  obtain ⟨gam', h'⟩ := h'
  exact ⟨gam.trans gam', fun a b => by rw [← h, ← h']; rfl⟩

theorem card_isometric_le {D D₀ : Datum H} (h₀ : D₀.p + D₀.q = D.p + D.q) {k : ℕ} (hk : 0 < k)
    {n : ℕ} (Di : Fin n → Datum H) (t : ∀ i, D.La →ₗ[𝓞 E] (Di i).La)
    (hmatch : ∀ (i j : Fin n) (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La),
      (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) →
      (∀ a, ∃ e, gam (t i a) = t j a + k • e) → i = j)
    (s : Finset (Fin n)) (hs : ∀ i ∈ s, Isometric (Di i) D₀) :
    s.card ≤ k ^ (2 * FD.fdeg E * (D.p + D.q) ^ 2) := by
  classical
  have := D₀.fin
  have : Module.Finite ℤ D₀.La := Module.Finite.trans (𝓞 E) D₀.La
  have := datum_free_int D₀
  let K : AddSubgroup D₀.La := (nsmulAddMonoidHom k : D₀.La →+ D₀.La).range
  have hK : Nat.card (D₀.La ⧸ K) = k ^ Module.finrank ℤ D₀.La :=
    AddSubgroup.index_range_nsmul D₀.La k
  have : Finite (D₀.La ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨x, hx⟩ := exists_generators D hk
  choose gam hgam using hs
  let F : s → Fin (D.p + D.q) → D₀.La ⧸ K := fun i c => QuotientAddGroup.mk (gam i.1 i.2 (t i.1 (x c)))
  have hF : Function.Injective F := by
    intro i j hij
    refine Subtype.ext (hmatch i.1 j.1 ((gam i.1 i.2).trans (gam j.1 j.2).symm) (fun a b => ?_)
      fun a => ?_)
    · rw [← hgam j.1 j.2, ← hgam i.1 i.2]
      simp
    · have h1 : ∀ c, ∃ e, gam i.1 i.2 (t i.1 (x c)) = gam j.1 j.2 (t j.1 (x c)) + k • e := fun c => by
        obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (congrFun hij c).symm
        exact ⟨e, by rw [show k • e = _ from he, add_neg_cancel_left]⟩
      choose e he using h1
      obtain ⟨c, m', rfl⟩ := hx a
      refine ⟨(gam j.1 j.2).symm (∑ d, c d • e d + gam i.1 i.2 (t i.1 m') - gam j.1 j.2 (t j.1 m')), ?_⟩
      apply (gam j.1 j.2).injective

      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add (f := _), map_nsmul, map_sum,
      map_smul, he, smul_add, smul_sub, Finset.sum_add_distrib, Finset.smul_sum, smul_comm k]
      abel
  have h2 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_fun, hK, datum_finrank_int, h₀,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul] at h2
  refine h2.trans (le_of_eq ?_)
  congr 1
  unfold FD.fdeg
  ring

theorem exists_representatives {n : ℕ} (Di : Fin n → Datum H) :
    ∃ (m : ℕ) (rep : Fin m → Fin n), (∀ c d, Isometric (Di (rep c)) (Di (rep d)) → c = d) ∧
      ∀ i, ∃ c, Isometric (Di i) (Di (rep c)) := by
  let S : Setoid (Fin n) := ⟨fun i j => Isometric (Di i) (Di j),
    fun _ => Isometric.refl _, Isometric.symm, Isometric.trans⟩
  let e := Finite.equivFin (Quotient S)
  refine ⟨_, fun c => (e.symm c).out, fun c d h => ?_, fun i => ⟨e (Quotient.mk S i), ?_⟩⟩
  · exact e.symm.injective (Quotient.out_equiv_out.1 h)
  · simp only [Equiv.symm_apply_apply]
    exact Isometric.symm (Quotient.mk_out (s := S) i)

end PeriodSpaceCount


open PeriodSpaceCount in
theorem familyUnif_card_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (r : ℕ), r = D.p + D.q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → (U.n : ℝ) ≤ (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * ((1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2)) ∧ ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log U.n ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  intro hN hT hL E _ _ _ H D l Xo σ g ty h1 hσ hty U r hr ξ AA hξ hξ0 hfg hA0 hAA
  classical
  have hk : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨m, rep, hrep, hcls⟩ := exists_representatives U.Di
  have hm := GlobalTheory.T.card_nonisometric_cmTorusData_le hN E H D.p D.q r hr ξ AA hξ hξ0 hfg hA0 hAA m (fun c => U.Di (rep c))
    (fun c => U.sig _) fun c d gam h => hrep c d ⟨gam, h⟩
  have hn : U.n ≤ m * l.M' ^ (2 * FD.fdeg E * r ^ 2) := by
    have h2 : (Finset.univ : Finset (Fin U.n)) ⊆ (Finset.univ : Finset (Fin m)).biUnion
        fun c => Finset.univ.filter fun i => Isometric (U.Di i) (U.Di (rep c)) := fun i _ => by
      obtain ⟨c, hc⟩ := hcls i
      exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
    have h3 := (Finset.card_le_card h2).trans (Finset.card_biUnion_le_card_mul _ _
      (l.M' ^ (2 * FD.fdeg E * r ^ 2)) fun c _ => by
        rw [hr]
        exact card_isometric_le (D₀ := U.Di (rep c)) (by rw [(U.sig _).1, (U.sig _).2]) hk U.Di U.t
          (GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry hT hL E H D l Xo σ g ty h1 hσ hty U) _ fun i hi => (Finset.mem_filter.1 hi).2)
    simpa using h3
  have hmain := le_trans (b := (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * m) (a := (U.n : ℝ))
    (by rw [mul_comm]; exact_mod_cast hn) (mul_le_mul_of_nonneg_left hm (by positivity))
  refine ⟨hmain, fun L hf hL2 hd hrL hfL hM => ?_⟩
  have h := hmain.trans (ClassCount.pow_mul_bound_le_exp (FD.fdeg E) r (d := FD.dE E) hf hL2
    (abs_nonneg _) hd hrL hfL (Nat.cast_nonneg _) hM)
  have h0 := sq_nonneg (FD.fdeg E * r * L)
  have h' : (0 : ℝ) < U.n := by exact_mod_cast U.n_pos
  linarith [(Real.log_le_iff_le_exp h').2 h]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardPeriodSpacesFamilyUniformisationLeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.card_periodSpaces_familyUniformisation_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (r : ℕ), r = D.p + D.q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → (U.n : ℝ) ≤ (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * ((1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2)) ∧ ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log U.n ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  first | exact @GlobalTheory.familyUnif_card_le | exact GlobalTheory.familyUnif_card_le | (intros; apply GlobalTheory.familyUnif_card_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem log_card_comp_unf_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log (Fintype.card U.Comp) ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  intro hH hT hO E _ _ _ H D l Xo c σ r U hr hG hU ξ AA hcc hξ hfg hbot hdual L hdeg hL hdE hr' hdg hM

  obtain ⟨g, ty, F, hty, hcard⟩ := GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le hO E H D l Xo c σ r U hr hG hU
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  have hrank : r = D.p + D.q := hU'.1
  have hemb := hG
  unfold Formalism.L2.PjFree.GoodEmb at hemb

  have key := (GlobalTheory.T.card_periodSpaces_familyUniformisation_le hH hT hO E H D l Xo _ g ty (hrank ▸ hr) hemb hty F r hrank ξ AA hcc hξ
    hfg hbot hdual).2 L hdeg hL hdE hr' hdg hM
  rcases Nat.eq_zero_or_pos (Fintype.card U.Comp) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    positivity
  · refine le_trans (Real.log_le_log (by exact_mod_cast hpos) ?_) key
    exact_mod_cast hcard

end GlobalTheory
end
end
