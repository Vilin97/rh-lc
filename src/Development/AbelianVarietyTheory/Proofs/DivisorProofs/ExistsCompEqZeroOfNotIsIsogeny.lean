module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithfulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuationStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLe

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem end_isogeny_algebra_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K),
    Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  intro K _ A
  obtain ⟨hfin, hfree, hrk⟩ := GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A
  let e : End A ≃ₗ[ℤ] (A ⟶ A) := End.addEquiv.toIntLinearEquiv
  haveI : Module.Finite ℤ (A ⟶ A) := hfin
  haveI : Module.Free ℤ (A ⟶ A) := hfree
  haveI : Module.Finite ℤ (End A) := Module.Finite.equiv e.symm
  haveI : Module.Free ℤ (End A) := Module.Free.of_equiv e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  rw [e.finrank_eq]
  exact hrk

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.end_isogeny_algebra_finite_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K), Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  first | (exact @GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (exact GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (intros; apply GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFreeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.hom_torsionFree | exact GlobalTheory.AV.AbVar.hom_torsionFree | (intros; apply GlobalTheory.AV.AbVar.hom_torsionFree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isLocalizedModule_ratTensor (M : Type) [AddCommGroup M] :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)

theorem toEnd0_apply {K : Type} [Field K] (A : AbVar K) (f : End A) :
    toEnd0 A f = TensorProduct.mk ℤ ℚ (End A) 1 f := rfl

theorem toEnd0_injective_and_fraction : ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Injective (toEnd0 A) ∧ ∀ x : End0 A, ∃ (n : ℕ) (f : End A), 0 < n ∧ n • x = toEnd0 A f := by
  intro K _ A
  haveI := isLocalizedModule_ratTensor (End A)
  refine ⟨fun f g h => ?_, fun x => ?_⟩
  · rw [toEnd0_apply, toEnd0_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    have h1 : (c : ℤ) • (f - g) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [Submonoid.smul_def] using hc
    apply sub_eq_zero.1
    apply End.addEquiv.injective
    apply GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero K A A (c : ℤ) _ hc0
    have hh := congrArg (End.addEquiv (X := A)) h1
    rw [map_zsmul, map_zero] at hh
    exact hh
  · obtain ⟨⟨m, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    simp only [Submonoid.smul_def] at hc
    rcases Int.natAbs_eq (c : ℤ) with h | h
    · refine ⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩
      rw [toEnd0_apply, ← hc, ← natCast_zsmul, ← h]
    · refine ⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩
      have h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ) := by omega
      rw [toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]

end GlobalTheory.AV.AbVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompEqZeroOfNotIsIsogeny

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.Dieu.AbsDet

theorem exists_mul_eq_zero_of_not_isUnit {R : Type} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R] (x : R)
    (hx : ¬ IsUnit x) : ∃ y : R, y ≠ 0 ∧ y * x = 0 := by
  by_contra h
  push Not at h
  have hr : Function.Injective (LinearMap.mulRight ℚ x) := by
    intro a b hab
    by_contra hne
    refine h (a - b) (sub_ne_zero.mpr hne) ?_
    rw [sub_mul]
    exact sub_eq_zero.mpr hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hr) 1
  have hyx : y * x = 1 := hy
  have hl : Function.Injective (LinearMap.mulLeft ℚ x) := by
    intro a b hab
    have hab' : x * a = x * b := hab
    have e : y * (x * a) = y * (x * b) := by rw [hab']
    rwa [← mul_assoc, ← mul_assoc, hyx, one_mul, one_mul] at e
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hl) 1
  have hxz : x * z = 1 := hz
  have hyz : y = z := by
    calc y = y * (x * z) := by rw [hxz, mul_one]
      _ = z := by rw [← mul_assoc, hyx, one_mul]
  exact hx ⟨⟨x, y, hyz ▸ hxz, hyx⟩, rfl⟩

theorem norm_natCast_padicInt (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ‖((n : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ‖((n : ℕ) : ℤ_[p])‖ = ‖((n : ℚ) : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn.ne'),
    padicValRat.of_nat, Rat.cast_zpow, Rat.cast_natCast, Nat.padicValNat_def]

theorem exists_comp_eq_zero_of_not_isIsogeny {k : Type} [Field k] (A : AbVar k) (f : End A)
    (hf : ¬ IsIsogeny f.asHom) : ∃ g : End A, g ≠ 0 ∧ f.asHom ≫ g.asHom = 0 := by
  have hfin := (GlobalTheory.T.end_isogeny_algebra_finite_finrank_le k A).1
  have hx : ¬ IsUnit (toEnd0 A f) := by
    rintro ⟨u, hu⟩
    obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 (↑u⁻¹ : End0 A)
    have h1 : toEnd0 A (f * g) = toEnd0 A ((n : ℤ) • (1 : End A)) := by
      rw [map_mul, ← hg, ← hu, mul_smul_comm, Units.mul_inv, map_zsmul, map_one, natCast_zsmul]
    have h2 : g.asHom ≫ f.asHom = (n : ℤ) • 𝟙 A := by
      rw [← End.mul_asHom, (toEnd0_injective_and_fraction k A).1 h1]
      exact map_zsmul End.addEquiv (n : ℤ) (1 : End A)
    have hiso : IsIsogeny (g.asHom ≫ f.asHom) := by
      rw [h2]; exact (GlobalTheory.MulIsogeny.mul_isogeny k A n (by exact_mod_cast hn.ne')).1
    exact hf ((isIsogeny_comp_iff_and_deg_comp k A A A g.asHom f.asHom rfl rfl).1.1 hiso).2
  obtain ⟨y, hy0, hyx⟩ := exists_mul_eq_zero_of_not_isUnit _ hx
  obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 y
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hg
    have h0 : (n : ℚ) • y = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hg
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply hy0
    rw [← inv_smul_smul₀ hnq y, h0, smul_zero]
  · have hz : g * f = 0 := by
      apply (toEnd0_injective_and_fraction k A).1
      rw [map_mul, ← hg, smul_mul_assoc, hyx, smul_zero, map_zero]
    simpa only [End.addEquiv_apply, End.mul_asHom, map_zero] using congrArg End.addEquiv hz

theorem norm_det_eq_norm_deg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)]
    (ψ : ℤ_[p] →+* (WittVector p k)) (f : End A) (d : ℤ_[p]),
    LinearMap.det (T.map (t.map t f.asHom.hom)) = ψ d → ‖d‖ = ‖((deg f.asHom : ℕ) : ℤ_[p])‖ := by
  intro p _ T k _ _ _ A G t _ _ ψ f d hd
  have hlen := GlobalTheory.T.wittVector_colength_range_eq_det_valuation p k (T.M G) ψ (T.map (t.map t f.asHom.hom)) d hd
  by_cases hf : IsIsogeny f.asHom
  · have hb := (GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation p T k A A G G t t f.asHom).2.1 hf
    have hpos := (isogeny_flat_finrank k A A f.asHom hf).2.2.1
    rw [hlen.1 _ hb.2, norm_natCast_padicInt p _ hpos]
  · have hdeg : deg f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, norm_eq_zero]
    apply hlen.2.1
    intro hinj
    obtain ⟨g, hg0, hfg⟩ := exists_comp_eq_zero_of_not_isIsogeny A f hf
    have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    have hcomp : t.map t f.asHom.hom ≫ t.map t g.asHom.hom = 0 := by
      have e1 : f.asHom.hom ≫ g.asHom.hom = (1 : A.X ⟶ A.X) := by rw [← comp_hom, hfg, zero_hom]
      exact (TorsionTower.map_comp t t t _ _).symm.trans ((t.map_congr t e1).trans (TorsionTower.map_one t t))
    have hne : T.map (t.map t g.asHom.hom) ≠ 0 := by
      intro h0
      apply hg0
      apply End.addEquiv.injective
      rw [map_zero]
      exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A A G G t t g.asHom).2
        ((GlobalTheory.T.dieudonne_integrality_and_faithful p T k G G _).2 h0)
    obtain ⟨m, hm⟩ : ∃ m, T.map (t.map t g.asHom.hom) m ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    apply hm
    apply hinj
    have e := hfun.2.1 (t.map t f.asHom.hom) (t.map t g.asHom.hom)
    rw [hcomp, hfun.2.2.2.1] at e
    have e2 := LinearMap.congr_fun e m
    rw [map_zero]
    exact e2.symm.trans rfl

end GlobalTheory.Dieu.AbsDet
end
end
