module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealTangentSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscriminantTraceBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankRieszBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscreteLatticeMinimum

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscreteLatticeMinimum

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]

noncomputable def Bmap : VT (X := Y.toData) z ξ →ₗ[ℝ] VT (X := Y.toData) z ξ where
  toFun u := VT.mk (MajorantOperators.Bop z u.val) (MajorantOperators.Bop_mem hz.out u.val_mem)
  map_add' u v := VT.ext (by simp [MajorantOperators.Bop_add])
  map_smul' c u := VT.ext (by simp [MajorantOperators.Bop_smul])

theorem Bmap_val (u : VT (X := Y.toData) z ξ) : (Bmap z ξ u).val = MajorantOperators.Bop z u.val := rfl

theorem Bmap_Bmap (u : VT (X := Y.toData) z ξ) : Bmap z ξ (Bmap z ξ u) = (-(Y.k0 ^ 2)) • u := by
  apply VT.ext
  rw [Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]
  rfl

theorem inner_Bmap_right (u v : VT (X := Y.toData) z ξ) :
    inner ℝ u (Bmap z ξ v) = -inner ℝ (Bmap z ξ u) v := by
  rw [inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]

theorem norm_Bmap (u : VT (X := Y.toData) z ξ) : ‖Bmap z ξ u‖ = Y.k0 * ‖u‖ := by
  have h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq,
      Bmap_val, MajorantOperators.gI_Bop_self hz.out]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _))
    two_ne_zero).1 h

theorem Bmap_injective : Function.Injective (Bmap z ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := norm_Bmap z ξ u
  rw [hu, norm_zero] at h
  have h2 : ‖u‖ = 0 := by
    rcases mul_eq_zero.1 h.symm with h3 | h3
    · exact absurd h3 Y.minWeight_pos.ne'
    · exact h3
  exact norm_eq_zero.1 h2

noncomputable def Bequiv : VT (X := Y.toData) z ξ ≃ₗ[ℝ] VT (X := Y.toData) z ξ :=
  LinearEquiv.ofBijective (Bmap z ξ) ⟨Bmap_injective z ξ,
    LinearMap.surjective_of_injective (Bmap_injective z ξ)⟩

variable {ξ} (hξ : Y.IsIso ξ)

theorem mem_Lat_of_int (hD3 : IntegerApproximationCount (E := E)) (y : VT (X := Y.toData) z ξ)
    (hy : ∀ a ∈ Lat z ξ hξ, ∃ m : ℤ, inner ℝ y (Bmap z ξ a) = m) : y ∈ Lat z ξ hξ := by
  classical
  have hval : ∀ ν : Y.Λp ξ, inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) =
      (round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))) : ℝ) := by
    intro ν
    obtain ⟨m, hm⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
    rw [hm, round_intCast]
  let ψ : Y.Λp ξ →+ ℤ := AddMonoidHom.mk' (fun ν => round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))))
    (fun ν ν' => by
      obtain ⟨m1, hm1⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
      obtain ⟨m2, hm2⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν', rfl⟩)
      show round _ = round _ + round _
      rw [map_add (f := _), map_add (f := _), inner_add_right, hm1, hm2, ← Int.cast_add, round_intCast, round_intCast,
        round_intCast])
  have hψ : ∀ ν, (ψ ν : ℝ) = inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) := fun ν => (hval ν).symm
  have hvan : ∀ ν : Y.Λp ξ, (∃ e : E, (ν : Fin r → E) = e • ξ) → ψ ν = 0 := by
    rintro ν ⟨e, he⟩
    have h0 : phi z ξ hξ ν = 0 := VT.ext (by rw [phi_val, he, ucomp_line z ξ hξ e]; rfl)
    have := hψ ν
    rw [h0, map_zero, inner_zero_right] at this
    exact_mod_cast this
  obtain ⟨μ, hμ⟩ := (hermitian_dual_lattice_identity r Y ξ hξ).1 ψ hvan
  have hEF : ∀ ν : Y.Λp ξ,
      inner ℝ (Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) = 0 := by
    intro ν
    have h1 := hμ ν
    have h2 : ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) =
        inner ℝ (Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) := by
      rw [inner_eq, Bmap_val, phi_val, phi_val]
      exact MajorantOperators.EF_eq hz.out hξ.2.1 (LatticeSpanMembership.mem_Λp_iff.mp μ.2).2
        (LatticeSpanMembership.mem_Λp_iff.mp ν.2).2
    have h3 : (ψ ν : ℝ) = ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) := by exact_mod_cast h1
    rw [hψ, inner_Bmap_right, h2] at h3
    rw [inner_add_left]
    linarith
  set w := Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ) with hw
  have hwall : ∀ a ∈ Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := Y.toData) z ξ)),
      inner ℝ w a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨ν, rfl⟩ := (mem_Lat z ξ hξ).mp ha
      exact hEF ν
    | zero => exact inner_zero_right _
    | add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
    | smul c a _ iha => rw [inner_smul_right, iha, mul_zero]
  have hw0 : w = 0 := by
    have := hwall w (by rw [span_Lat z ξ hD3 hξ]; exact Submodule.mem_top)
    exact inner_self_eq_zero.mp this
  have hy0 : y + phi z ξ hξ μ = 0 := by
    apply Bmap_injective z ξ
    rw [map_add (f := _), ← hw, hw0, map_zero]
  have : y = phi z ξ hξ (-μ) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hy0
  rw [this]
  exact (mem_Lat z ξ hξ).mpr ⟨-μ, rfl⟩

section lattice

variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))

include hns in
theorem min_norm (a : VT (X := Y.toData) z ξ) (ha : a ∈ Lat z ξ hξ) (ha0 : a ≠ 0) :
    Real.sqrt ep0 / Y.NA ≤ ‖a‖ := by
  obtain ⟨μ, rfl⟩ := (mem_Lat z ξ hξ).mp ha
  have hμ := LatticeSpanMembership.mem_Λp_iff.mp μ.2
  have hNA : (Y.NA : E) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
  have hNAr : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
  obtain ⟨τ, hτ⟩ := hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1)
    (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero])
    (by
      intro e he
      apply ha0
      have hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ := by
        rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]
      exact VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))
  have hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ := by
    funext τ' b
    simp [Data.embV, Data.emb]
  rw [hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out] at hτ
  have h2 := maj_le_norm_sq z ξ (phi z ξ hξ μ) τ
  rw [phi_val] at h2
  have h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2 := by
    rw [mul_pow]
    exact le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  rw [div_le_iff₀ hNAr]
  linarith

include hns in
theorem discrete_Lat (hep : 0 < ep0) : DiscreteTopology (Lat z ξ hξ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hε : 0 < Real.sqrt ep0 / Y.NA :=
    div_pos (Real.sqrt_pos.mpr hep) (by exact_mod_cast Y.NA_pos)
  have hset : ({0} : Set (Lat z ξ hξ)) =
      Subtype.val ⁻¹' Metric.ball (0 : VT (X := Y.toData) z ξ) (Real.sqrt ep0 / Y.NA) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have := min_norm z hξ ep0 hns x.1 x.2 (fun h => hne (Subtype.ext h))
      linarith
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

include hns in
theorem short_basis (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) :
    ∃ y : Fin (finrank ℝ (VT (X := Y.toData) z ξ)) → VT (X := Y.toData) z ξ,
      LinearIndependent ℝ y ∧ (∀ i, y i ∈ Lat z ξ hξ) ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 /
        (Y.k0 * Real.sqrt ep0 / Y.NA) := by
  classical
  have := discrete_Lat z hξ ep0 hns hep
  have : IsZLattice ℝ (Lat z ξ hξ) := ⟨span_Lat z ξ hD3 hξ⟩
  have := ZLattice.module_free ℝ (Lat z ξ hξ)
  have := ZLattice.module_finite ℝ (Lat z ξ hξ)
  set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn
  let bZ := Module.Free.chooseBasis ℤ (Lat z ξ hξ)
  let bR := bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)
  have hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ := bZ.ofZLatticeBasis_span ℝ _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n :=
    (Module.finrank_eq_card_basis bR).symm
  let bF := bR.reindex (Fintype.equivFinOfCardEq hcard)
  have hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ := by
    rw [Basis.range_reindex]
    exact hspanR
  let e := (stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr
  let b' := (bF.map (Bequiv z ξ)).map e.toLinearEquiv
  have hb'j : ∀ j, b' j = e (Bmap z ξ (bF j)) := fun j => by
    simp only [b', Basis.map_apply]
    rfl
  set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam
  have hlam0 : 0 < lam := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  let f : VT (X := Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ
  have hfr : f '' Set.range bF = Set.range b' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hb'j j).symm)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    rw [← hfr, Submodule.span_image, hspanF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero f)
    have hfa : ‖f a‖ = Y.k0 * ‖a‖ := by
      show ‖e (Bmap z ξ a)‖ = _
      rw [LinearIsometryEquiv.norm_map, norm_Bmap]
    rw [hfa, hlam, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le
  obtain ⟨y, hli, hint, hnorm⟩ := T0.transference_dual b' lam hlam0 hmin
  refine ⟨fun i => e.symm (y i), ?_, ?_, ?_⟩
  · exact hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
  · intro i
    apply mem_Lat_of_int z hξ hD3
    intro a ha
    rw [← hspanF] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      obtain ⟨m, hm⟩ := hint i j
      refine ⟨m, ?_⟩
      rw [← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      exact ⟨m1 + m2, by rw [map_add (f := _), inner_add_right, h1, h2, Int.cast_add]⟩
    | smul c a _ iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨c * m, ?_⟩
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]
  · intro i
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm i


include hns in
theorem covering (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) (d : VT (X := Y.toData) z ξ) :
    ∃ μ : Y.Λp ξ, ‖d - phi z ξ hξ μ‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA /
      (2 * Y.k0 * Real.sqrt ep0) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos
  · have hsub : Subsingleton (VT (X := Y.toData) z ξ) := Module.finrank_zero_iff.mp h0
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]
    simp
  have : Nonempty (Fin (finrank ℝ (VT (X := Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨y, hli, hyL, hyn⟩ := short_basis z hξ ep0 hns hD3 hep
  let yb := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hyb : ∀ i, yb i = y i := fun i => Basis.mk_apply _ _ _
  set c := yb.repr d with hc
  set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp
  have hpL : p ∈ Lat z ξ hξ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)
  obtain ⟨μ, hμ⟩ := (mem_Lat z ξ hξ).mp hpL
  refine ⟨μ, ?_⟩
  rw [hμ]
  have hd : d = ∑ i, c i • y i := by
    conv_lhs => rw [← yb.sum_repr d]
    simp only [hyb, hc]
  have hdiff : d - p = ∑ i, (c i - round (c i)) • y i := by
    rw [hd, hp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [hdiff]
  calc ‖∑ i, (c i - round (c i)) • y i‖ ≤ ∑ i, ‖(c i - round (c i)) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ (VT (X := Y.toData) z ξ)), (1 / 2) *
        ((finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 / (Y.k0 * Real.sqrt ep0 / Y.NA)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)
    _ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 := Y.minWeight_pos.ne'
        have h2 : (Y.NA : ℝ) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
        have h3 := (Real.sqrt_pos.mpr hep).ne'
        field_simp

end lattice

end DiscreteLatticeMinimum

end ReciprocityTheory.ChartRestriction.G.FD
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NoShortVectorLowerBoundHolds

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module RealTangentSpace DiscreteLatticeMinimum
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem noShortVectorLowerBound_holds : NoShortVectorLowerBound (E := E) := by
  intro r X ξ ep0 hξ hep z hz hgap δ
  have hz' : z ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj z τ (Data.emb τ.1 ξ) = 1 := hz
  have hz1 : z ∈ X.dom := hz'.1
  haveI hzf : Fact (z ∈ X.dom) := ⟨hz1⟩
  have hk0 : 0 < X.k0 := X.minWeight_pos
  have hk0ne : X.k0 ≠ 0 := hk0.ne'
  have hdE : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero (K := E)))
  have hdEne : dE E ≠ 0 := hdE.ne'
  have hrd : 0 ≤ rdE E := by
    unfold rdE
    exact Real.rpow_nonneg hdE.le _
  have hepne : ep0 ≠ 0 := hep.ne'
  obtain ⟨d, hd⟩ : ∃ d : VT (X := X.toData) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
    apply FinrankRieszBounds.riesz <;> assumption
  obtain ⟨d', hd'⟩ : ∃ d' : VT (X := X.toData) z ξ,
      d' = (2 / (dE E * X.k0 ^ 2)) • Bmap z ξ d := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : X.Λp ξ, ‖d' - phi z ξ hξ μ‖ ≤
      (finrank ℝ (VT (X := X.toData) z ξ) : ℝ) ^ 3 * X.NA / (2 * X.k0 * Real.sqrt ep0) := by
    apply DiscreteLatticeMinimum.covering (Y := X) (z := z) (ξ := ξ) (hD3 := integerApproximationCount_holds) (hep := hep) <;> assumption
  have hfin : finrank ℝ (VT (X := X.toData) z ξ) ≤ 2 * fdeg E * (r - 2) := by
    apply FinrankRieszBounds.finrank_le <;> assumption
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = finrank ℝ (VT (X := X.toData) z ξ) := ⟨_, rfl⟩
  rw [← hn] at hμ hfin
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ‖d' - phi z ξ hξ μ‖ := ⟨_, rfl⟩
  rw [← hDdef] at hμ
  obtain ⟨w, hw⟩ : ∃ w : VT (X := X.toData) z ξ,
      w = (-(dE E / 2)) • Bmap z ξ (d' - phi z ξ hξ μ) := ⟨_, rfl⟩
  have hd_eq : (-(dE E / 2)) • Bmap z ξ d' = d := by
    rw [hd', map_smul, DiscreteLatticeMinimum.Bmap_Bmap, smul_smul, smul_smul]
    convert one_smul ℝ d using 2
    field_simp <;> ring
  have hw_eq : w = d - (-(dE E / 2)) • Bmap z ξ (phi z ξ hξ μ) := by
    rw [hw, map_sub, smul_sub, hd_eq]
  have hwn : ‖w‖ = dE E / 2 * (X.k0 * D) := by
    rw [hw, norm_smul, DiscreteLatticeMinimum.norm_Bmap, ← hDdef, Real.norm_eq_abs, abs_neg,
      abs_of_pos (half_pos hdE)]
  have hspos : 0 < Real.sqrt ep0 := Real.sqrt_pos.mpr hep
  have hsq : Real.sqrt ep0 ^ 2 = ep0 := Real.sq_sqrt hep.le
  have hden : 0 < 2 * X.k0 * Real.sqrt ep0 := mul_pos (mul_pos two_pos hk0) hspos
  have hD0 : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
  have hB : D * (2 * X.k0 * Real.sqrt ep0) ≤ (n : ℝ) ^ 3 * X.NA := (le_div_iff₀ hden).mp hμ
  have hD2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) ≤ ((n : ℝ) ^ 3 * X.NA) ^ 2 := by
    have h0 : 0 ≤ D * (2 * X.k0 * Real.sqrt ep0) := mul_nonneg hD0 hden.le
    have h1 := pow_le_pow_left₀ h0 hB 2
    have h2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) = (D * (2 * X.k0 * Real.sqrt ep0)) ^ 2 := by
      linear_combination (-(4 * D ^ 2 * X.k0 ^ 2)) * hsq
    rw [h2]
    exact h1
  have hx : 0 ≤ (X.NC : ℝ) ^ 2 * rdE E / ep0 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hrd) hep.le
  have hM2 : frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 =
      (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 * (X.NA : ℝ) ^ 2 *
        ((X.NC : ℝ) ^ 2 * rdE E / ep0) := by
    have hs := Real.sq_sqrt hx
    rw [frameIndexBound]
    linear_combination ((fdeg E : ℝ) * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 3 * dE E *
      (X.NA : ℝ)) ^ 2 * hs
  have hwM : ‖w‖ ^ 2 ≤ frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0 := by
    rw [hwn, hM2]
    have hlhs : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by
      have h3 : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) =
          dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) := by ring
      rw [h3]
      calc dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) ≤ dE E ^ 2 * (((n : ℝ) ^ 3 * X.NA) ^ 2) :=
            mul_le_mul_of_nonneg_left hD2 (sq_nonneg _)
        _ = dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by ring
    have hQ : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    have hS : 0 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hk0.le) hrd
    have hn6 : (n : ℝ) ^ 6 ≤ ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfin) 6
    have hinv : ep0 * ep0⁻¹ = 1 := mul_inv_cancel₀ hepne
    have heq : (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 *
        (X.NA : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * rdE E / ep0) * X.k0 * (16 * ep0) =
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      linear_combination (16 * (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 *
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (X.NC : ℝ) ^ 2 * rdE E * X.k0) * hinv
    have hP : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 := by
      positivity
    have h6 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hn6 hQ
    have hrhs : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      by_cases hN : ((2 * fdeg E * (r - 2) : ℕ) : ℝ) = 0
      · have hP0 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 = 0 := by
          rw [hN]; ring
        have h5 : 0 ≤ 16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
            ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) :=
          mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hP)) hS
        linarith
      · have hN' : 2 * fdeg E * (r - 2) ≠ 0 := by exact_mod_cast hN
        have hf0 : fdeg E ≠ 0 := fun h => hN' (by simp [h])
        have hr : 0 < r := Nat.pos_of_ne_zero (fun h => hN' (by simp [h]))
        have hk : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
          apply DiscriminantTraceBounds.two_le_normSq_mul_rootDisc <;> assumption
        have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ 2 := by
          have h1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf0
          nlinarith
        have h7 : 2 ≤ (fdeg E : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by nlinarith
        have h8 := mul_le_mul_of_nonneg_left h7 hP
        linarith
    exact le_of_mul_le_mul_right (hlhs.trans (hrhs.trans_eq heq.symm)) (mul_pos (by norm_num) hep)
  refine ⟨(μ : Fin r → E), μ.2, ?_⟩
  intro u hu τ
  have hsm : ∀ (c : ℝ) (v : Fin r → ℂ),
      X.Hf z τ (u τ) (c • v) = (c : ℂ) * X.Hf z τ (u τ) v := by
    intro c v
    have hcv : c • v = (c : ℂ) • v := (Complex.coe_smul c v).symm
    rw [hcv, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal]
  have hkey : δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
      hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV (μ : Fin r → E)) τ) =
      X.Hf z τ (u τ) (w.val τ) := by
    rw [hw_eq, VT.val_sub, VT.val_smul, Pi.sub_apply, Pi.smul_apply, MajorantOperators.Hf_sub_right,
      ← hd u hu τ, DiscreteLatticeMinimum.Bmap_val, RealTangentSpace.phi_val]
    congr 1
    rw [hsm]
    simp only [MajorantOperators.Bop]
    rw [UnipotentCoefficientShift.Hf_smul_right, Data.Hf_eq_jp, X.hermC_jp_jp hz1]
    simp only [map_mul, map_neg, map_ofNat, MajorantOperators.conj_purely_imaginary_generator]
    push_cast
    ring
  rw [hkey, FinrankRieszBounds.maj_csmul hz1]
  have hc : X.k0 * X.maj z τ (Data.emb τ.1 ξ) = 1 := by
    have h2 := hz'.2 τ
    simp only [Data.c] at h2
    rw [X.ξ0_abs τ] at h2
    linear_combination h2
  have hme : 0 ≤ X.maj z τ (Data.emb τ.1 ξ) := MajorantOperators.maj_nonneg hz1 τ _
  have hmu : 0 ≤ X.maj z τ (u τ) := MajorantOperators.maj_nonneg hz1 τ _
  have hcs := MajorantOperators.Hf_cs hz1 τ (u τ) (w.val τ)
  have hmw : X.maj z τ (w.val τ) ≤ ‖w‖ ^ 2 := by
    apply RealTangentSpace.maj_le_norm_sq
  calc ‖X.Hf z τ (u τ) (w.val τ)‖ ^ 2 * X.maj z τ (Data.emb τ.1 ξ)
      ≤ (X.maj z τ (u τ) * X.maj z τ (w.val τ)) * X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right hcs hme
    _ ≤ (X.maj z τ (u τ) * (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0)) *
        X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmw.trans hwM) hmu) hme
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) *
        (X.k0 * X.maj z τ (Data.emb τ.1 ξ)) := by ring
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) := by
        rw [hc, mul_one]

end ReciprocityTheory.ChartRestriction.G.FD
end
end
