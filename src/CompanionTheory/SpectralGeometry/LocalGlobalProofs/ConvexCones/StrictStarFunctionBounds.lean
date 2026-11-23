module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedFormDecompositionBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CentreFunctionOneOnCellStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthGapOnCellStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestriction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthBoundedDenominator

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator

theorem starDepth_den : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
        ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  intro O _ _ _ _ bar hb q ψ w hψ hw
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  have key : ∀ k : Fin n, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ {x : ℝ | ∃ β ∈ balForms bar (R k), (∀ y, 0 ≤ β y y) ∧
      haveI := (hR k).1; x = (starDepth bar ψ w).evalZ β}, ∃ z : ℤ, (D : ℝ) * x = z := fun k => by
    haveI := (hR k).1
    haveI := (hR k).2.1
    obtain ⟨-, h2, h3⟩ := hw (R k) (hR k).2.2
    obtain ⟨D, hD, hA⟩ := GlobalTheory.PolFan.StarDen.module_den (hψ (R k) (hR k).2.2) h2 h3
    refine ⟨D, hD, ?_⟩
    rintro x ⟨β, hβ, hp, rfl⟩
    exact hA β (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hb (R k) β hβ hp)
  obtain ⟨D₀, hD₀, hall⟩ := GlobalTheory.PolFan.StarDen.common_den _ key
  refine ⟨D₀, hD₀, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  haveI := (hR k).1
  have hval : (starDepth bar ψ w).evalZ (pull f.symm.toLinearMap β) = (starDepth bar ψ w).evalZ β :=
    evalZ_pull _ f.symm.surjective β
  rw [← hval]
  exact hall k _ ⟨_, pull_mem _ hβ, fun y => hp _, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthBoundedDenominatorStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.star_depth_bounded_denominator : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionOffCell

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarOffCell

theorem off_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (b : ℕ), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → 0 < N → StrictWith bar ψ N ℓ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  intro O _ _ _ _ bar hb q ψ w b hψ hw X _ _ _ _ hX hgen m γ N ℓ hγ hN hsw β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos C hC K hK β hβ hβn
    hoff
  have hon := (GlobalTheory.T.mul_starDepth_le_faceCut_on_cell O bar hb q ψ w hψ hw X hX m γ hγ β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos).1
  obtain ⟨n, u, hu, hun, hlψ, hlp, hub, hu1, t, ht, hsum⟩ := hgen β hβ hβn
  have hh₀ : (1 : ℝ) ≤ h β₀ := by exact_mod_cast hpos
  have hoffu : ∀ i, ¬ InRCone γ (u i) → (N : ℝ) * h β₀ * (starDepth bar ψ w).evalZ (u i) - N * h (u i) <
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i hi => by
    obtain ⟨z, hz⟩ := (hψ X hX).integral (u i) (hu i) (hun i)
    have hle := hsw.2.1 (u i) (hu i) (hun i)
    have hne : (N : ℝ) * ψ.evalZ (u i) ≠ ℓ (u i) := fun e => by
      obtain ⟨k, c, hk, e'⟩ := hsw.2.2 (u i) (hu i) (hun i) e
      exact hi (GlobalTheory.PolFan.StarKey.OffCell.inRCone_of_nsmul hk e')
    have hlt : (N : ℤ) * z < ℓ (u i) := by
      have := lt_of_le_of_ne hle hne
      rw [hz] at this
      exact_mod_cast this
    have hf : (1 : ℝ) ≤ ℓ (u i) - N * ψ.evalZ (u i) := by
      rw [hz]
      have : (1 : ℤ) ≤ ℓ (u i) - N * z := by omega
      exact_mod_cast this
    refine GlobalTheory.PolFan.StarKey.OffCell.arith (C := C) (b := b) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh₀ hf rfl (hub i) (hu1 i) ?_ ?_
    · exact_mod_cast hC (u i) (hu i) (hun i)
    · exact_mod_cast hK
  have hall : ∀ i, (N : ℝ) * h β₀ * (starDepth bar ψ w).evalZ (u i) - N * h (u i) ≤
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i => by
    by_cases hi : InRCone γ (u i)
    · rw [GlobalTheory.PolFan.StarKey.ell_eq_of_inRCone hγ.linear hsw hi, sub_self, mul_zero, mul_assoc, ← mul_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (hon _ (hu i) (hun i) hi))
    · exact (hoffu i hi).le
  obtain ⟨i₀, hi₀, hi₀'⟩ : ∃ i, t i ≠ 0 ∧ ¬ InRCone γ (u i) := by
    by_contra hcon
    exact hoff (GlobalTheory.PolFan.StarKey.OffCell.inRCone_of_sum ht hsum fun i hi => by_contra fun h' => hcon ⟨i, hi, h'⟩)
  have e1 : ψ.evalZ β = ∑ i, t i * ψ.evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff ψ u).1 hlψ t ht
  have e2 : (starDepth bar ψ w).evalZ β = ∑ i, t i * (starDepth bar ψ w).evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff _ u).1 hlp t ht
  have key : ∑ i, t i * ((N : ℝ) * h β₀ * (starDepth bar ψ w).evalZ (u i) - N * h (u i)) <
      ∑ i, t i * (K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i))) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (ht i))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hoffu i₀ hi₀') (lt_of_le_of_ne (ht i₀) hi₀.symm)⟩
  rw [e1, e2, GlobalTheory.PolFan.StarKey.OffCell.lin_eq_sum hsum h, GlobalTheory.PolFan.StarKey.OffCell.lin_eq_sum hsum ℓ]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  convert key using 2 with i _ i _ <;> ring

end GlobalTheory.CompanionTheory.Ar.Fan.StarOffCell
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionOffCellStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.star_function_off_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (b : ℕ), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → 0 < N → StrictWith bar ψ N ℓ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarOffCell.off_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.StarOffCell.off_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarOffCell.off_cell <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.UniformCellBoundPolyhedralFan

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound

open GlobalTheory.PolFan.StrictData

theorem uniform_bound (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (hb : CMOrd O bar) (q : ℕ) (ψ : InvFun O) (hψ : IsPolyFan bar q ψ) :
    ∃ N₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ := by
  classical
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  have hfin : ∀ k, Module.Finite O (R k) := fun k => (hR k).1
  have key : ∀ k, ∃ N₀ : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)),
      IsCell bar ψ δ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ (R k) →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧
        StrictWith bar ψ N ℓ δ := fun k => by
    have := (hR k).2.1
    exact perModule_bound (hψ (R k) (hR k).2.2)
  choose N₀ hN₀ using key
  refine ⟨Finset.univ.sup N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ :=
    hN₀ k m (fun i => pull f.symm.toLinearMap (γ i)) (CellClass.isCell_pull_equiv hγ f.symm)
  exact ⟨N, _, hN, hNle.trans (Finset.le_sup (Finset.mem_univ k)), StrictWith.of_pull f.symm.surjective hℓ⟩

theorem exists_strict_data : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  intro O _ _ _ _ bar hb q ψ hDom hψ
  obtain ⟨N₀, hN₀⟩ := uniform_bound O bar hb q ψ hψ
  refine ⟨N₀, N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ := hN₀ X hX m γ hγ
  refine ⟨N, ℓ, hN, hNle, hℓ, fun m' s h hh => ?_⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  have hF := GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q ψ hψ X hX (hDom X) m γ hγ m' s h hh
  obtain ⟨NF, ℓF, -, hNFle, hℓF⟩ := hN₀ X hX m' _ hF
  obtain ⟨h1, h2, h3⟩ := faceCut_data (hψ X hX) hγ hN hℓ hh hℓF
  refine ⟨_, h1, h2, fun β hβ hp => (h3 β hβ hp).trans ?_⟩
  have hℓβ : (0 : ℤ) ≤ ℓ β := by
    have := le_trans (mul_nonneg (Nat.cast_nonneg _) (evalZ_nonneg (hψ X hX) hβ hp)) (hℓ.2.1 β hβ hp)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNFle) hℓβ

end GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.UniformCellBoundPolyhedralFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.uniform_cell_bound_polyhedral_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data | exact GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StrictStarFunctionBounds

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StrictStarFunction

theorem exists_starFun_strict : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict bar (starFun bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict bar (starFun bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  intro O _ _ _ _ bar hb q ψ w hdom hψ hcs
  obtain ⟨D₀, hD₀, hint⟩ := GlobalTheory.T.star_depth_bounded_denominator O bar hb q ψ w hψ hcs
  obtain ⟨N₀, C₀, hdata⟩ := GlobalTheory.T.uniform_cell_bound_polyhedral_fan O bar hb q ψ hdom hψ
  obtain ⟨b, hgens⟩ := GlobalTheory.T.balanced_form_decomposition_bound O bar hb q ψ w hψ hcs
  have hD₀r : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  refine ⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩
  · intro X _ _ _ _ hX β hβ hp
    obtain ⟨n₁, hn₁⟩ := (hψ X hX).integral β hβ hp
    obtain ⟨n₂, hn₂⟩ := hint X hX β hβ hp
    refine ⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩
    rw [starFun_evalZ, hn₁]
    push_cast
    linear_combination hn₂
  · intro X _ _ _ _ hX m γ hγ hnoc
    obtain ⟨N, ℓ, hN, hNN, hsw, -⟩ := hdata X hX m γ hγ
    have hgap := GlobalTheory.T.star_depth_gap_on_cell O bar hb q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw
    have hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth bar ψ w).evalZ β := fun β =>
      starDepth_eval_nonneg (fun a b => (β a b : ℝ))
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKN : (N : ℝ) + 1 ≤ K := by
      have : N + 1 ≤ K := by rw [hKdef]; omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · have h0 := hsw.1 i
      have hps : (starDepth bar ψ w).evalZ (γ i) = 0 :=
        le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)
      rw [starFun_evalZ, hps]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [h0]; ring
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      set P := (starDepth bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have k1 : (N : ℝ) * P ≤ K * (L - N * Ψ) := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      nlinarith [mul_le_mul_of_nonneg_left k1 hD₀r.le]
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, smul_eq_mul] at he
      push_cast at he
      set P := (starDepth bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have e1 : (N : ℝ) * P = K * (L - N * Ψ) := by
        have := mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)
        exact this
      have e2 : L - N * Ψ = 0 := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      exact hsw.2.2 β hβ hp (by linarith)
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos
    obtain ⟨N, ℓ, hN, hNN, hsw, hcuts⟩ := hdata X hX m γ hγ
    obtain ⟨h', hcut', hpos', hdom'⟩ := hcuts m' s h hcut
    have hp' : 0 < h' β₀ := hpos' β₀ hin₀ hpos
    obtain ⟨hin, hone, hzero, heq⟩ :=
      GlobalTheory.T.mul_starDepth_le_faceCut_on_cell O bar hb q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K := by
      rw [hKdef]
      have h1 : N * C₀ ≤ N₀ * C₀ := Nat.mul_le_mul_right _ hNN
      have h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))
      omega
    have hoff := GlobalTheory.T.star_function_off_cell O bar hb q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h'
      hcut' hp' C₀ hdom' K hKb
    have hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β := fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ
    have hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]
    have hH0 : (0 : ℝ) < h' β₀ := by exact_mod_cast hp'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by
      have : 0 < (h' β₀).toNat := by omega
      positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [starFun_evalZ, hone]
        have hl := hlinγ β₀ hin₀
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        push_cast
        rw [hcast, hl]; ring
      · simp only [Fin.cons_succ]
        have hh : h' (γ (s j)) = 0 := (hcut'.2 (s j)).2 ⟨j, rfl⟩
        rw [starFun_evalZ, hzero j]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]
        push_cast
        rw [hcast, hsw.1 (s j)]; ring
    · rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
      push_cast
      rw [hcast]
      set P := (starDepth bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        have hi := hin β hβ hp hc
        rw [hl]
        nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]
    · rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
      push_cast at he
      rw [hcast] at he
      set P := (starDepth bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        rw [hl] at he
        refine heq β hβ hp hc ?_
        have : ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ) := by linear_combination he
        exact mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]

end GlobalTheory.CompanionTheory.Ar.Fan.StrictStarFunction
end
end
