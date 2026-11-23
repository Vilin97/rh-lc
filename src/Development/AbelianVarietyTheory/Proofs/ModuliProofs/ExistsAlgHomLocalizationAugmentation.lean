module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Mathlib.RingTheory.Trace.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
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
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetNotMemSpanMulVecOfSocle
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLocalPresentationSmoothGroupStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensorStatement

section

@[expose] public section

open scoped TensorProduct
theorem _root_.GlobalTheory.T.dvd_trace_of_tensor_lmul_eq : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  first | exact @GlobalTheory.dvd_trace_of_balanced_tensor | exact GlobalTheory.dvd_trace_of_balanced_tensor | (intros; apply GlobalTheory.dvd_trace_of_balanced_tensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPow

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_pow_mul_one_sub_mem_map_maximalIdeal (O H : Type) [CommRing O] [IsLocalRing O]
    [CommRing H] [Algebra O H] [Module.Finite O H] (u : H) :
    ∃ (N : ℕ) (y : H), u ^ N * (1 - y * u) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  set m := IsLocalRing.maximalIdeal O
  set J := m.map (algebraMap O H)
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite (O ⧸ m) (H ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (H ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := H ⧸ J) (M := H ⧸ J)
    (Ideal.Quotient.mk J u) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨N, y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one, pow_succ] at hy
  simp only [map_mul, map_pow, map_sub, map_one]
  linear_combination -hy

theorem exists_mul_kills_ker_of_localization (O H : Type) [CommRing O] [CommRing H] [Algebra O H]
    [Module.Finite O H] (ε : H →ₐ[O] O) (M : Submonoid H) (T : Type) [CommRing T] [Algebra H T]
    [IsLocalization M T] (u : H) (hu : ∀ h, ε h = 0 → algebraMap H T (h * u) = 0) :
    ∃ s : M, ∀ h, ε h = 0 → h * (s * u) = 0 := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := O) (M := H)
  have h1 : ∀ b : H, ∃ s : M, (s : H) * ((b - algebraMap O H (ε b)) * u) = 0 := fun b =>
    (IsLocalization.map_eq_zero_iff M T _).1 (hu _ (by simp))
  choose s hs using h1
  refine ⟨∏ b ∈ G, s b, fun h hh => ?_⟩
  have key : ∀ h : H, (h - algebraMap O H (ε h)) * (((∏ b ∈ G, s b : M) : H) * u) = 0 := by
    intro h
    have hmem : h ∈ Submodule.span O (G : Set H) := by rw [hG]; trivial
    induction hmem using Submodule.span_induction with
    | mem b hb =>
      rw [← Finset.mul_prod_erase G s hb, Submonoid.coe_mul]
      linear_combination ((∏ x ∈ G.erase b, s x : M) : H) * hs b
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      linear_combination ha + hb
    | smul c a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
      linear_combination algebraMap O H c * ha
  simpa [hh] using key h

theorem exists_integral_of_local_presentation :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  intro O H _ _ _ _ _ ε g n T _ _ _ _ _ εT hε S _ _ π x a ρ hπ hker hkerT ha hρx hρm
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set p : Ideal H := m.comap ε with hp
  have hmT : (m.map (algebraMap O H)).map (algebraMap H T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmS : (m.map (algebraMap O S)).map (π : S →+* T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  set A : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)) :=
    ρ.mapMatrix a with hA
  have hred : ∀ z : S, π z ∈ m.map (algebraMap O T) →
      ρ z ∈ Ideal.span (Set.range (A.mulVec MvPowerSeries.X)) := by
    intro z hz
    rw [← hmS] at hz
    have hz' : z ∈ m.map (algebraMap O S) ⊔ RingHom.ker π := by
      have := Ideal.comap_map_of_surjective (π : S →+* T) hπ (m.map (algebraMap O S))
      have h2 : z ∈ ((m.map (algebraMap O S)).map (π : S →+* T)).comap (π : S →+* T) := hz
      rw [this] at h2
      exact h2
    have hle : m.map (algebraMap O S) ⊔ RingHom.ker π ≤
        (Ideal.span (Set.range (A.mulVec MvPowerSeries.X))).comap ρ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        simp only [Ideal.mem_comap, hρm c hc, zero_mem]
      · rw [hker, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        refine Ideal.subset_span ⟨i, ?_⟩
        simp [hA, Matrix.mulVec, dotProduct, hρx]
    exact hle hz'
  have hx0 : ∀ i, εT (π (x i)) = 0 := fun i => by
    have : π (x i) ∈ RingHom.ker εT := by rw [hkerT]; exact Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hnil : ∀ i, ∃ N : ℕ, π (x i) ^ N ∈ m.map (algebraMap O T) := by
    intro i
    obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π (x i))
    have hu : ε u = 0 := by
      have := congrArg εT hut
      rw [map_mul, hx0, zero_mul, hε] at this
      exact this.symm
    obtain ⟨N, y, hy⟩ := exists_pow_mul_one_sub_mem_map_maximalIdeal O H u
    have hy' := Ideal.mem_map_of_mem (algebraMap H T) hy
    rw [hmT, map_mul, map_pow] at hy'
    have hunit : IsUnit (algebraMap H T (1 - y * u)) := by
      refine IsLocalization.map_units T (⟨1 - y * u, ?_⟩ : p.primeCompl)
      intro hc
      have hc' : ε (1 - y * u) ∈ m := hc
      rw [map_sub, map_mul, hu, mul_zero, sub_zero, map_one] at hc'
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hc')
    rw [Ideal.mul_unit_mem_iff_mem _ hunit] at hy'
    simp only at hut
    rw [← hut, mul_pow,
      Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.map_units T t).pow N)] at hy'
    exact ⟨N, hy'⟩
  choose N hN using hnil
  have hdet : π a.det ∉ m.map (algebraMap O T) := by
    intro hc
    refine det_notMem_span_mulVec_X _ g (Finset.univ.sup N) A (fun i => ?_) ?_
    · rw [← hρx, ← map_pow]
      apply hred
      rw [map_pow]
      exact Ideal.pow_mem_of_pow_mem _ (hN i) (Finset.le_sup (Finset.mem_univ i))
    · rw [hA, ← RingHom.map_det]
      exact hred _ hc
  have hkill : ∀ w : T, εT w = 0 → w * π a.det = 0 := by
    intro w hw
    have hw' : w ∈ RingHom.ker εT := hw
    rw [hkerT] at hw'
    have hle : Ideal.span (Set.range fun i => π (x i)) ≤
        LinearMap.ker (LinearMap.mulRight T (π a.det)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change π (x i) * π a.det = 0
      rw [← map_mul]
      change x i * a.det ∈ RingHom.ker π
      have h1 : x i * a.det = (a.adjugate.mulVec (a.mulVec x)) i := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp [mul_comm]
      rw [h1, hker]
      change ∑ j, a.adjugate i j * a.mulVec x j ∈ _
      exact Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    exact hle hw'
  have hval : εT (π a.det) = (n : O) ^ g := by
    have h1 : εT (π a.det) = ((εT.comp π).mapMatrix a).det := by
      rw [← AlgHom.map_det]; rfl
    have h2 : (εT.comp π).mapMatrix a = Matrix.diagonal fun _ => (n : O) := by
      ext i j
      simp [Matrix.diagonal_apply, ha]
    rw [h1, h2, Matrix.det_diagonal]
    simp
  obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π a.det)
  simp only at hut
  obtain ⟨s, hs⟩ := exists_mul_kills_ker_of_localization O H ε p.primeCompl T u (fun h hh => by
    rw [map_mul, ← hut, ← mul_assoc, hkill _ (by rw [hε, hh]), zero_mul])
  refine ⟨s * u, hs, ?_, fun hc => hdet ?_⟩
  · have := congrArg εT hut
    rw [map_mul, hval, hε, hε] at this
    rw [map_mul, ← this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · have hc' := Ideal.mem_map_of_mem (algebraMap H T) hc
    rw [hmT, map_mul, Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units T s), ← hut,
      Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units T t)] at hc'
    exact hc'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPowStatement

section

@[expose] public section

open scoped TensorProduct
theorem _root_.GlobalTheory.T.exists_integral_of_local_presentation_pow : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  first | exact @GlobalTheory.exists_integral_of_local_presentation | exact GlobalTheory.exists_integral_of_local_presentation | (intros; apply GlobalTheory.exists_integral_of_local_presentation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  first | exact @GlobalTheory.TorsionTheta.exists_theta | exact GlobalTheory.TorsionTheta.exists_theta | (intros; apply GlobalTheory.TorsionTheta.exists_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgHomLocalizationAugmentation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_algHom_localization_augmentation (O : Type) [CommRing O] [IsLocalRing O]
    (H : Type) [CommRing H] [Algebra O H] (ε : H →ₐ[O] O) :
    ∃ εT : Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε) →ₐ[O] O,
      ∀ h, εT (algebraMap H _ h) = ε h := by

  have hunit : ∀ s : ((IsLocalRing.maximalIdeal O).comap ε).primeCompl, IsUnit (ε s) := by
    intro s
    by_contra hs
    apply s.2
    show ε s ∈ IsLocalRing.maximalIdeal O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hs
  refine ⟨IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal O).comap ε).primeCompl)
    (S := Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) hunit, fun h => ?_⟩
  rw [IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq hunit h

theorem pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by
  intro O _ _ G _ _ n H _ _ _ _ y g hsm hy huniv h

  obtain ⟨ε, hε, -⟩ := huniv O 1 (one_pow n)
  obtain ⟨εT, hεT⟩ := exists_algHom_localization_augmentation O H ε

  obtain ⟨S, _, _, π, x, a, ρ, hπ, hker, hkerε, ha, hρ, hρm⟩ :=
    GlobalTheory.T.torsion_local_presentation_smooth_group O G n H y g hsm hy huniv ε hε
      (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT

  obtain ⟨l, hl, hdvd, hlm⟩ :=
    GlobalTheory.T.exists_integral_of_local_presentation_pow O H ε g n (Localization.AtPrime ((IsLocalRing.maximalIdeal O).comap ε)) εT hεT
      S π x a ρ hπ hker hkerε ha hρ hρm

  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_diagonal_element_lmul_eq_nonzero_geometric_points O G n H y hy huniv ε l (ε l) hε hl rfl hlm
  exact dvd_trans hdvd (GlobalTheory.T.dvd_trace_of_tensor_lmul_eq O H Θ (ε l) hΘ h)

end GlobalTheory
end
end
