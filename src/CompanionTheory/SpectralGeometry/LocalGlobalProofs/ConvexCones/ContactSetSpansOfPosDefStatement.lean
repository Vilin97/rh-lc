module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraintsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSetStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.RingTheory.PiTensorProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbationStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsMin2IffFinite

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_iff_finite : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (y : X),
    (∀ i x, 0 ≤ u i x x) → ∃ F : Finset X, ∀ B ∈ rcone u,
      (IsMin2 B y ↔ ∀ x ∈ F, B y y ≤ B (y + (x + x)) (y + (x + x))) := by
  intro X _ m u y hu
  obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := X) m fun x i => (u i (y + (x + x)) (y + (x + x))).toNat
  refine ⟨F, ?_⟩
  rintro B ⟨t, ht, rfl⟩
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  obtain ⟨x', hx', hle⟩ := hF x
  refine (h x' hx').trans ?_
  have hval : ∀ a : X, (∑ i, t i • toReal (u i)) a a = ∑ i, t i * (u i a a : ℝ) := fun a => by
    simp [LinearMap.sum_apply]
  simp only [hval]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
  have h1 := hle i
  have h2 := hu i (y + (x' + x'))
  have h3 := hu i (y + (x + x))
  simp only at h1
  exact_mod_cast (by omega : u i (y + (x' + x')) (y + (x' + x')) ≤ u i (y + (x + x)) (y + (x + x)))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominating

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem contact_inter_rcone_spanned : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι]
    (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) →
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
      (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd
  classical
  choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd
  let A : Set (Fin m → ℤ) := ⋃ i, (fun (x : X) (k : Fin m) =>
    u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)
  let V : Set (Fin m → ℤ) := Set.range fun (p : O × X × X) (k : Fin m) =>
    u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)
  have hA : A.Finite := Set.finite_iUnion fun i => (F i).finite_toSet.image _
  obtain ⟨r, v, hv, -⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A V hA
  have hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ) :=
    fun t y z => by simp [LinearMap.sum_apply]
  have hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k =
      (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q' := fun t p p' q q' => by
    rw [hval, hval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔
      ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0) := fun t ht => by
    constructor
    · intro h b hb
      obtain ⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m =>
          u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by
        simpa [A] using hb
      rw [hdiff]
      linarith [h i x]
    · intro h i
      refine (hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_
      have := h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
      rw [hdiff] at this
      linarith
  have hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z =
      (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0 := fun t => by
    constructor
    · rintro h _ ⟨⟨c, y, z⟩, rfl⟩
      simp only []
      rw [hdiff, h, sub_self]
    · intro h c y z
      have := h _ ⟨(c, y, z), rfl⟩
      simp only [] at this
      rw [hdiff] at this
      linarith
  let γ : Fin r → LinearMap.BilinForm ℤ X := fun s => ∑ k, v s k • u k
  have hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z := fun s y z => by
    simp [γ, LinearMap.sum_apply]
  have hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k) := fun s => LinearMap.ext₂ fun y z => by
    rw [hval, toReal_apply, hγ]
    push_cast
    rfl
  have hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧
      (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0) := fun s => by
    refine (hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩
    · by_cases h : j = s
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      simp
  have hbal : ∀ s, γ s ∈ balForms bar X := fun s => by
    refine mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩
    · simp only [hγ, hsym _ y z]
    · have := (hViff _).2 (hvs s).2.2 c y z
      rw [← hγr] at this
      simpa using this
  have hnn : ∀ s y, 0 ≤ γ s y y := fun s y => by
    rw [hγ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)
  refine ⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa using hbal s) (by simpa using hnn s) (by simp)
  · rw [hγr]
    exact (hAiff _ (hvs s).1).2 (hvs s).2.1 i
  · rintro _ hB ⟨t, ht, rfl⟩
    have hre := mem_realForms_of_mem_psdCone hB.1
    obtain ⟨c, hc, rfl⟩ := (hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩
    refine ⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩
    rw [hval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominatingStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.exists_balanced_forms_dominating : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | exact GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsPosDefAddAndMemPsdCone

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Module.Finite ℤ Y ∧ Module.Free ℤ Y := by
  have hfin : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by
    simpa using LinearMap.congr_fun hs y)
  have htf : Module.IsTorsionFree ℤ Y := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n y h
    by_contra hc
    push_neg at hc
    have h1 : ((n : O)) • y = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : (n : O) • s y = 0 := by rw [← map_smul, h1, map_zero]
    have hy : s y ≠ 0 := fun h0 => hc.2 (hinj (by rw [h0, map_zero]))
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hy
    have h3 := DFunLike.congr_fun h2 a
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha
    exact (mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem sum_nonneg_of_isPosDef {Y ι : Type} [AddCommGroup Y] [Fintype ι] (b : Module.Basis ι ℤ Y)
    {B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ} (h : IsPosDef B) {n : ℕ} (y : Fin n → Y) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B (y i) (y j) := by
  have hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l) := fun i j => by
    conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) *
      (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l) := by
    symm
    simp only [hy, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [key]
  by_cases hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0
  · have hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0 := fun k => congrFun hd k
    simp [hd']
  · exact ((isPosDef_iff_basis b B).1 h _ hd).le

theorem sum_nonneg_of_mem_psdCone (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X))
    {n : ℕ} (x : Fin n → X) (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_int_of_projective O X₁
  simp only [h2]
  exact sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c

theorem isPosDef_add_and_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : B ∈ psdCone (bar := bar) (X := X)) (hB₀ : B₀ ∈ realForms bar X) (h₀ : IsPosDef B₀) :
    IsPosDef (B + B₀) ∧ B + B₀ ∈ psdCone (bar := bar) (X := X) := by
  have hpos : IsPosDef (B + B₀) := fun n x hx c hc => by
    have h1 := sum_nonneg_of_mem_psdCone O hB x c
    have h2 := h₀ n x hx c hc
    have h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) =
        ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j) := by
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h3]
    exact add_pos_of_nonneg_of_pos h1 h2
  exact ⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDef

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SlopeTestRemainingChoices

variable {X : Type} [AddCommGroup X]

theorem IsMin2.add {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) (h' : IsMin2 B' y) : IsMin2 (B + B') y :=
  fun x => by
    simpa only [LinearMap.add_apply] using add_le_add (h x) (h' x)

theorem IsMin2.smul {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) {t : ℝ} (ht : 0 ≤ t) : IsMin2 (t • B) y :=
  fun x => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (h x) ht

theorem isPosDef_smul_of_pos {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) {t : ℝ} (ht : 0 < t) : IsPosDef (t • B) :=
  fun n x hx c hc => by
    have key : ∑ i, ∑ j, c i * c j * (t • B) (x i) (x j) = t * ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    exact mul_pos ht (h n x hx c hc)

theorem rcone_subset_sigma {k : ℕ} {s : Fin k → ℕ} (γ : ∀ j, Fin (s j) → LinearMap.BilinForm ℤ X) {N : ℕ}
    (e : (Σ j, Fin (s j)) ≃ Fin N) (j : Fin k) :
    rcone (γ j) ⊆ rcone (fun i => γ (e.symm i).1 (e.symm i).2) := by
  rintro B ⟨t, ht, rfl⟩
  have hinj : Function.Injective (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) := fun b c h => by simpa using h
  let T : (Σ j, Fin (s j)) → ℝ := Function.extend (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) t 0
  have hT : ∀ b, T ⟨j, b⟩ = t b := fun b => hinj.extend_apply t 0 b
  have hT0 : ∀ a, a ≠ j → ∀ b, T ⟨a, b⟩ = 0 := fun a ha b => by
    refine (Function.extend_apply' _ _ _ ?_).trans rfl
    rintro ⟨c, hc⟩
    exact ha (congrArg Sigma.fst hc).symm
  have hTn : ∀ p, 0 ≤ T p := fun ⟨a, b⟩ => by
    by_cases ha : a = j
    · subst ha
      rw [hT]
      exact ht b
    · rw [hT0 a ha]
  refine ⟨fun i => T (e.symm i), fun i => hTn _, ?_⟩
  rw [e.symm.sum_comp (fun p => T p • toReal (γ p.1 p.2)), Fintype.sum_sigma,
    Finset.sum_eq_single j (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hT0 a ha, zero_smul])
      (fun h => (h (Finset.mem_univ j)).elim)]
  exact Finset.sum_congr rfl fun b _ => by rw [hT]

end SlopeTestRemainingChoices

theorem isSpanned_contact_of_posDef : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR hC ⟨B₀, hB₀, hd⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨k, m, u, hsym, hnn, hcov⟩ := GlobalTheory.T.exists_psd_forms_cover_contact_set O bar X ι a hR hC
  choose s γ hbal hγnn hγK hsub using fun j => GlobalTheory.T.exists_balanced_forms_dominating O bar X ι a (m j) (u j) (hsym j) (hnn j)
  let e := Fintype.equivFin (Σ j, Fin (s j))
  refine ⟨_, fun i => γ (e.symm i).1 (e.symm i).2, fun i => hbal _ _, fun i y => hγnn _ _ _, fun i => hγK _ _,
    fun B hB => ?_⟩
  refine GlobalTheory.T.mem_rational_cone_of_perturbation X _ _ B B₀ fun ε hε => ?_
  have hεd : IsPosDef (ε • B₀) := isPosDef_smul_of_pos hd hε
  have hεr : ε • B₀ ∈ realForms bar X := (realForms bar X).smul_mem ε (mem_realForms_of_mem_psdCone hB₀.1)
  obtain ⟨hpd, hps⟩ := isPosDef_add_and_mem_psdCone O bar X B (ε • B₀) hB.1 hεr hεd
  have hmem : B + ε • B₀ ∈ contact bar a := ⟨hps, fun i => (hB.2 i).add ((hB₀.2 i).smul hε.le)⟩
  obtain ⟨j, hj⟩ := hcov _ hmem hpd
  exact rcone_subset_sigma γ e j (hsub j _ hmem hj)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDefStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.contact_set_spans_of_pos_def : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | exact GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef <;> assumption)
end
end
