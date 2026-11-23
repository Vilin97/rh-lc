module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCoverStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Mathlib.RingTheory.PiTensorProduct
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsNatCombOfToRealMemRcone

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_nat_comb_of_toReal_mem_rcone (X : Type) [AddCommGroup X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) (hβ : toReal β ∈ rcone γ) :
    ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i := by
  obtain ⟨t, ht0, ht⟩ := hβ
  let vec : X × X → Fin (m + 1) → ℤ := fun p =>
    Fin.snoc (α := fun _ => ℤ) (fun i => γ i p.1 p.2) (-(β p.1 p.2))
  obtain ⟨r, v, hreal, -⟩ :=
    GlobalTheory.MinkWeylReal.cone_orthant_fg (m + 1) ∅ (Set.range vec) Set.finite_empty
  let T : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) t 1
  have hpt : ∀ y z : X, (β y z : ℝ) = ∑ i, t i * (γ i y z : ℝ) := by
    intro y z
    have h := LinearMap.congr_fun (LinearMap.congr_fun ht y) z
    simpa [toReal, LinearMap.sum_apply] using h
  have hT : (∀ i, 0 ≤ T i) ∧ (∀ a ∈ (∅ : Set (Fin (m + 1) → ℤ)), ∑ i, (a i : ℝ) * T i ≤ 0) ∧
      (∀ b ∈ Set.range vec, ∑ i, (b i : ℝ) * T i = 0) := by
    refine ⟨fun i => ?_, fun a ha => absurd ha (Set.notMem_empty a), ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [T]
      · simpa [T] using ht0 j
    · rintro _ ⟨⟨y, z⟩, rfl⟩
      rw [Fin.sum_univ_castSucc]
      simp only [vec, T, Fin.snoc_castSucc, Fin.snoc_last]
      have h2 : ∑ x, ((γ x y z : ℤ) : ℝ) * t x = ∑ i, t i * (γ i y z : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have h3 := hpt y z
      push_cast
      linarith
  obtain ⟨c, hc0, hTc⟩ := (hreal T).1 hT
  have hlast : (1 : ℝ) = ∑ k, c k * (v k (Fin.last m) : ℝ) := by
    have h := congrFun hTc (Fin.last m)
    simpa [T, Finset.sum_apply] using h
  have hex : ∃ k, 0 < v k (Fin.last m) := by
    by_contra hno
    push_neg at hno
    have : ∑ k, c k * (v k (Fin.last m) : ℝ) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have : v k (Fin.last m) = 0 := Nat.le_zero.1 (hno k)
        simp [this]
    rw [this] at hlast
    exact one_ne_zero hlast
  obtain ⟨k, hk⟩ := hex
  have hv := (hreal (fun i => (v k i : ℝ))).2
    ⟨Pi.single k 1, fun j => by
      by_cases h : j = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h], by
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp⟩
  refine ⟨v k (Fin.last m), fun i => v k i.castSucc, hk, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have h := hv.2.2 (vec (y, z)) ⟨(y, z), rfl⟩
  rw [Fin.sum_univ_castSucc] at h
  simp only [vec, Fin.snoc_castSucc, Fin.snoc_last] at h
  have h' : ∑ i, γ i y z * (v k i.castSucc : ℤ) + -(β y z) * (v k (Fin.last m) : ℤ) = 0 := by
    exact_mod_cast h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul]
  push_cast
  have h2 : ∑ i, (v k i.castSucc : ℤ) * γ i y z = ∑ i, γ i y z * (v k i.castSucc : ℤ) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLift

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_sum_smul {X : Type} [AddCommGroup X] {m : ℕ} (B : Fin m → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c : Fin m → ℝ) (y : X)
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ i, IsMin2 (B i) y) : IsMin2 (∑ i, c i • B i) y := by
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i x) (hc i)

def sumDiag {X ι : Type} [AddCommGroup X] [Fintype ι] (g : ℕ) (p : ι → X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := 2 ^ g * ∑ y, β (p y) (p y)
  map_add' β γ := by
    simp only [LinearMap.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' k β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem isCell_vorFun_of_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ)
    (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) →
    (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ →
    IsCell bar (vorFun O g) γ := by
  intro O _ _ _ _ bar g X _ _ _ _ n r a hr ha m γ hbal hpsd hcon hsub
  have hval := (vorFun_value_le O bar g X n r a hr ha).2
  have hreal : ∀ (β : LinearMap.BilinForm ℤ X) , (∀ y, 0 ≤ β y y) → ∀ y, 0 ≤ toReal β y y := fun β hβ y => by
    simpa [toReal_apply] using hβ y
  have hℓ : ∀ β : LinearMap.BilinForm ℤ X, ((sumDiag g (fun y => r (a y)) β : ℤ) : ℝ) =
      2 ^ g * ∑ y, toReal β (r (a y)) (r (a y)) := fun β => by
    simp [sumDiag, toReal_apply]
  have hgen : ∀ i, (2 : ℝ) ^ n * (vorFun O g).evalZ (γ i) = sumDiag g (fun y => r (a y)) (γ i) := fun i => by
    rw [hℓ, ← evalR_toReal]
    exact (hval _ (hreal _ (hpsd i))).2.2 (hcon i).2
  refine ⟨hbal, hpsd, (linearOn_iff _ γ).2 fun c hc => ?_, 2 ^ n, sumDiag g (fun y => r (a y)), by positivity, ?_, ?_, ?_⟩
  · have hS : ∀ y, 0 ≤ (∑ i, c i • toReal (γ i)) y y := fun y => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hreal _ (hpsd i) y)
    have h1 := (hval _ hS).2.2 fun y => isMin2_sum_smul _ c _ hc fun i => (hcon i).2 y
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine mul_left_cancel₀ hp (h1.trans ?_)
    have h2 : ∀ i, (2 : ℝ) ^ g * ∑ y, toReal (γ i) (r (a y)) (r (a y)) = 2 ^ n * (vorFun O g).evalZ (γ i) := fun i => by
      rw [hgen, hℓ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, h2, mul_left_comm]
  · intro i
    push_cast
    exact (hgen i).symm
  · intro β _ hβ
    have h := (hval _ (hreal β hβ)).1
    rw [evalR_toReal] at h
    rw [hℓ]
    push_cast
    exact h
  · intro β hb hβ he
    have hmin : ∀ y, IsMin2 (toReal β) (r (a y)) := by
      refine (hval _ (hreal β hβ)).2.1 ?_
      rw [evalR_toReal, ← hℓ]
      exact_mod_cast he
    have hpc : toReal β ∈ psdCone (bar := bar) (X := X) := by
      simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hb]) (by simp [hβ]) (by simp)
    exact exists_nat_comb_of_toReal_mem_rcone X m γ β (hsub ⟨hpc, hmin⟩)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLiftStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ → IsCell bar (vorFun O g) γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbits

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_vorFun_cells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar g hcov X _ _ _ _
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov X
  have hcls : ∀ (j : Fin k) (y : Fin n → ZMod (1 + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV 1 a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, ∀ a', redV 1 a' = y → B (r a) (r a) ≤ B (r a') (r a') := by
    intro j y
    obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := {a : Fin n → ℤ // redV 1 a = y}) (nP j)
      fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective 1 n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, fun a ha => ?_⟩
      obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
      refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
      simp only [Function.Embedding.subtype_apply, hval]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have h1 := hle i
      have h2 := hPp j i (r a'.1)
      have h3 := hPp j i (r a)
      simp only at h1
      exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  have hred : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)) (y : Fin n → ZMod (1 + 1)), redV 1 (c y).1 = y :=
    fun j c y => hFred j y _ (c y).2
  have cell : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)), ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X),
      IsCell bar (vorFun O g) γ ∧ (contact bar fun y => r (c y).1) ⊆ rcone γ := by
    intro j c
    have hcv := (vorFun_value_le O bar g X n r (fun y => (c y).1) hr (hred j c)).1
    obtain ⟨s, γ, h1, h2, h3, h4⟩ := GlobalTheory.T.contact_set_spanned_of_cover O bar hcov X _ _ hcv
    exact ⟨s, γ, GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone O bar g X n r _ hr (hred j c) s γ h1 h2 h3 h4, h4⟩
  choose s γ hγ hγc using cell
  refine ⟨⋃ j, ⋃ c, Set.range (γ j c), Set.finite_iUnion fun j => Set.finite_iUnion fun c => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone (bar := bar) (X := X) := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  choose a0 ha0F ha0 using fun y => hFmin j y _ hBP
  let d : ∀ y, ↥(F j y) := fun y => ⟨a0 y, ha0F y⟩
  have hcon : pullR e.toLinearMap B ∈ contact bar fun y => r (d y).1 := by
    refine ⟨hB', fun y x => ?_⟩
    obtain ⟨b, rfl⟩ := hr x
    have hb : redV 1 (a0 y + (b + b)) = y := by
      have h2 : a0 y + (b + b) = a0 y + (((1 : ℕ) : ℤ) + 1) • b := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [h2, redV_add_smul]
      exact hFred j y _ (ha0F y)
    simpa only [map_add (f := _)] using ha0 y _ hb
  obtain ⟨c', hc', hBc⟩ := hγc j d hcon
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbitsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.psd_cone_finitely_many_orbits : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells <;> assumption)
end
end
