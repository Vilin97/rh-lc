module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevel
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevelStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.finite_pos_def_form_sublevel : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) → ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | exact GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFiniteBelowModTwo

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_finite_below_mod_two {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] {m : ℕ}
    (f : X → Fin m → ℕ) :
    ∃ G : Set X, G.Finite ∧ ∀ y, ∃ y' ∈ G, (∃ x : X, y' = y + (x + x)) ∧ f y' ≤ f y := by
  classical
  have hmin : ∀ (V : Set (Fin m → ℕ)) (a : Fin m → ℕ), a ∈ V → ∃ v, Minimal (· ∈ V) v ∧ v ≤ a := by
    intro V a ha
    obtain ⟨v, ⟨hvV, hva⟩, hvmin⟩ := wellFounded_lt.has_min {w | w ∈ V ∧ w ≤ a} ⟨a, ha, le_rfl⟩
    refine ⟨v, ⟨hvV, fun w hwV hwv => ?_⟩, hva⟩
    by_contra hne
    exact hvmin w ⟨hwV, hwv.trans hva⟩ (lt_of_le_of_ne hwv fun h => hne (le_of_eq h.symm))
  set e := (Module.finBasis ℤ X).equivFun with he
  have key : ∀ y : X, ∃ x : X,
      e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y + (x + x) := by
    intro y
    refine ⟨e.symm (fun i => -(e y i / 2)), ?_⟩
    apply e.injective
    rw [map_add (f := _), map_add (f := _), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext i
    simp only [ZMod.val_intCast, Pi.add_apply, Nat.cast_ofNat]
    rw [Int.emod_def]
    ring
  let red : X → (Fin (Module.finrank ℤ X) → ZMod 2) := fun y i => ((e y i : ℤ) : ZMod 2)
  have hred : ∀ y y' : X, red y' = red y → ∃ x : X, y' = y + (x + x) := by
    intro y y' h
    obtain ⟨x1, h1⟩ := key y
    obtain ⟨x2, h2⟩ := key y'
    refine ⟨x1 - x2, ?_⟩
    have hh : (fun i => ((e y' i : ℤ) : ZMod 2)) = (fun i => ((e y i : ℤ) : ZMod 2)) := h
    have h2' : e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y' + (x2 + x2) := by
      rw [← h2]
      congr 1
      funext i
      rw [congrFun hh i]
    have h3 : y' + (x2 + x2) = y + (x1 + x1) := h2'.symm.trans h1
    rw [eq_sub_of_add_eq h3]
    abel
  let V : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => f '' {y | red y = ε}
  let M : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => {v | Minimal (· ∈ V ε) v}
  have hMfin : ∀ ε, (M ε).Finite := fun ε =>
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain fun x => x ∈ V ε)
  let pick : (Fin (Module.finrank ℤ X) → ZMod 2) → (Fin m → ℕ) → X := fun ε v =>
    if h : ∃ y, red y = ε ∧ f y = v then h.choose else 0
  refine ⟨⋃ ε, pick ε '' M ε, Set.finite_iUnion fun ε => (hMfin ε).image _, fun y => ?_⟩
  obtain ⟨v, hvM, hvle⟩ := hmin (V (red y)) (f y) ⟨y, rfl, rfl⟩
  have hex : ∃ w, red w = red y ∧ f w = v := by
    obtain ⟨w, hw, hwv⟩ := hvM.1
    exact ⟨w, hw, hwv⟩
  have hpick : red (pick (red y) v) = red y ∧ f (pick (red y) v) = v := by
    dsimp only [pick]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨pick (red y) v, Set.mem_iUnion.mpr ⟨red y, v, hvM, rfl⟩, hred y _ hpick.1, ?_⟩
  rw [hpick.2]
  exact hvle

theorem finite_isMin2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (m : ℕ)
    (P : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) →
    ∃ F : Set X, F.Finite ∧ ∀ B ∈ rcone P, IsPosDef B → ∀ y, IsMin2 B y → y ∈ F := by
  intro X _ _ _ m P hsym hnn
  classical
  obtain ⟨G, hG, hGy⟩ := exists_finite_below_mod_two (fun y i => (P i y y).toNat)
  set C : ℤ := ∑ g ∈ hG.toFinset, ∑ i, P i g g with hC
  let Q : Finset (Fin m) → LinearMap.BilinForm ℤ X := fun S => ∑ i ∈ S, P i
  have hQ : ∀ S z w, Q S z w = ∑ i ∈ S, P i z w := by
    intro S z w
    simp [Q, LinearMap.sum_apply]
  refine ⟨⋃ S : Finset (Fin m), if (∀ y : X, y ≠ 0 → 0 < Q S y y) then {y | Q S y y ≤ S.card * C} else ∅,
    ?_, ?_⟩
  · refine Set.finite_iUnion fun S => ?_
    split_ifs with hpos
    · exact GlobalTheory.T.finite_pos_def_form_sublevel X (Q S) (fun y z => by
        rw [hQ, hQ]
        exact Finset.sum_congr rfl fun i _ => hsym i y z) hpos _
    · exact Set.finite_empty
  · rintro B ⟨t, ht0, rfl⟩ hB y hy
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter (fun i => 0 < t i) := ⟨_, rfl⟩
    have hBapp : ∀ z w : X, (∑ i, t i • GlobalTheory.PolFan.toReal (P i)) z w = ∑ i, t i * ((P i z w : ℤ) : ℝ) := by
      intro z w
      simp [GlobalTheory.PolFan.toReal, LinearMap.sum_apply]
    have hBpos : ∀ z : X, z ≠ 0 → 0 < ∑ i, t i * ((P i z z : ℤ) : ℝ) := by
      intro z hz
      have h1 := hB 1 ![z] (linearIndependent_unique_iff.mpr (by simpa using hz)) ![1] (by simp)
      simpa [hBapp] using h1
    have hterm : ∀ z : X, ∑ i, t i * ((P i z z : ℤ) : ℝ) = ∑ i ∈ S, t i * ((P i z z : ℤ) : ℝ) := by
      intro z
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · have h0 : t i = 0 := le_antisymm (not_lt.mp h) (ht0 i)
        simp [h0]
    have hpos : ∀ z : X, z ≠ 0 → 0 < Q S z z := by
      intro z hz
      rw [hQ]
      by_contra hle
      have h0 : ∑ i ∈ S, P i z z = 0 := le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => hnn i z)
      have hzero : ∀ i ∈ S, P i z z = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i z).mp h0
      have h1 := hBpos z hz
      rw [hterm, Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; simp] at h1
      exact lt_irrefl _ h1
    obtain ⟨y', hy'G, ⟨x, hx⟩, hle⟩ := hGy y
    have hle' : ∀ i, P i y' y' ≤ P i y y := fun i => by
      have h1 : (P i y' y').toNat ≤ (P i y y).toNat := hle i
      have h2 := hnn i y
      have h3 := hnn i y'
      omega
    have hmin : ∑ i, t i * ((P i y y : ℤ) : ℝ) ≤ ∑ i, t i * ((P i y' y' : ℤ) : ℝ) := by
      have h1 := hy x
      rw [← hx, hBapp, hBapp] at h1
      exact h1
    have hd : ∀ i ∈ Finset.univ, 0 ≤ t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) := fun i _ =>
      mul_nonneg (ht0 i) (sub_nonneg.mpr (by exact_mod_cast hle' i))
    have hsum : ∑ i, t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) = 0 := by
      apply le_antisymm
      · simp only [mul_sub, Finset.sum_sub_distrib]
        linarith
      · exact Finset.sum_nonneg hd
    have heq : ∀ i ∈ S, P i y y ≤ P i y' y' := by
      intro i hi
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hsum i (Finset.mem_univ i)
      rw [hS, Finset.mem_filter] at hi
      have h4 : ((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp hi0 with h | h
        · exact absurd h hi.2.ne'
        · exact h
      have h5 : ((P i y y : ℤ) : ℝ) ≤ ((P i y' y' : ℤ) : ℝ) := by linarith
      exact_mod_cast h5
    have hbound : ∀ i, P i y' y' ≤ C := by
      intro i
      rw [hC]
      calc P i y' y' ≤ ∑ j, P j y' y' := Finset.single_le_sum (fun j _ => hnn j y') (Finset.mem_univ i)
        _ ≤ ∑ g ∈ hG.toFinset, ∑ j, P j g g :=
          Finset.single_le_sum (f := fun g => ∑ j, P j g g)
            (fun g _ => Finset.sum_nonneg fun j _ => hnn j g) (hG.mem_toFinset.mpr hy'G)
    refine Set.mem_iUnion.mpr ⟨S, ?_⟩
    rw [if_pos hpos]
    show Q S y y ≤ S.card * C
    rw [hQ]
    calc ∑ i ∈ S, P i y y ≤ ∑ i ∈ S, C := Finset.sum_le_sum fun i hi => (heq i hi).trans (hbound i)
      _ = S.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntEqZeroOfForallTwoPowDvd

section

@[expose] public section

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem int_eq_zero_of_forall_two_pow_dvd (n : ℤ) (h : ∀ k : ℕ, (2 : ℤ) ^ k ∣ n) : n = 0 := by
  refine Int.eq_zero_of_abs_lt_dvd (h n.natAbs) ?_
  have h1 : n.natAbs < 2 ^ n.natAbs := Nat.lt_two_pow_self
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

theorem exists_two_pow_smul_of_covers2 {X : Type} [AddCommGroup X] {ι : Type} {a : ι → X}
    (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) (k : ℕ) :
    ∀ y : X, ∃ z : X, d y = ((2 : ℤ) ^ k) • z := by
  induction k with
  | zero => exact fun y => ⟨d y, by simp⟩
  | succ k ih =>
    intro y
    obtain ⟨i, x, rfl⟩ := ha y
    obtain ⟨z, hz⟩ := ih x
    refine ⟨z, ?_⟩
    rw [map_add (f := _), map_add (f := _), hd, hz, zero_add, pow_succ, mul_smul, two_smul]
    simp only [two_smul, smul_add]

theorem addHom_eq_zero_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) : d = 0 := by
  ext y
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun j => ?_)
  have : b.repr (d y) j = 0 := by
    refine int_eq_zero_of_forall_two_pow_dvd _ fun k => ?_
    obtain ⟨z, hz⟩ := exists_two_pow_smul_of_covers2 ha d hd k y
    exact ⟨b.repr z j, by rw [hz]; simp⟩
  simpa using this

theorem addHom_ext_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) {f g : X →+ X} (h : ∀ i, f (a i) = g (a i)) : f = g := by
  have := addHom_eq_zero_of_covers2 ha (f - g) (fun i => by simp [h i])
  exact sub_eq_zero.mp this

theorem finite_addHom_of_covers2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (ι : Type)
    [Finite ι] (a : ι → X), Covers2 a → ∀ F : Set X, F.Finite → {f : X →+ X | ∀ i, f (a i) ∈ F}.Finite := by
  intro X _ _ _ ι _ a ha F hF
  have hT : (Set.pi Set.univ fun _ : ι => F).Finite := Set.Finite.pi fun _ => hF
  refine Set.Finite.of_injOn (f := fun (f : X →+ X) (i : ι) => f (a i)) ?_ ?_ hT
  · exact fun f hf i _ => hf i
  · exact fun f _ g _ h => addHom_ext_of_covers2 ha fun i => congrFun h i

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSet

section

@[expose] public section

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem finite_free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Module.Finite ℤ X ∧ Module.Free ℤ X := by
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hinj : Function.Injective s := fun x y h => by
    have := congrArg (Finsupp.linearCombination O id) h
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hinj ?_)
    rw [map_zero]
    ext c
    have h1 : r • s x = 0 := by
      rw [← map_zsmul s r x, hx, map_zero]
    have h2 : r • (s x c) = 0 := by simpa using DFunLike.congr_fun h1 c
    rw [zsmul_eq_mul] at h2
    have h3 : (r : O) ≠ 0 := by exact_mod_cast hr
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem exists_fin_reindex {T : Type} [Finite T] {X : Type} [AddCommGroup X] (m' : T → ℕ)
    (u' : ∀ t, Fin (m' t) → LinearMap.BilinForm ℤ X) (hsym : ∀ t i y z, u' t i y z = u' t i z y)
    (hnn : ∀ t i y, 0 ≤ u' t i y y) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∃ t, B ∈ rcone (u' t)) → ∃ j, B ∈ rcone (u j) := by
  obtain ⟨k, ⟨eq⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨k, fun j => m' (eq.symm j), fun j => u' (eq.symm j), fun j => hsym _, fun j => hnn _, ?_⟩
  rintro B ⟨t, ht⟩
  refine ⟨eq t, ?_⟩
  have key : ∀ t', t' = t → B ∈ rcone (u' t') := by
    rintro _ rfl
    exact ht
  exact key _ (eq.symm_apply_apply t)

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem isPosDef_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : IsPosDef B) :
    IsPosDef (pullR e.toLinearMap B) := by
  intro n x hx c hc
  let eZ : X ≃ₗ[ℤ] X := e.toAddEquiv.toIntLinearEquiv
  have h1 : LinearIndependent ℤ (fun i => e (x i)) := hx.map' eZ.toLinearMap eZ.ker
  simpa using hB n _ h1 c hc

theorem isMin2_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (hy : IsMin2 B y) :
    IsMin2 (pullR e.toLinearMap B) (e.symm y) := by
  intro x
  have := hy (e x)
  simpa [pullR_apply, map_add (f := _)] using this

theorem exists_rcone_cover_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
    HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR ha
  obtain ⟨hfin, hfree⟩ := finite_free_int_of_projective O X
  obtain ⟨k, n, P, hsym, hnn, hcov⟩ := hR
  choose F hF hmin using fun j => finite_isMin2 X (n j) (P j) (hsym j) (hnn j)
  have hU : (⋃ j, F j).Finite := Set.finite_iUnion hF
  have hS := finite_addHom_of_covers2 X ι a ha _ hU
  let S : Set (X →+ X) := {f : X →+ X | ∀ i, f (a i) ∈ ⋃ j, F j}
  have hSf : Finite S := hS
  let form : ∀ (t : (Fin k) × S), Fin (n t.1) → LinearMap.BilinForm ℤ X := fun t i =>
    (P t.1 i).compl₁₂ t.2.1.toIntLinearMap t.2.1.toIntLinearMap
  obtain ⟨K, m, u, h1, h2, h3⟩ := exists_fin_reindex (T := Fin k × S) (fun t => n t.1) form
    (fun t i y z => hsym _ _ _ _) (fun t i y => hnn _ _ _)
  refine ⟨K, m, u, h1, h2, fun B hB hpos => h3 B ?_⟩
  obtain ⟨e, j, c, hc, hE⟩ := hcov B hB.1
  let f : X →+ X := e.symm.toLinearMap.toAddMonoidHom
  have hf : f ∈ S := fun i => Set.mem_iUnion.2 ⟨j, hmin j _ ⟨c, hc, hE⟩ (isPosDef_pullR e hpos) _ (isMin2_pullR e (hB.2 i))⟩
  refine ⟨(j, ⟨f, hf⟩), c, hc, LinearMap.ext₂ fun y z => ?_⟩
  have h4 := LinearMap.congr_fun₂ hE (f y) (f z)
  simpa [f, form, LinearMap.sum_apply] using h4

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSetStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.exists_psd_forms_cover_contact_set : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X), (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧ ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact <;> assumption)
end
end
