module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.OperatorsKillInvariantProjection
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsClearDenominators
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightSpaceEqBotOutsideSupport

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionPreservesLattice

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section pw
variable {n : ℕ} {K : Type} [Field K] {L W : Type} [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]

theorem llcomp_pow_apply (X : Module.End K W) (m : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.llcomp K L W W X) ^ m) f = (X ^ m) ∘ₗ f := by
  induction m generalizing f with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    rfl

theorem lcomp_pow_apply (Y : Module.End K L) (j : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.lcomp K W Y) ^ j) f = f ∘ₗ (Y ^ j) := by
  induction j generalizing f with
  | zero =>
    ext x
    simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    rfl

theorem homRepresentation_pow_apply (EL : GLOps n K L) (E : GLOps n K W) (a b : Fin n) (k : ℕ) (f : L →ₗ[K] W) (x : L) :
    ((homRepresentation EL E a b) ^ k) f x =
      ∑ m ∈ range (k + 1), ((k.choose m : K) * (-1) ^ (k - m)) • (E a b ^ m) (f ((EL a b ^ (k - m)) x)) := by
  have hc : Commute (LinearMap.llcomp K L W W (E a b)) ((-1 : K) • LinearMap.lcomp K W (EL a b)) := by
    refine Commute.smul_right ?_ (-1 : K)
    ext g y
    rfl
  have ht : homRepresentation EL E a b =
      LinearMap.llcomp K L W W (E a b) + (-1 : K) • LinearMap.lcomp K W (EL a b) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  rw [ht, hc.add_pow, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Module.End.mul_apply, Module.End.natCast_apply, smul_pow, LinearMap.smul_apply,
    map_nsmul, map_smul, llcomp_pow_apply, lcomp_pow_apply, LinearMap.comp_apply]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul]

end pw

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem restrictRepresentation_pow_coe (E : GLOps n (KK O) W) (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (j : ℕ)
    (x : L) : (((restrictRepresentation E L hL a b) ^ j) x : W) = (E a b ^ j) (x : W) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem int_smul_mem_lattice (M : Submodule O W) (z : ℤ) {x : W} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem weightProjection_preserves_lattice [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M) (mu : Fin n → ℤ) (π : Module.End (KK O) W)
    (hπ : IsWtProj E mu π) : ∀ x ∈ M, π x ∈ M := by
  classical
  obtain ⟨sh, shwt, shM⟩ : ∃ sh : Fin n → ℤ → ℕ → Module.End (KK O) W,
      (∀ a c d ρ x, x ∈ weightSp E ρ → sh a c d x = ((Ring.choose (ρ a + c) d : ℤ) : KK O) • x) ∧
      (∀ a c d x, x ∈ M → sh a c d x ∈ M) := by
    refine ⟨fun a c d => ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : KK O) • binomE E a ij.1,
      ?_, ?_⟩
    · intro a c d ρ x hx
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, binomial_diagonal_apply_weight E a ρ x hx, smul_smul]
      rw [← Finset.sum_smul, Ring.add_choose_eq d (Commute.all _ _)]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun ij _ => by ring
    · intro a c d x hx
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun ij _ => ?_
      rw [LinearMap.smul_apply]
      exact int_smul_mem_lattice M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)
  have hT : ∀ nu : Fin n → ℤ, ∃ (T : Module.End (KK O) W) (h : (Fin n → ℤ) → ℤ), h mu = 1 ∧
      (nu ≠ mu → h nu = 0) ∧ (∀ ρ, ∀ x ∈ weightSp E ρ, T x = ((h ρ : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, T x ∈ M := by
    intro nu
    by_cases hne : nu = mu
    · refine ⟨1, fun _ => 1, rfl, fun h => absurd hne h, fun ρ x _ => by simp, fun x hx => by simpa using hx⟩
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, mu a - nu a = (d : ℤ) := ⟨(mu a - nu a).toNat, by omega⟩
        have hd0 : 0 < d := by omega
        refine ⟨sh a (-(nu a)) d, fun ρ => Ring.choose (ρ a + -(nu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(nu a)) d = 1
          rw [show mu a + -(nu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]
          rfl
        · intro _
          show Ring.choose (nu a + -(nu a)) d = 0
          rw [show nu a + -(nu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro ρ x hx
          exact shwt a _ _ ρ x hx
        · intro x hx
          exact shM a _ _ x hx
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, nu a - mu a = (d : ℤ) := ⟨(nu a - mu a).toNat, by omega⟩
        refine ⟨sh a (-(mu a)) 0 - sh a (-(mu a)) d,
          fun ρ => Ring.choose (ρ a + -(mu a)) 0 - Ring.choose (ρ a + -(mu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(mu a)) 0 - Ring.choose (mu a + -(mu a)) d = 1
          have hd0 : 0 < d := by omega
          rw [Ring.choose_zero_right, show mu a + -(mu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro _
          show Ring.choose (nu a + -(mu a)) 0 - Ring.choose (nu a + -(mu a)) d = 0
          rw [Ring.choose_zero_right, show nu a + -(mu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_self]
          rfl
        · intro ρ x hx
          rw [LinearMap.sub_apply, shwt a _ _ ρ x hx, shwt a _ _ ρ x hx, ← sub_smul]
          push_cast
          rfl
        · intro x hx
          rw [LinearMap.sub_apply]
          exact M.sub_mem (shM a _ _ x hx) (shM a _ _ x hx)
  have hproj : ∀ F : Finset (Fin n → ℤ), ∃ (P : Module.End (KK O) W) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧
      (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧ (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, P x ∈ M := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨1, fun _ => 1, rfl, by simp, fun nu x _ => by simp, fun x hx => by simpa using hx⟩
    | insert nu F hnu ih =>
      obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := ih
      obtain ⟨T, h, hh1, hh0, hhw, hhM⟩ := hT nu
      refine ⟨T * P, fun ρ => h ρ * g ρ, by simp [hh1, hg1], ?_, ?_, ?_⟩
      · intro ν hν hne
        rcases Finset.mem_insert.1 hν with rfl | hν'
        · simp [hh0 hne]
        · simp [hg0 ν hν' hne]
      · intro ρ x hx
        rw [Module.End.mul_apply, hgw ρ x hx, map_smul, hhw ρ x hx, smul_smul]
        congr 1
        push_cast
        ring
      · intro x hx
        exact hhM _ (hgM x hx)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) W) ≤ ⨆ nu ∈ F, weightSp E nu := by
    let bs := Module.finBasis (KK O) W
    have hb : ∀ i, ∃ s : Finset (Fin n → ℤ), bs i ∈ ⨆ nu ∈ s, weightSp E nu := by
      intro i
      apply Submodule.mem_iSup_iff_exists_finset.1
      rw [hE.2.2]
      exact Submodule.mem_top
    choose s hs using hb
    refine ⟨Finset.univ.biUnion s, ?_⟩
    rw [← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmono : (⨆ nu ∈ s i, weightSp E nu) ≤ ⨆ nu ∈ Finset.univ.biUnion s, weightSp E nu :=
      biSup_mono fun nu hnu => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hnu⟩
    exact hmono (hs i)
  obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := hproj F
  have hπP : π = P := by
    have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (π - P) := by
      refine iSup₂_le fun nu hnu => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hgw nu x hx]
      by_cases h : nu = mu
      · subst h
        rw [hπ.1 x hx, hg1]
        simp
      · rw [hπ.2 nu h x hx, hg0 nu hnu h]
        simp
    ext x
    have hx := hle (hF (Submodule.mem_top (x := x)))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
  intro x hx
  rw [hπP]
  exact hgM x hx

theorem homLattice_dividedPower_stable [CharZero (KK O)] (E : GLOps n (KK O) W) (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (hab : a ≠ b) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f ∈ homLattice M L := by
  have hf' : ∀ y : L, (y : W) ∈ M → f y ∈ M := hf
  show ∀ x : L, (x : W) ∈ M → divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x ∈ M
  intro x hx
  have hexp : divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x =
      ∑ m ∈ range (k + 1), (((-1 : ℤ) ^ (k - m) : ℤ) : KK O) •
        divPowE E a b m (f ((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x)) := by
    rw [divPowE, LinearMap.smul_apply, LinearMap.smul_apply, homRepresentation_pow_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    simp only [divPowE, LinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    have hc : ((k.choose m : ℕ) : KK O) * (m.factorial : KK O) * ((k - m).factorial : KK O) =
        (k.factorial : KK O) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmk
    have h1 : (m.factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have h2 : ((k - m).factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - m))
    rw [← hc]
    have h3 : ((k.choose m : ℕ) : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hmk).ne'
    push_cast
    field_simp
  rw [hexp]
  refine Submodule.sum_mem _ fun m _ => ?_
  apply int_smul_mem_lattice
  have hy : (((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x : L) : W) =
      divPowE E a b (k - m) (x : W) := by
    rw [Submodule.coe_smul, restrictRepresentation_pow_coe, divPowE, LinearMap.smul_apply]
  have hyM : divPowE E a b (k - m) (x : W) ∈ M := hM _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) _ hx
  have hfy := hf' _ (by rw [hy]; exact hyM)
  exact hM _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ hfy

end lat

end Formalism.MainNotions.G.GLWeightTheory
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.HomLatticeDividedPowerStable

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem homLattice_binomial_stable [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a : Fin n) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    binomE (homRepresentation (restrictRepresentation E L hL) E) a k f ∈ homLattice M L := by
  have hres := restrictRepresentation_isRep E hE L hL
  obtain ⟨s, π, h1, h2, h3, h4, h5⟩ := weight_projections_exist (restrictRepresentation E L hL) hres
  obtain ⟨s', π', h1', h2', h3', h4', h5'⟩ := weight_projections_exist E hE
  have hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have : ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x) := by
      intro mu' _

      rw [← map_sum, ← map_sum, h5]
    rw [Finset.sum_congr rfl this, h5']
  have hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu) := by
    intro mu' mu
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul,
      Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]
  have hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype := by
    intro mu
    refine linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_
    have hy' : (y : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu y).1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    by_cases h : nu = mu
    · subst h; rw [(h1 nu).1 y hy, (h1' nu).1 _ hy']
    · rw [(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']; rfl
  have hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L := by
    intro mu' mu x hx
    have hx1 : ((π mu x : L) : W) ∈ M := by
      have := congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]
      exact weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx
    exact weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)

  rw [hdec, map_sum]
  refine Submodule.sum_mem _ fun mu' _ => ?_

  rw [map_sum]
  refine Submodule.sum_mem _ fun mu _ => ?_
  rw [binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]
  exact int_smul_mem_lattice _ _ (hmem mu' mu)

theorem mem_homLattice_iff_basis (M : Submodule O W) (L : Submodule (KK O) W) {d : ℕ} (b : Module.Basis (Fin d) (KK O) L)
    (hbM : ∀ i, ((b i : L) : W) ∈ M)
    (hbc : ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o) (f : L →ₗ[KK O] W) :
    f ∈ homLattice M L ↔ ∀ i, f (b i) ∈ M := by
  constructor
  · intro hf i
    exact hf (b i) (hbM i)
  · intro hf
    show ∀ x : L, (x : W) ∈ M → f x ∈ M
    intro x hx
    choose o ho using hbc x hx
    have hx' : x = ∑ i, b.coord i x • b i := by
      simp only [Module.Basis.coord_apply]
      exact (b.sum_repr x).symm

    rw [hx', map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, ho i, algebraMap_smul]
    exact M.smul_mem (o i) (hf i)

end lat

theorem hom_lattice_dividedPower_stable : HomLatticeDividedPowerStable := by
  intro O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL
  obtain ⟨d, b, hbM, hbc⟩ := lattice_adapted_basis_exists O W M hM.2 hMQ L
  have hiff := mem_homLattice_iff_basis M L b hbM hbc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf
    · exact homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf
    · exact homLattice_binomial_stable E hE M hM.1 L hL a k f hf
  · have : homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map
        ((b.constr (KK O)).toLinearMap.restrictScalars O) := by
      ext f
      rw [hiff]
      constructor
      · intro hf
        exact ⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩
      · rintro ⟨y, hy, rfl⟩ i
        have : (b.constr (KK O) y) (b i) = y i := b.constr_basis (KK O) y i
        simpa [this] using hy i trivial
    rw [this]
    exact (Submodule.fg_pi fun _ => hM.2).map _
  · rw [eq_top_iff]
    intro f _
    choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)
    have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
    have hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne hA
    have h1 : (∏ i, a i) • f ∈ homLattice M L := by
      rw [hiff]
      intro i
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
      rw [LinearMap.smul_apply, hc, mul_comm, mul_smul]
      exact M.smul_mem _ (hax i)
    have h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f) := by
      rw [← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Formalism.MainNotions.G.GLWeightTheory
end
end
end
