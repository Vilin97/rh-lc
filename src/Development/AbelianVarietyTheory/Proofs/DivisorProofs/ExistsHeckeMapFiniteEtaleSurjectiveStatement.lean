module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHeckeMapCompEqForgetLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  first | (exact @GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (exact GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (intros; apply GlobalTheory.etale_isFinite_of_comp_etale_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_of_comp_etale_of_smoothOfRelativeDimension :
    ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ),
      h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY →
      Etale (h ≫ f) → Etale h := by
  intro X Y Z S h f sX sY d hs hX hY he
  subst hs
  haveI : FormallyUnramified (h ≫ f) := inferInstance
  haveI : FormallyUnramified h := FormallyUnramified.of_comp h f
  exact etale_of_formallyUnramified_of_smoothOfRelativeDimension h sY d hY hX

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension : ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ), h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY → Etale (h ≫ f) → Etale h := by
  first | (exact @GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (exact GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (intros; apply GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointPrimeToPSimilitude

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_adjoint_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ),
    c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) →
    c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧
      (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧
      (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  intro p _ D g c k hc hk hE himg hck
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hc)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hk)
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0

  have ginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply D.nondeg
    ext y
    have h := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at h
    simp only [map_zero, LinearMap.zero_apply]
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hcZ
    · exact h'
  choose f hf using himg
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => ginj (by rw [map_add (f := _), hf, hf, hf, smul_add])
  have fsmul : ∀ (b : D.O) x, f (b • x) = b • f x := fun b x => ginj (by
    rw [map_smul, hf, hf, smul_comm])
  let g' : D.La →ₗ[D.O] D.La :=
    { toFun := f, map_add' := fadd, map_smul' := fsmul }
  have h1 : ∀ x, g (g' x) = k • x := hf
  have h2 : ∀ x, g' (g x) = k • x := fun x => ginj (by rw [h1, map_nsmul])
  obtain ⟨q, hq⟩ := hck
  have hdiv : k ^ 2 / c = q := by rw [hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
  refine ⟨g', h1, h2, ?_, fun x => ⟨g x, h2 x⟩, ?_, ?_, ?_⟩
  · intro x y
    have h := hE (g' x) (g' y)
    rw [h1, h1, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul] at h
    push_cast [hdiv]
    have hqZ : ((k : ℤ) ^ 2 / c) = q := by
      rw [show (k : ℤ) ^ 2 = ((k ^ 2 : ℕ) : ℤ) by push_cast; ring, hq]
      push_cast
      exact Int.mul_ediv_cancel_left _ hcZ
    have hqI : (k : ℤ) ^ 2 = c * q := by exact_mod_cast hq
    rw [hqZ]
    apply mul_left_cancel₀ hcZ
    rw [← h, nsmul_eq_mul]
    push_cast
    rw [← sq, hqI]
    ring
  · rw [hdiv]
    have : q ∣ k ^ 2 := ⟨c, by rw [hq, mul_comm]⟩
    exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 2 hk)
  · rw [hdiv]; exact ⟨c, by rw [hq, mul_comm]⟩
  · rw [hdiv, hq]

end GlobalTheory.UPel.HT.Hecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointPrimeToPSimilitudeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.exists_adjoint_primeToP_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧ (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧ (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | exact GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem isSeparated_model_str {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have : IsSeparated (PSpace.str R n) := by
    unfold PSpace.str
    infer_instance
  rw [← e]
  infer_instance

theorem exists_heckeMap_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hg hgk hck M M'
  have hp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (Nat.coprime_zero_left p |>.1 hk) hp.ne_one
    · exact h
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.exists_adjoint_primeToP_similitude p D g c k hc hk hg hgk hck
  have h3' : ∀ x y, D.EF (g' x) (g' y) = ((k ^ 2 / c : ℕ) : ℤ) * D.EF x y := by
    intro x y
    rw [h3 x y]
    push_cast
    rfl
  have c1 : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have c2 : (N * k * k).Coprime p := Nat.Coprime.mul_left c1 hk
  have c3 : (N * k * k * k).Coprime p := Nat.Coprime.mul_left c2 hk
  have l1 : 3 ≤ N * k := hN.trans (Nat.le_mul_of_pos_right _ hk0)
  have l2 : 3 ≤ N * k * k := l1.trans (Nat.le_mul_of_pos_right _ hk0)
  have l3 : 3 ≤ N * k * k * k := l2.trans (Nat.le_mul_of_pos_right _ hk0)
  obtain ⟨M₂⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k) l2 c2
  obtain ⟨M₃⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k * k) l3 c3
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k N hc hk hN hNp hg hgk hck M M'
  obtain ⟨π₁, hπ₁⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g' (k ^ 2 / c) k (N * k) h5 hk l1 c1 h3' h4 h6 M' M₂
  obtain ⟨π₂, hπ₂⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k (N * k * k) hc hk l2 c2 hg hgk hck M₂ M₃
  have e : π ≫ M.s = M'.s := hπ.1
  have e₁ : π₁ ≫ M'.s = M₂.s := hπ₁.1
  have e₂ : π₂ ≫ M₂.s = M₃.s := hπ₂.1
  have f1 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g g' c (k ^ 2 / c) k N hk hN hNp h1 h2 h7 c2 M.toRepFam M'.toRepFam
    M₂.toRepFam π π₁ hπ hπ₁
  have f2 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g' g (k ^ 2 / c) c k (N * k) hk l1 c1 h2 h1 (by rw [mul_comm, h7]) c3
    M'.toRepFam M₂.toRepFam M₃.toRepFam π₁ π₂ hπ₁ hπ₂
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b N (N * k * k) _ c2 hN M M₂ (π₁ ≫ π)
    (by rw [Category.assoc, e, e₁]) f1
  obtain ⟨-, -, b3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b (N * k) (N * k * k * k) _ c3 l1 M' M₃ (π₂ ≫ π₁)
    (by rw [Category.assoc, e₁, e₂]) f2
  have s1 : Surjective π₁ := Surjective.of_comp π₂ π₁
  have t1 : Etale π₁ := GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension _ _ _ _ π₁ π M₂.s M'.s _ e₁ M₂.smooth M'.smooth a2
  have hs : IsSeparated π := by
    have : IsSeparated (π ≫ M.s) := e ▸ isSeparated_model_str M'
    exact IsSeparated.of_comp π M.s
  have hl : LocallyOfFiniteType π := by
    have := M'.smooth
    have : Smooth M'.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M'.s
    have : LocallyOfFiniteType (π ≫ M.s) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp π M.s
  obtain ⟨r1, r2⟩ := GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' _ _ _ π₁ π t1 s1 a2 a1 hs hl
  exact ⟨π, hπ, r2, r1, Surjective.of_comp π₁ π⟩

end GlobalTheory.UPel.HT.Hecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.exists_heckeMap_finite_etale_surjective' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective) | (exact GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective  <;> assumption)
end
end
