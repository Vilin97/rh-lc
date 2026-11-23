module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochainStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (x : T ⟶ A) (m : ℕ) : ρ ≫ x ^ m = (ρ ≫ x) ^ m :=
  MonObj.comp_pow x m ρ

theorem chi_eq_of_torsion : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ g : Fn2 A, IsSecAdd n S g →
    ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb S hS g hg D _ _ x hx
  obtain ⟨E, _, _, ψ, z, hff, hz⟩ := hR D x
  apply hff.injective
  change ψ (chi n g D x) = ψ (b D x)
  have hpow : ∀ i : ℕ, (z ^ i) ^ n = spOver ψ ≫ x ^ i := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, hz, comp_pow_pt]

  have hterm : ∀ i : ℕ, ψ (g D (x ^ i) x) =
      (S D (x ^ (i + 1)) E ψ (z ^ (i + 1)) - S D (x ^ i) E ψ (z ^ i)) - S D x E ψ z := by
    intro i
    have h := hg D (x ^ i) x E ψ (z ^ i) z (hpow i) hz
    rw [← pow_succ, ← pow_succ] at h
    rw [h]
  have hnE : (n : E) = 0 := by
    rw [← map_natCast (algebraMap R E), hn, map_zero]
  have hsum : ψ (chi n g D x) = S D (x ^ n) E ψ (z ^ n) - S D (x ^ 0) E ψ (z ^ 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [chi, map_sum, hterm, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ S D (x ^ i) E ψ (z ^ i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, zero_mul, sub_zero]
  rw [hsum, hx, pow_zero, pow_zero]

  have h1 : (1 : Pt A E) ^ n = spOver ψ ≫ (1 : Pt A D) := by rw [one_pow, MonObj.comp_one]
  have h2 : (z ^ n) ^ n = 1 := by rw [hpow n, hx, MonObj.comp_one]
  have hs := (hS D 1).2 E ψ 1 (z ^ n) h1 h2
  rw [_root_.one_mul] at hs
  rw [hs, add_sub_cancel_left, hz]
  exact hb.1 D E ψ x hx

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifference

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n :=
  MonObj.comp_pow x n f

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      RingHom.FaithfullyFlat.stableUnderComposition ψ1.toRingHom ψ2.toRingHom hf1 hf2,
      hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ g : Fn2 A, IsSecAdd n S g := by
  intro R _ A _ _ n hr b hb S hS
  have difference (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) :=
    (GlobalTheory.sec_mul_diff R A n hr b hb D x y (S D x) (S D y) (S D (x * y))
      (hS D x) (hS D y) (hS D (x * y))).exists
  refine ⟨fun D _ _ x y ↦ (difference D x y).choose, ?_⟩
  intro D _ _ x y E _ _ ψ z w hz hw
  exact ((difference D x y).choose_spec E ψ z w hz hw).symm

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunctionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sectionAddition_two_point_function :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
        (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
        ∃ g : Fn2 A, IsSecAdd n S g :=
  @GlobalTheory.PtExt.exists_isSecAdd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isAdd_of_isSecDiff_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ (u : Fn1 A) (g : Fn2 A), IsSecDiff n S u → IsSecAdd n S g → IsAdd u g := by
  intro R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y
  let x' : Pt A D' := spOver φ ≫ x
  let y' : Pt A D' := spOver φ ≫ y
  obtain ⟨D1, _, _, ψ1, z1, h1, hz1⟩ := hR D' x'
  obtain ⟨E, _, _, ψ2, w, h2, hw⟩ := hR D1 (spOver ψ1 ≫ y')
  let ψ : D' →ₐ[R] E := ψ2.comp ψ1
  let z : Pt A E := spOver ψ2 ≫ z1
  have hψ : spOver ψ = spOver ψ2 ≫ spOver ψ1 := (spOver_comp ψ1 ψ2).symm
  have hz : z ^ n = spOver ψ ≫ x' := by
    rw [show z = spOver ψ2 ≫ z1 from rfl, ← comp_pow, hz1, hψ, Category.assoc]
  have hw' : w ^ n = spOver ψ ≫ y' := by rw [hw, hψ, Category.assoc]
  have hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y) := comp_mul _ _ _
  have hzw : (z * w) ^ n = spOver ψ ≫ spOver φ ≫ (x * y) := by
    rw [mul_pow, hz, hw', hmul, comp_mul]
  have hc (t : Pt A D) : spOver ψ ≫ spOver φ ≫ t = spOver (ψ.comp φ) ≫ t := by
    rw [← Category.assoc, spOver_comp]
  have hinj : Function.Injective ψ := fun _ _ h ↦ h1.injective (h2.injective h)
  apply hinj
  have e1 := hg D' x' y' E ψ z w hz hw'
  have e2 := hg D x y E (ψ.comp φ) z w (hz.trans (hc x)) (hw'.trans (hc y))
  rw [AlgHom.comp_apply] at e2
  have e3 := hu D D' φ (x * y) E ψ (z * w) hzw
  rw [hmul] at e3
  have e4 := hu D D' φ x E ψ z hz
  have e5 := hu D D' φ y E ψ w hw'
  simp only [map_sub]
  linear_combination e1 - e2 - e3 + e4 + e5

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isCoc_of_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
    ∀ u : Fn1 A, IsSecDiff n S u → IsCoc (whole A) u := by
  intro R _ A _ _ n hR b _ S _ u hu
  unfold IsCoc
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  obtain ⟨E, _, _, χ, z, hχ, hz⟩ := hR D'' (spOver ψ ≫ spOver φ ≫ x)
  apply (show Function.Injective χ from hχ.injective)
  have h1 := hu D D'' (ψ.comp φ) x E χ z (by rw [hz, ← spOver_comp, Category.assoc])
  have h2 := hu D D' φ x E (χ.comp ψ) z (by rw [hz, ← spOver_comp, Category.assoc])
  have h3 := hu D' D'' ψ (spOver φ ≫ x) E χ z hz
  rw [AlgHom.comp_apply] at h2
  rw [map_add χ, h1, h2, h3, ← spOver_comp, Category.assoc, AlgHom.comp_assoc]
  abel

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : (n : R) = 0) (hR : HasRoots A n) (b : Fn0 A) (hb : IsTorsChar n b) :
    ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
        chi n g D x = b D x := by
  have hSec := GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (hSec D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (hSec D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end
end
