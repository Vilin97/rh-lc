module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTrait
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma
import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.Enlarge.exists_rational_ext | exact GlobalTheory.Mum.Enlarge.exists_rational_ext | (intros; apply GlobalTheory.Mum.Enlarge.exists_rational_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemmaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  first | exact @GlobalTheory.Mum.thetaLevels_galois | exact GlobalTheory.Mum.thetaLevels_galois | (intros; apply GlobalTheory.Mum.thetaLevels_galois <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesValuesGaloisScalar

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  intro R _ _ _ hR D A lab hT m hm hmu v H σ
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em₀, hW, hφ, hloc, -, -, -, -⟩ := hT
  obtain ⟨C, _, _, _, _, _, _, hC⟩ := GlobalTheory.Ex.StepInh.exists_cExt W hW
  have hg : Function.Injective ((algebraMap (FractionRing W) C).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) C).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) C := (IsFractionRing.lift hg).toAlgebra
  have hA : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hg r
  haveI := hloc
  have hCR : GlobalTheory.Ex.CExt R (maximalIdeal R) C :=
    ⟨fun r => by rw [hA]; exact hC.1 _, fun r hr => by rw [hA]; exact hC.2 _ (map_nonunit φ r hr)⟩
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, nu, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult C ⊤
    (fun _ => trivial)
  have hB := D.tau_bimult
  let em : Kb R →ₐ[FractionRing R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hq := ((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N nu).2.2.2.2 (m ^ 2)).1
  choose e₁ he₁ using fun i => GlobalTheory.LabTrans.exists_ext hB em i
  choose e₂ he₂ using fun i => GlobalTheory.LabTrans.exists_ext hB σ i
  choose qq hqq using fun x : QkPt D.toPre C (m ^ 2) => (hq x).exists
  obtain ⟨s, hs⟩ := H C hCR em N nu e₁ (fun i => qq (e₁ i)) he₁ (fun i => hqq _)
  obtain ⟨s', hs'⟩ := H C hCR (em.comp σ) N nu (fun i => e₁ (e₂ i)) (fun i => qq (e₁ (e₂ i)))
    (fun i => GlobalTheory.LabTrans.qkExt_trans (he₂ i) (he₁ (e₂ i))) (fun i => hqq _)
  have key : ∀ p p', QkExt σ.toRingHom p p' → em (σ (v p)) = ((s' * s⁻¹ : Cˣ) : C) * em (v p') := by
    intro p p' h
    obtain rfl : e₂ p = p' := GlobalTheory.LabTrans.ext_unique hB σ (he₂ p) h
    have h1 := hs' p
    have h2 := hs (e₂ p)
    rw [AlgHom.comp_apply] at h1
    rw [h1, h2, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left]
  have emi : Function.Injective em := em.toRingHom.injective
  by_cases hex : ∃ p p', QkExt σ.toRingHom p p' ∧ v p' ≠ 0
  · obtain ⟨p₀, p₀', h₀, hv₀⟩ := hex
    have hσ0 : σ (v p₀) ≠ 0 := by
      intro h0
      have k0 := key p₀ p₀' h₀
      rw [h0, map_zero] at k0
      exact hv₀ ((map_eq_zero em).1 ((mul_eq_zero.1 k0.symm).resolve_left (Units.ne_zero _)))
    refine ⟨Units.mk0 (σ (v p₀) / v p₀') (div_ne_zero hσ0 hv₀), fun p p' h => emi ?_⟩
    have hne : em (v p₀') ≠ 0 := (map_ne_zero em).2 hv₀
    rw [Units.val_mk0, map_mul, map_div₀, key p p' h, key p₀ p₀' h₀]
    field_simp
  · push_neg at hex
    refine ⟨1, fun p p' h => ?_⟩
    have k := key p p' h
    rw [hex p p' h, map_zero, mul_zero] at k
    rw [hex p p' h, mul_zero]
    exact (map_eq_zero em).1 k
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesValuesGaloisScalarStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaSeries_values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  first | exact @GlobalTheory.Mum.values_galois_scalar | exact GlobalTheory.Mum.values_galois_scalar | (intros; apply GlobalTheory.Mum.values_galois_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquares

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalSquares

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_div {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    {k : ℕ} (l N : ℕ) (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) :
    ∃ q : QkPt D.toPre (Kb R) N, q.y = p.y ∧ l • q.g = p.g := by
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_nsmul_eq (F := Kb R) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1.1)
    (n := l) (by omega) p.g
  refine ⟨GlobalTheory.TorusExt.qkMk D.tau_bimult p.y g ?_, rfl, hg⟩
  rw [hN, mul_nsmul', hg]
  exact GlobalTheory.TorusExt.qk_nsmul D.tau_bimult p

theorem qkExt_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') {k N : ℕ}
    (l : ℕ) {p : QkPt D F k} {p' : QkPt D F' k} {q : QkPt D F N} (hp : QkExt σ.toRingHom p p') (hy : q.y = p.y)
    (hg : l • q.g = p.g) : ∃ q' : QkPt D F' N, QkExt σ.toRingHom q q' ∧ q'.y = p'.y ∧ l • q'.g = p'.g := by
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext σ.commutes
  refine ⟨GlobalTheory.TorusExt.qkExt hB σ.toRingHom hσ q, (GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).2 rfl, ?_, ?_⟩
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    exact hy
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    show l • GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ q.g = GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ p.g
    rw [← map_nsmul, hg]

theorem pow_left_of_comp {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (x y : TFK (R := R) (Kb R) ⟶ A.A) (h : y.left = spMap σ.toRingHom ≫ x.left)
    (l : ℕ) : (y ^ l).left = spMap σ.toRingHom ≫ (x ^ l).left := by
  let s : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap σ.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes))
  have hy : y = s ≫ x := Over.OverMorphism.ext h
  have hp : ∀ m : ℕ, s ≫ x ^ m = (s ≫ x) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [hy, ← hp]
  rfl

theorem compPow {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (m : ℕ) :
    (ρ ≫ x) ^ m = ρ ≫ x ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem lab_level {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hO : OneTrait D.toPre A lab) (k l N : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) N) (hy : q.y = p.y)
    (hg : GtPtF.IsNsmul l q.g p.g) : (lab k p).left = ((lab N q) ^ l).left := by
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hl
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := (GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k l N hk hl hN
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab N q))).2
    (by show hD.xe.symm p.y = hD.xe.symm q.y; rw [hy])
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g) =
        l • GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g)
      rw [(GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg, map_nsmul, map_nsmul])) (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₁).trans ((hf _ _).1 h₂).symm
  have hs : s ≫ lab k p = s ≫ lab N q ^ l := by
    have := congrArg e hx
    rw [e.apply_symm_apply, map_pow, e.apply_symm_apply] at this
    rw [this, compPow]
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs)

end GlobalTheory.Mum.GalSquares


open GlobalTheory.Mum.GalSquares in
theorem GlobalTheory.Mum.galEqN_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime →
    Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' →
        (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  intro R _ _ _ hR n hn _ _ D A lab hO ⟨i₀, H⟩ σ j p p' hpp'
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (Kb R)
  have hi : i₀ ≤ max i₀ j := le_max_left _ _
  have hj : j ≤ max i₀ j := le_max_right _ _
  have hN : (n ^ max i₀ j) ^ 2 = n ^ j * n ^ (2 * max i₀ j - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hl : 1 ≤ n ^ (2 * max i₀ j - j) := Nat.one_le_pow _ _ hn.pos
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  obtain ⟨q, hqy, hqg⟩ := exists_div hR D _ _ hl hN p
  obtain ⟨q', hq', hq'y, hq'g⟩ := qkExt_nsmul D.toPre D.tau_bimult σ _ hpp' hqy hqg
  have e₁ := lab_level D A lab hO _ _ _ hk hl hN p q hqy ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hqg.symm)
  have e₂ := lab_level D A lab hO _ _ _ hk hl hN p' q' hq'y ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hq'g.symm)
  rw [e₂, pow_left_of_comp σ _ _ (H _ hi σ q q' hq'), ← e₁]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquaresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionLabels_galois_all_levels_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  first | exact @GlobalTheory.Mum.galEqN_of_squares | exact GlobalTheory.Mum.galEqN_of_squares | (intros; apply GlobalTheory.Mum.galEqN_of_squares <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionGaloisEquivariantLabels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  intro R _ _ _ hR D n hn ho hu R₁ _ _ _ ρ D₁ A lab hρ hP hS hOT
  have hU₁ : UniTrait D₁.toPre A := by
    obtain ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, i6, em, hW, hφ, hloc, hG, hF, -, -⟩ := hOT
    exact ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, hW, hφ, hloc, hG, hF⟩
  obtain ⟨R₂, _, _, _, ρ₂, D₂, A₂, hρ₂, hP₂, hS₂, hU₂, hRat⟩ := GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait R hR D n hn ho hu R₁ ρ D₁ A hρ hP hS hU₁
  have hB₂ : Base R₂ := by
    have := hR.2
    exact ⟨hρ₂.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map ρ₂
  obtain ⟨lab₂, hOT₂⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₂ hB₂ D₂ A₂ hU₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂, D₂, A₂, lab₂, hρ₂, hP₂, hS₂, hOT₂, ?_⟩
  obtain ⟨i₀, hi₀⟩ := GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ hRat
  refine GlobalTheory.T.torsionLabels_galois_all_levels_of_squares R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ ⟨i₀, fun i hi => ?_⟩
  have hmo : Odd (n ^ i) := ho.pow
  have hmu : IsUnit ((n ^ i : ℕ) : R₂) := by rw [Nat.cast_pow]; exact hu₂.pow i
  obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R₂ hB₂ D₂ (n ^ i) hmo hmu (QkPt D₂.toPre (Kb R₂) ((n ^ i) ^ 2)) id
  have hθ := GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R₂ hB₂ D₂ A₂ lab₂ n hn ho hu₂ hOT₂ i v hv
  exact hi₀ i hi v hθ (GlobalTheory.T.thetaSeries_values_galois_scalar R₂ hB₂ D₂ A₂ lab₂ hOT₂ (n ^ i) hmo hmu v hv)

end GlobalTheory.Mum
end
end
