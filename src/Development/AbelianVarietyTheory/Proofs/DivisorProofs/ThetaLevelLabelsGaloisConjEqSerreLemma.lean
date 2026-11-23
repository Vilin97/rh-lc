module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderNStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMulStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QkMul

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qk_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  intro R _ _ _ D F _ _ k d p
  refine ⟨qkMk D.tau_bimult (d • p.y) p.g ?_, rfl, rfl⟩
  rw [mul_nsmul, qk_nsmul D.tau_bimult, map_nsmul]

end GlobalTheory.Mum.QkMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_levelPoint_mul_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  first | exact @GlobalTheory.Mum.QkMul.exists_qk_mul | exact GlobalTheory.Mum.QkMul.exists_qk_mul | (intros; apply GlobalTheory.Mum.QkMul.exists_qk_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphism

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaConj

def conjHom {R : Type} [CommRing R] [IsDomain R] (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact σ.commutes a)

end GlobalTheory.ThetaConj


open GlobalTheory.ThetaConj GlobalTheory.ThetaCoord in
theorem GlobalTheory.isThetaPt_conj : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  intro R _ _ A k σ I x x' v hx H
  have hs : Subsingleton (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Kb R)))
  have hn : Nonempty (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Kb R)))
  let e : Kb R ≃ₐ[FractionRing R] Kb R :=
    AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hi : conjHom σ ≫ conjHom e.symm.toAlgHom = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    ext a
    exact e.apply_symm_apply a
  have Q := isThetaPtOver_pull A (isThetaPtOver_of_subsingleton A H) _ _ hi
  have Q' : IsThetaPtOver A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
    convert Q using 2 with a a
    · exact Over.OverMorphism.ext (hx a)
    · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))
  refine ⟨H.1, H.2.1, fun p => ⟨⊤, trivial, ?_⟩⟩
  let j : TFK (R := R) (Kb R) ⟶ overRes (T := TFK (R := R) (Kb R)) ⊤ :=
    Over.homMk (TFK (R := R) (Kb R)).left.topIso.inv (by
      change _ ≫ Scheme.Opens.ι ⊤ ≫ _ = _
      rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact isThetaPtOver_pull A Q' (overResι ⊤) j
    (Over.OverMorphism.ext (TFK (R := R) (Kb R)).left.topIso.hom_inv_id)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphismStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaPoint_conj_algClosure_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  first | exact @GlobalTheory.isThetaPt_conj | exact GlobalTheory.isThetaPt_conj | (intros; apply GlobalTheory.isThetaPt_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabTorsTrait

open GlobalTheory.ArcPull GlobalTheory.Mum.Recog

theorem labTors_of_oneTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  intro R _ _ _ hR D A lab hT k hk
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, iφ, _, hG, ha, c, H⟩ := hT
  have := hR.2
  have : CharZero W := (RingHom.charZero_iff iφ).1 inferInstance
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB' := D'.tau_bimult
  have c' : Compat φ (Kb W) := c
  obtain ⟨f', hf'⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws W (maximalIdeal W) bW D' A' G' hG U' (Kb W) k hk
  obtain ⟨ε, hε, iε, oε, wε⟩ := exists_ptHom ha c' em
  have e : ∀ p, f' (tr hD c' em hB' p) = ε (lab k p) := fun p => by
    obtain ⟨p₁, h₁, h₂, h₃⟩ := (lies_iff hD c' em hB' p (tr hD c' em hB' p)).2 rfl
    exact ((hf'.1 _ _).1 (H k hk p p₁ _ _ h₁ h₂ h₃ ((hε _ _).1 rfl))).symm
  have pw : ∀ x : TFK (R := R) (Kb R) ⟶ A.A, ε x ^ k = 1 ↔ x ^ k = 1 := fun x => by
    rw [← map_pow, ← map_one ε, iε.eq_iff]
  have hp : ∀ p, lab k p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← pw, ← e]
    exact (((hf'.1 _ _).2 rfl) w hw).1
  refine ⟨fun y hy => ?_, hp, fun p q => ?_, fun p q r h => ?_, fun p q z => ?_⟩
  · obtain ⟨p', hp'⟩ := hf'.2.1 (ε y) ((pw y).2 hy)
    obtain ⟨p, rfl⟩ := (tr_bij hD c' em hB' hk).2 p'
    exact ⟨p, iε (by rw [← e, hp'])⟩
  · rw [← iε.eq_iff, ← e, ← e, hf'.2.2.1, tr_equiv]
  · apply iε
    rw [map_mul, ← e, ← e, ← e]
    exact hf'.2.2.2.1 _ _ _ ((tr_add hD c' em hB' p q r).2 h)
  · rw [← tr_weil hD c' em hB' hk p q z, wε k _ _ (hp p) (hp q) z, ← e, ← e]
    exact hf'.2.2.2.2 _ _ (Units.map em.toRingHom.toMonoidHom z)

end GlobalTheory.Mum.LabTorsTrait
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  first | exact @GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | exact GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | (intros; apply GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaLevels

variable {R : Type} [CommRing R] [IsDomain R]

def galPt {A : PolAV (Sp (FractionRing R))} (σ : Kb R →ₐ[FractionRing R] Kb R) (y : TFK (R := R) (Kb R) ⟶ A.A) :
    TFK (R := R) (Kb R) ⟶ A.A :=
  Over.homMk (spMap σ.toRingHom ≫ y.left) (by
    rw [Category.assoc, Over.w y]
    show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) σ.comp_algebraMap)

theorem conj_eq_of_pow_eq_one [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hT : OneTrait D.toPre A lab) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : Kb R) ≠ 0) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (hQ : ∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p')
    (hA : ∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ n = 1 → spMap σ.toRingHom ≫ y.left = y.left)
    {M d : ℕ} (hd : 1 ≤ d) (hM : M = n * d) (x₂ : QkPt D.toPre (Kb R) M → (TFK (R := R) (Kb R) ⟶ A.A))
    (hx₂ : ∀ p p', QkExt σ.toRingHom p p' → (x₂ p').left = spMap σ.toRingHom ≫ (lab M p).left)
    (h₂ : LabTors D.toPre A M x₂) (p' : QkPt D.toPre (Kb R) M) (hp' : lab M p' ^ n = 1) : x₂ p' = lab M p' := by
  subst hM
  have hnd : 1 ≤ n * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have T₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT n hn
  have T₂ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT (n * d) hnd
  obtain ⟨r, hr⟩ := T₁.1 _ hp'
  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r
  have hq : lab (n * d) q = lab n r := GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r q hqy hqg
  have hqp : QkPt.Equiv D.toPre (Kb R) q p' := (T₂.2.2.1 q p').1 (hq.trans hr)
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hnK r
  obtain ⟨q₀, hq₀y, hq₀g⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r₀
  have hq₀ : QkExt σ.toRingHom q₀ q := by
    obtain ⟨y, g, e⟩ := q
    obtain ⟨y₀, g₀, e₀⟩ := q₀
    dsimp only at hqy hqg hq₀y hq₀g
    subst hqg hq₀g hqy hq₀y
    exact ⟨congrArg (d • ·) hr₀.1, hr₀.2.1, hr₀.2.2⟩
  have e₂ := hx₂ q₀ q hq₀
  rw [GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r₀ q₀ hq₀y hq₀g, (T₁.2.2.1 r₀ r).2 (hQ r₀ r hr₀), hr, hA _ hp'] at e₂
  exact ((h₂.2.2.1 q p').2 hqp).symm.trans (Over.OverMorphism.ext e₂)

end GlobalTheory.Mum.ThetaLevels


open GlobalTheory.Mum.ThetaLevels in
theorem GlobalTheory.Mum.thetaLevels_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  intro R _ _ _ hR n hn ho hu D A lab hT hG
  have hch : CharZero R := hR.2
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ j₀ * (n ^ 2) ^ 2 := by
    refine ⟨((n ^ 2) ^ 2) ^ A.g * A.g.factorial, ?_⟩
    have h1 : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ (((n ^ 2) ^ 2) ^ A.g * A.g.factorial) :=
      Nat.lt_pow_self hn.one_lt
    have h2 : 1 ≤ (n ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ h2)
  refine ⟨j₀ + 4, fun i hi v hv hc σ p p' hpp' => ?_⟩
  have hmj : n ^ i = n ^ (i - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hbound : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < (n ^ i) := by
    rw [hmj]
    exact lt_of_lt_of_le hj₀ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn.pos (by omega)))
  have hF : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hKc : CharZero (Kb R) := charZero_of_injective_algebraMap (algebraMap (FractionRing R) (Kb R)).injective
  have hMK : (((n ^ i) ^ 2 : ℕ) : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))
  choose pre hpre using fun p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hMK p'
  let x₂ : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A) := fun q => galPt σ (lab ((n ^ i) ^ 2) (pre q))
  have hx₂ : ∀ q q', QkExt σ.toRingHom q q' → (x₂ q').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) q).left := fun q q' h => by
    show spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) (pre q')).left = _
    rw [GlobalTheory.QkClosure.qkExt_inj σ.toRingHom σ.comp_algebraMap (hpre q') h]
  have hM1 : 1 ≤ (n ^ i) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ hn.ne_zero))
  have H₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT ((n ^ i) ^ 2) hM1
  have H₂ := GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure R hR D A σ ((n ^ i) ^ 2) hM1 (lab ((n ^ i) ^ 2)) x₂ H₁ hx₂
  have Hn : ∀ q, lab ((n ^ i) ^ 2) q ^ n = 1 → x₂ q = lab ((n ^ i) ^ 2) q := fun q hq =>
    conj_eq_of_pow_eq_one hR D A lab hT hn.one_lt.le (Nat.cast_ne_zero.2 hn.ne_zero) σ (hG σ).1 (hG σ).2
      (d := n ^ (2 * i - 1)) (Nat.one_le_pow _ _ hn.pos)
      (by rw [← pow_mul, ← pow_succ']; congr 1; omega) x₂ hx₂ H₂ q hq
  obtain ⟨c, hc'⟩ := hc σ
  have h₁ := GlobalTheory.ThetaDescentLevel.isThetaPt_reindex hv pre
  have h₂ := GlobalTheory.T.thetaPoint_conj_algClosure_automorphism R A (n ^ i) σ _ (fun q => lab ((n ^ i) ^ 2) (pre q)) x₂ (fun q => v (pre q)) (fun q => rfl) h₁
  have h₃ : IsThetaPt A (n ^ i) x₂ (fun q => GlobalTheory.Ex.fnOf (v q)) :=
    GlobalTheory.Ex.ThetaDescent.isThetaPt_unit_mul A (n ^ i) x₂ _ _ (GlobalTheory.Ex.fnOf ((c⁻¹ : (Kb R)ˣ) : Kb R))
      ((Units.isUnit c⁻¹).map _) (fun q => by
        unfold GlobalTheory.Ex.fnOf
        rw [← map_mul, hc' _ _ (hpre q), ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]) h₂
  have key := GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n R D.toPre A n (i - 4) (n ^ i) hn ho hmj hbound (lab ((n ^ i) ^ 2)) x₂ H₁ H₂ Hn v hv h₃ p'
  rw [← key]
  exact hx₂ p p' hpp'
end
end
end
