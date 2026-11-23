module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishingStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedQuotientVanishAboveDim

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GrTop

variable {X : Scheme.{0}}

theorem iInf_basicOpen {V : X.Opens} {ι : Type} (f : ι → Γ(X, V)) (S : Finset ι) (hS : S.Nonempty) :
    (⨅ α ∈ S, X.basicOpen (f α)) = X.basicOpen (∏ α ∈ S, f α) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert, Finset.prod_insert (by simpa using ha), Scheme.basicOpen_mul, ih]

theorem exists_cover {O : Type} [CommRing O] (q : X ⟶ Spec (CommRingCat.of O)) (d : ℕ) [SmoothOfRelativeDimension d q]
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Γ(X, V)), (⨆ α, X.basicOpen (f α)) = V ∧
      ∀ α, Nonempty (Coord q (X.basicOpen (f α)) d) := by
  classical
  have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have key : ∀ x : V, ∃ f : Γ(X, V), (x : X) ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h x.2
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f hf hc using key
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf _⟩)
  refine ⟨t, inferInstance, fun a => f a.1, le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_, fun a => hc a.1⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hx)
  obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s r j : ℕ)
    (hsr : s ≤ r) : Subsingleton (HQ (KS q s {V}) (r : ℤ) ((r : ℤ) + 1) j) := by
  have hz : ∀ (T : (KS q s {V}).FullSubcategory)
      (x : (sq (sFil (KS q s {V}) (r : ℤ)) (sFil (KS q s {V}) ((r : ℤ) + 1))).obj T), x = 0 := by
    intro T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have hy2 : (show T.obj.B from y) ∈ T.obj.pdPow ((r : ℤ).toNat) := hy
    rw [Int.toNat_natCast] at hy2
    have hy' : (show T.obj.B from y) ∈ T.obj.pdPow s := T.obj.pdPow_anti hsr hy2
    rw [T.property.1.1, Ideal.mem_bot] at hy'
    subst hy'
    rfl
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, hz1, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 a
  obtain ⟨z', hz1', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 b
  have e : z = z' := funext fun σ => (hz _ _).trans (hz _ _).symm
  subst e
  rfl

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop (hG : KH.LocGr) (hP : KH.PolyTf) : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V →
    ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r → Subsingleton (HQ (KS q s {V}) r (r + 1) j) := by
  intro K _ _ X q d _ V hV s r j hr
  lift r to ℕ using (by omega)
  have hdr : d < r := by exact_mod_cast hr
  rcases le_or_gt s r with hsr | hsr
  · exact twoVariableSeriesVanishesBelowDegree_one_shiftVariable q V s r j hsr
  obtain ⟨ι, _, f, hcov, hc⟩ := exists_cover q d hV
  let U : ι → X.Opens := fun α => X.basicOpen (f α)
  have hloc : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU (sq (thFil (smFun X q) (r : ℤ))
      (thFil (smFun X q) ((r : ℤ) + 1))) (St (TF 1 s) {⨅ α ∈ S, U α}) j) := by
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    have haff : IsAffineOpen (⨅ α ∈ S, U α) := by
      change IsAffineOpen (⨅ α ∈ S, X.basicOpen (f α))
      rw [iInf_basicOpen f S hS]
      exact hV.basicOpen _
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (hc α).some (iInf₂_le α hα) haff
    exact GlobalTheory.CompanionTheory.KIso.loc_vanish q hG hP c' r s hdr (by omega) j
  have hglob := (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U 0).2.1
    hloc j
  have h2 : KS q s (Set.range U) ≤ KS q s {V} := by
    rintro T ⟨hT, W, ⟨α, rfl⟩, hW⟩
    exact ⟨hT, V, rfl, fun x hx => X.basicOpen_le (f α) (hW hx)⟩
  have hc' : ∀ W ∈ ({V} : Set X.Opens), W ≤ sSup (Set.range U) := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, sSup_range]
    exact hcov.ge
  have b := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF 1 s : ObjectProperty (Thick (smFun X q))) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} h2 hc' j).1 (r : ℤ) ((r : ℤ) + 1)
  have : Subsingleton (HQ (KS q s (Set.range U)) (r : ℤ) ((r : ℤ) + 1) j) := hglob
  exact ⟨fun a c => b.1 (@Subsingleton.elim _ this _ _)⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop_main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) :=
  @grTop GlobalTheory.CompanionTheory.LocGrStep.loc_gr GlobalTheory.CompanionTheory.PolyTfCon.polyTf

end GlobalTheory.CompanionTheory.GrTop
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedQuotientVanishAboveDimStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.affine_graded_quotient_vanish_above_dim : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.GrTop.grTop_main | exact GlobalTheory.CompanionTheory.GrTop.grTop_main | (intros; apply GlobalTheory.CompanionTheory.GrTop.grTop_main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmul

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConePow

theorem cupPowC_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ) : cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    change (CH.mulP A).cupC (by omega) (cupPowC A (a • z) k) (a • z) =
      a ^ (k + 1) • (CH.mulP A).cupC (by omega) (cupPowC A z k) z
    rw [ih, map_smul, map_smul, LinearMap.smul_apply, pow_succ', mul_smul]

end GlobalTheory.CompanionTheory.ConePow
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmulStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cup_power_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  first | exact @GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | exact GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | (intros; apply GlobalTheory.CompanionTheory.ConePow.cupPowC_smul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeOne

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resI (x : X) : K →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ q)).hom

theorem spec_resI (x : X) :
    Spec.map (CommRingCat.ofHom (resI q x)) = X.fromSpecResidueField x ≫ q := by
  have : CommRingCat.ofHom (resI q x) = Spec.preimage (X.fromSpecResidueField x ≫ q) := rfl
  rw [this, Spec.map_preimage]

def resPt (x : X) : PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K))
    (X.residueField x ⧸ (⊥ : Ideal (X.residueField x))) :=
  ⟨(Ideal.quotientMap ⊥ (resI q x) bot_le,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (X.residueField x)))) ≫ X.fromSpecResidueField x), by
    rw [Category.assoc, ← spec_resI, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl⟩

def resT (x : X) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (X.residueField x) (resI q x) ⊥
    (dividedPowersBot _)
    ⟨fun h => absurd rfl h, fun _ => ⟨1, by simp⟩⟩
    ⟨by simp, fun a ha => by
      classical
      have : a = 0 := ha
      subst this
      rw [map_zero, dividedPowersBot_dpow_eq, dividedPowersBot_dpow_eq]
      simp only [true_and]
      split_ifs <;> simp⟩
    (resPt q x) (fun _ => rfl)

end GlobalTheory.CompanionTheory.ConeOne

open GlobalTheory.CompanionTheory.ConeOne in
theorem GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  intro K _ X q ⟨x⟩ h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h
  have h2 : (fun s : ComposableArrows (Thick (smFun X q)) 0 =>
      (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) = 0 := h1
  have h3 := congrFun h2 (ComposableArrows.mk₀ (resT q x))
  exact one_ne_zero (α := X.residueField x) h3
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonemptyStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.unit_class_ne_zero_of_nonempty : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | exact GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.OneKNeZero

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := GlobalTheory.T.unit_class_ne_zero_of_nonempty

theorem gr_top_van : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) := GlobalTheory.T.affine_graded_quotient_vanish_above_dim

theorem cupPowC_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := GlobalTheory.T.cup_power_smul

end CrystallineSemistableComparison.Pb
end
end
end
