module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtendsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorusLieSubStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLattice

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ToricQuot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_denominator {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (δ : X →+ K) :
    ∃ (a : O) (δ' : X →+ O), a ≠ 0 ∧ (algebraMap O K).toAddMonoidHom.comp δ' = algebraMap O K a • δ := by
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (fun i => δ (b i))
  choose g hg using ha
  refine ⟨a, (b.constr ℤ g).toAddMonoidHom, nonZeroDivisors.coe_ne_zero a, ?_⟩
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun i => ?_
  have := hg i
  simp only [Algebra.smul_def] at this
  simp [this, Algebra.smul_def]

theorem lattice_step {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {E E' T T' : Type} [AddCommGroup E] [Module O E] [AddCommGroup E'] [Module O E'] [Module.Projective O E']
    [AddCommGroup T] [Module K T] [Module O T] [IsScalarTower O K T]
    [AddCommGroup T'] [Module K T'] [Module O T'] [IsScalarTower O K T']
    (j : E →ₗ[O] T) (j' : E' →ₗ[O] T') (hj : IsBaseChange K j) (hj' : IsBaseChange K j')
    (I : (X →+ K) →ₗ[K] T) (A : T →ₗ[K] T') (hex : ∀ t, A t = 0 ↔ ∃ δ, I δ = t) (hA : Function.Surjective A)
    (io : (X →+ O) →ₗ[O] E) (f : E →ₗ[O] E')
    (hio : ∀ δ, j (io δ) = I ((algebraMap O K).toAddMonoidHom.comp δ)) (hf : ∀ e, j' (f e) = A (j e))
    (hsat : ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io) :
    LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  have : IsLocalizedModule (nonZeroDivisors O) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j).2 hj
  have : IsLocalizedModule (nonZeroDivisors O) j' :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K j').2 hj'
  have hinj : Function.Injective j' := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j') hxy
    exact smul_right_injective E' (nonZeroDivisors.coe_ne_zero c) hc
  refine ⟨le_antisymm ?_ ?_, fun e' => ?_⟩
  · intro e he
    have h0 : A (j e) = 0 := by rw [← hf, show f e = 0 from he, map_zero]
    obtain ⟨δ, hδ⟩ := (hex _).1 h0
    obtain ⟨a, δ', ha, hδ'⟩ := exists_denominator (O := O) δ
    have h1 : j (a • e) = j (io δ') := by
      rw [hio, hδ', map_smul, map_smul, hδ, algebraMap_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := j) h1
    refine hsat a e ha (hsat c _ (nonZeroDivisors.coe_ne_zero c) ⟨(c : O) • δ', ?_⟩)
    rw [map_smul]
    exact hc.symm
  · rintro _ ⟨δ, rfl⟩
    apply hinj
    rw [hf, hio, map_zero]
    exact (hex _).2 ⟨_, rfl⟩
  · obtain ⟨t, ht⟩ := hA (j' e')
    obtain ⟨⟨e, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) j t
    refine ⟨s, e, nonZeroDivisors.coe_ne_zero s, hinj ?_⟩
    have hs' : (s : O) • t = j e := hs
    rw [hf, ← hs', map_smul j', ← ht, ← algebraMap_smul K (s : O) t, map_smul, algebraMap_smul]

theorem exists_model_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S}
    (h : x = y) {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ M' : LieModel G y E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_fibre_model {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (G₁ : Over (Sp R')) [GrpObj G₁] (φ : G₁.left ⟶ G.left)
    (h : IsGrpPullback G₁ G (spMap (algebraMap R R')) φ) {V : Type} [AddCommGroup V] [Module R V]
    (M : LieModel G (𝟙 _) V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T)
      (M₁ : LieModel G₁ (𝟙 _) T) (j : V →ₗ[R] T),
      (∀ e, ((M₁.pt (j e)).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap (algebraMap R R') ≫ 𝟙 _)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  have tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  let c := algebraMap R R'
  have halg : (dualMap c).comp (algebraMap R (DualNumber R)) =
      (algebraMap R' (DualNumber R')).comp c := by
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hscale (r : R) : (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    all_goals simp [dualMap, epsMul, mul_comm]
  let base : epsAt (spMap c ≫ 𝟙 (Sp R)) ⟶ epsAt (𝟙 (Sp R)) :=
    Over.homMk (spMap (dualMap c)) (by
      change spMap (dualMap c) ≫ Spec.map _ ≫ 𝟙 (Sp R) = Spec.map _ ≫ spMap c ≫ 𝟙 (Sp R)
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 _) v) :
      IsTanAt G (spMap c ≫ 𝟙 _) (base ≫ v) := by
    have h1 : (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap c ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = (1 : Over.mk (spMap c ≫ 𝟙 (Sp R)) ⟶ G).left := by
      rw [← h1]; rfl
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hfst]
  have ex : ∀ e, ∃ t, M'.pt t = base ≫ M.pt e :=
    fun e => M'.onto _ (htan _ (M.tan e))
  choose f hf using ex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap c) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, hsm, M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hscale])) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf]
    exact Category.comp_id _
  obtain ⟨M'', h''⟩ := exists_model_of_eq (y := 𝟙 (Sp R') ≫ spMap (algebraMap R R'))
    (by rw [Category.comp_id, Category.id_comp]) M'
  obtain ⟨M₁, h₁⟩ := (LiePull.lieModel_pullback _ _ G G₁ _ φ h R' (𝟙 _) T).1 M''
  refine ⟨T, iT, mT, mR, tower, M₁, j, fun e => ?_, GlobalTheory.T.lie_model_isBaseChange _ G R R' _ V T M M' j hl⟩
  have := hl e
  rw [h₁, h'', ← this]
  exact (Category.comp_id _).symm

theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {c : R →+* R'} {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] {φ : G₁.left ⟶ G.left} (h : IsGrpPullback G₁ G (spMap c) φ)
    {V : Type} [AddCommGroup V] [Module R V] {M : LieModel G (𝟙 _) V} {e : V} {v w : epsAt (𝟙 (Sp R')) ⟶ G₁}
    (hv : (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) (hw : (w.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left)) : v = w := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext (hv.trans hw.symm) ?_
  rw [Over.w v, Over.w w]

theorem lie_quot_full : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  intro O K _ _ _ _ _ G G' _ _ GK _ τ φ φ'
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hG hG' hφ hφ' MT hMT E _ _ E' _ _ M M'
  have := τ.free
  have := τ.finite
  have := τ.q_hom
  have := τ.i_hom
  have := hG.comm
  have := hG.smooth
  have := hG'.comm
  have := hG'.smooth
  have : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  obtain ⟨io, hio, hinj, hsat⟩ := GlobalTheory.T.semiabelian_torus_lie_sub O K G GK φ hG hφ τ.X τ.i MT hMT E M
  obtain ⟨f, hf⟩ := GlobalTheory.T.semiabelian_hom_lie_extends O K G G' GK τ.B φ φ' hG hG' hφ hφ' τ.q E E' M M'
  have := (GlobalTheory.T.lie_model_finite_projective _ G' O _ E' M').2
  obtain ⟨T, _, _, _, _, MK, j, hj, hbc⟩ := exists_fibre_model G GK φ hφ M
  obtain ⟨T', _, _, _, _, MK', j', hj', hbc'⟩ := exists_fibre_model G' τ.B φ' hφ' M'
  obtain ⟨I, hI, -⟩ := lieModel_exists_unique_diff _ _ GK K _ _ T MT MK τ.i
  obtain ⟨A, hA, -⟩ := lieModel_exists_unique_diff _ GK τ.B K _ T T' MK MK' τ.q
  have hex := GlobalTheory.T.torus_extension_tangent_exact K GK τ K (RingHom.id K)
  have hid : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  rw [hid] at hex
  refine ⟨io, f, hio, hf, hinj, lattice_step j j' hbc hbc' I A (fun t => ?_) (fun t' => ?_) io f
    (fun δ => ?_) (fun e => ?_) hsat⟩
  · have h1 : A t = 0 ↔ MK.pt t ≫ τ.q = 1 := by
      rw [← hA, ← MK'.pt_zero]
      exact MK'.inj.eq_iff.symm
    rw [h1, hex.1 _ (MK.tan t)]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨δ, rfl⟩ := MT.onto w hw
      exact ⟨δ, MK.inj (by rw [hI, e])⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨_, MT.tan δ, (hI δ).symm⟩
  · obtain ⟨v, hv, e⟩ := hex.2 _ (MK'.tan t')
    obtain ⟨t, rfl⟩ := MK.onto v hv
    exact ⟨t, MK'.inj (by rw [hA, e])⟩
  · apply MK.inj
    rw [hI]
    exact lifts_unique hφ (hj _) (hio δ)
  · apply MK'.inj
    rw [hA]
    exact lifts_unique hφ' (hj' _) (hf e _ (hj e))

end GlobalTheory.CompanionTheory.Ar.ToricQuot
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLatticeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_extension_lie_lattice : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | exact GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | (intros; apply GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtension

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TopPt

section Alg

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ}

theorem hom_eq_sum {O : Type} [CommRing O] (δ : X →+ O) :
    δ = ∑ i, δ (Module.Free.chooseBasis ℤ X i) •
      (Int.castAddHom O).comp ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
  ext x

  conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
  simp only [map_zsmul]
  simp [AddMonoidHom.finsetSum_apply, mul_comm]

theorem exists_dual (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) (a : Fin r) :
    ∃ x : X, ∀ φ : X →+ ℤ, φ x = bs.repr φ a := by
  refine ⟨∑ i, bs.repr ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom a • Module.Free.chooseBasis ℤ X i,
    fun φ => ?_⟩
  have e : φ = ∑ i, φ (Module.Free.chooseBasis ℤ X i) •
      ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
    ext x

    conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  conv_rhs => rw [e]

  simp [map_sum, mul_comm]

theorem indep {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    LinearIndependent O (fun a => (Int.castAddHom O).comp (bs a)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  obtain ⟨x, hx⟩ := exists_dual bs a
  have := DFunLike.congr_fun hg x
  simpa [AddMonoidHom.finsetSum_apply, hx, Finsupp.single_apply] using this

theorem span_top {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) = ⊤ := by
  have key : ∀ φ : X →+ ℤ, (Int.castAddHom O).comp φ ∈
      Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) := by
    intro φ
    have e : (Int.castAddHom O).comp φ = ∑ a, ((bs.repr φ a : ℤ) : O) • (Int.castAddHom O).comp (bs a) := by
      ext x
      have e₀ := DFunLike.congr_fun (bs.sum_repr φ) x
      rw [AddMonoidHom.finsetSum_apply] at e₀

      rw [AddMonoidHom.comp_apply, ← e₀, map_sum]
      simp [AddMonoidHom.finsetSum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [eq_top_iff]
  intro δ _
  rw [hom_eq_sum δ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key _)

theorem image_basis {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ))
    (io : (X →+ O) →ₗ[O] V) (h : Function.Injective io) :
    LinearIndependent O (fun a => io ((Int.castAddHom O).comp (bs a))) ∧
      LinearMap.range io = Submodule.span O (Set.range fun a => io ((Int.castAddHom O).comp (bs a))) := by
  have hk : LinearMap.ker io = ⊥ := LinearMap.ker_eq_bot_of_injective h
  have hi := (indep (O := O) bs).map' io hk
  refine ⟨hi, ?_⟩
  rw [LinearMap.range_eq_map, ← span_top (O := O) bs, Submodule.map_span, ← Set.range_comp]
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem cast_comp {O K : Type} [CommRing O] [CommRing K] (c : O →+* K) (φ : X →+ ℤ) :
    c.toAddMonoidHom.comp ((Int.castAddHom O).comp φ) = (Int.castAddHom K).comp φ := by
  ext x; simp

end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem exists_pull {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (z : S' ⟶ S) :
    ∃ (G₀ : Over S') (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left), IsSemiAbelian G₀ ∧ IsGrpPullback G₀ G z ψ :=
  ⟨(Over.pullback z).obj G, inferInstance, pullback.fst G.hom z, IsSemiAbelian.pullback z G hG,
    isGrpPullback_pullback G z⟩

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') {X : Scheme.{0}} {z : Sp R ⟶ X} {G : Over X}
    [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (hp : IsGrpPullback G₀ G z ψ)
    {GK : Over (Sp R')} {φ₀ : GK.left ⟶ G₀.left} (hw : φ₀ ≫ G₀.hom = GK.hom ≫ spMap c)
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G z V) (M₀ : LieModel G₀ (𝟙 _) V)
    (hM₀ : ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) (e : V) (v : epsAt (𝟙 (Sp R')) ⟶ GK) :
    (v.left ≫ φ₀ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M₀.pt e).left) ↔ (v.left ≫ (φ₀ ≫ ψ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  constructor
  · intro h
    rw [← Category.assoc, h, Category.assoc, hM₀]
  · intro h
    apply hp.1.hom_ext
    · rw [Category.assoc, h, Category.assoc, hM₀]
    · have w₂ := Over.w (M₀.pt e)
      have w₃ := Over.w v
      rw [Category.assoc, hw, ← Category.assoc, w₃, Category.assoc, w₂]
      show (Spec.map _ ≫ 𝟙 _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem main : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  intro X G _ _ hG L _ _ z GK _ φ τ G' _ φ'
  let _ := τ.addCommGroup
  let _ := τ.grpB
  have := τ.free
  have := τ.finite
  intro hG' hφ hφ' MT hMT V V' _ _ _ _ M M' r bs
  obtain ⟨G₀, _, ψ, hG₀, hp⟩ := exists_pull G hG z
  obtain ⟨φO, hF, hw⟩ : ∃ φO : GK.left ⟶ G₀.left, φO ≫ ψ = φ ∧
      φO ≫ G₀.hom = GK.hom ≫ spMap (algebraMap (𝓞 L) L) :=
    ⟨hp.1.lift φ (GK.hom ≫ spMap (algebraMap (𝓞 L) L)) (by rw [hφ.1.w, Category.assoc]), hp.1.lift_fst _ _ _,
      hp.1.lift_snd _ _ _⟩
  subst hF
  have hO : IsGrpPullback GK G₀ (spMap (algebraMap (𝓞 L) L)) φO := hp.cancel hφ hw
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main (𝓞 L) X z G G₀ ψ V hp).1 M
  have hiff := lifts_iff (algebraMap (𝓞 L) L) hp hw M M₀ hM₀
  obtain ⟨io, f, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.torus_extension_lie_lattice (𝓞 L) L G₀ G' GK τ φO φ'
    hG₀ hG' hO hφ' MT hMT V V' M₀ M'
  obtain ⟨b1, b2⟩ := image_basis bs io h3
  refine ⟨fun a => io ((Int.castAddHom (𝓞 L)).comp (bs a)), f, fun a => ?_, fun e v h => h2 e v ((hiff e v).2 h),
    b1, h4.trans b2, h5⟩
  have := h1 ((Int.castAddHom (𝓞 L)).comp (bs a))
  rw [cast_comp] at this
  exact (hiff _ _).1 this

end GlobalTheory.CompanionTheory.Ar.TopPt
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.semi_abelian_pullback_torus_extension : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopPt.main | exact GlobalTheory.CompanionTheory.Ar.TopPt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.TopPt.main <;> assumption)
end
end
