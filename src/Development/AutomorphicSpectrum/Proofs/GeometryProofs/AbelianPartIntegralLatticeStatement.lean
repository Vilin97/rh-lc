module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedFamilyBasisChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedGramDetPositiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenComponentMapCompatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangent
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieValuePullbackFieldExtStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeAltBis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abPart_comp_spMap_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ∧ GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e P.τ P'.τ mK.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hermitian_bundle_fibre_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeBC.main | exact GlobalTheory.CompanionTheory.Ar.HodgeBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeBC.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeAction

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ActBC

theorem exists_act_extends : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  intro L L' _ _ e G G' _ _ φ hpb O _ act act' hcomm V V' _ _ _ _ MV MV' j hj hspan ρ hρ
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ _ _ _ MV' _ act'.act act'.hom act'.one
    act'.mul act'.add
  refine ⟨ρ', hρ', fun a x => ?_⟩
  apply MV'.inj
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hρ' a (j x), Over.comp_left, Category.assoc, hcomm a, ← Category.assoc, hj x, Category.assoc,
      ← Over.comp_left, ← hρ a x, hj (ρ a x)]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.ActBC
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_action : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | exact GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeExists

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.Ar.LieBc

theorem exists_model_of_eq {S : Scheme.{0}} {R : Type} [CommRing R] (G : Over S) [GrpObj G] {x₁ x₂ : Sp R ⟶ S}
    (hx : x₁ = x₂) {T : Type} [AddCommGroup T] [Module R T] (M₁ : LieModel G x₁ T) :
    ∃ M₂ : LieModel G x₂ T, ∀ t, (M₂.pt t).left = (M₁.pt t).left := by
  subst hx
  exact ⟨M₁, fun _ => rfl⟩

theorem injective_of_isBaseChange {K K' : Type} [Field K] [Field K'] [Algebra K K'] {V T : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T] {j : V →ₗ[K] T}
    (hj : IsBaseChange K' j) : Function.Injective j := by
  have e : ⇑j = hj.equiv ∘ TensorProduct.mk K K' V 1 := by
    funext x
    simp [IsBaseChange.equiv_tmul]
  rw [e]
  exact hj.equiv.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective V)

theorem span_range_of_isBaseChange {K K' : Type} [CommRing K] [CommRing K'] [Algebra K K'] {V T : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T] [Module K' T] [IsScalarTower K K' T]
    {j : V →ₗ[K] T} (hj : IsBaseChange K' j) : Submodule.span K' (Set.range j) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  refine hj.inductionOn t (fun m => Submodule.subset_span ⟨m, rfl⟩) (fun s n h => Submodule.smul_mem _ s h)
    (fun a b ha hb => Submodule.add_mem _ ha hb)

end GlobalTheory.CompanionTheory.Ar.LieBc

theorem GlobalTheory.CompanionTheory.Ar.LieBc.main : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  intro L L' _ _ e G G' _ _ _ _ φ h V _ _ MV
  letI : Algebra L L' := e.toAlgebra
  obtain ⟨T, iT, mT, mR, tower, M', j, hl, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange (Sp L) G L L' (𝟙 _) V MV
  have hx : spMap (algebraMap L L') ≫ 𝟙 (Sp L) = 𝟙 (Sp L') ≫ spMap e := by
    rw [Category.comp_id, Category.id_comp]
    rfl
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.CompanionTheory.Ar.LieBc.exists_model_of_eq G hx M'
  refine ⟨T, iT, mT, GlobalTheory.CompanionTheory.Ar.LieMove.pullModel h M₂, j.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro c x
    change j (c • x) = e c • j x
    rw [map_smul]
    exact (algebraMap_smul L' c (j x)).symm
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.injective_of_isBaseChange hbc
  · intro x
    have e₁ := hl x
    have e₂ : (M'.pt (j x)).left ≫ 𝟙 G.left = spMap (dualMap (algebraMap L L')) ≫ (MV.pt x).left := e₁
    change (GlobalTheory.CompanionTheory.Ar.LieMove.liftEps h (M₂.pt (j x))).left ≫ φ = _
    rw [GlobalTheory.CompanionTheory.Ar.LieMove.liftEps_left, hM₂]
    exact (Category.comp_id _).symm.trans e₂
  · exact GlobalTheory.CompanionTheory.Ar.LieBc.span_range_of_isBaseChange hbc
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeExistsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_exists : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBc.main | exact GlobalTheory.CompanionTheory.Ar.LieBc.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBc.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralLattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem isTan_comp {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {R : Type}
    [CommRing R] {x : Sp R ⟶ S} {v : epsAt x ⟶ G} (h : IsTanAt G x v) : IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left]
  congr 1
  exact MonObj.one_comp f

theorem geo_height_arch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H → CMType H ⊕ CMType H) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : CMType H → Fin k → A.Λ) (b : CMType H → Fin m → 𝔐.Li) (bL : CMType H → Fin m → V) (T : CMType H → Matrix (Fin m) (Fin m) L), 𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ, IsValues 𝔐 z P MV (b τ) (bL τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ e : L →+* ℂ, (∀ τ, 0 < A.gramDet e (q τ)) ∧ ∃ ν : ℝ, 𝔐.GeoPhi lab (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) b ν ∧ 0 < ν ∧ ν = (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ _ z P V _ _ _ _ MV A lab r k m h v q b bL T hA hv hq hb hT hdet e
  obtain ⟨hact, hlab, hΛ, hcoch, hprin, t', m', MB, hfib, hlift⟩ := hA
  have hgram : ∀ τ, 0 < A.gramDet e (q τ) := fun τ =>
    GlobalTheory.T.adapted_gram_det_positive E L _ V A (lab τ) r k v (q τ) hv (hq τ).1 (hq τ).2 e
  refine ⟨hgram, ?_⟩
  obtain ⟨P', mK, mB, h1, h2, h3⟩ := GlobalTheory.T.abPart_comp_spMap_compat E H _ 𝔐.t L ℂ (spMap (algebraMap (𝓞 L) L) ≫ z) P e
  haveI := P.tK.semi.smooth
  obtain ⟨V', _, _, MV', j, hjs, hji, hjpt, hjspan⟩ := GlobalTheory.T.lie_model_base_change_exists L ℂ e P.tK.G P'.tK.G mK.φ mK.cart V MV
  obtain ⟨ρ', hρa, hρ⟩ := GlobalTheory.T.lie_model_base_change_action L ℂ e _ _ mK.φ mK.cart (𝓞 E) P.tK.act P'.tK.act mK.act V V' MV MV' j hjpt hjspan
    A.ρ hact
  have hcoch' : P'.IsCochars MV' (A.I.map j) :=
    GlobalTheory.T.torus_over_lie_model_base_change L ℂ e _ _ mK.φ P.τ P'.τ mK.cart h3 V V' MV MV' j hjpt A.I hcoch
  letI := P'.τ.grpB
  haveI := P'.τ.q_hom
  haveI := P'.e_hom
  obtain ⟨hbF, hbI, hbv⟩ := GlobalTheory.T.hermitian_bundle_fibre_tangent E H L t' P.tB P'.tB e m' mB A.Bq MB hfib V'
    (fun x => MV'.pt x ≫ P'.τ.q ≫ P'.e.hom) (fun x => isTan_comp _ (MV'.tan x))
  have hover : ∀ x : A.Λ, (MV'.pt (j x) ≫ P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ≫ m'.φ =
      spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt (A.f x)).left := fun x => by
    have e1 := hlift x
    unfold LieModel.Lifts at e1
    rw [dualMap_comp]
    have e3 : spMap ((dualMap e).comp (dualMap (algebraMap (𝓞 L) L))) =
        spMap (dualMap e) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3, Category.assoc, ← e1, Over.comp_left, Category.assoc]
    rw [← Category.assoc (P'.τ.q ≫ P'.e.hom).left, ← h2, Category.assoc, ← Category.assoc _ mK.φ, hjpt]
    simp [Over.comp_left]
  have heig : ∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a)) := fun τ a => by
    refine GlobalTheory.T.eigen_component_map_compat L ℂ V V' (𝓞 E) e j hjs A.ρ ρ' hρ (A.σ (lab τ)) (v a) ?_
    have h0 := (hq τ).1.1.ne_zero (Fin.castAdd k a)
    simpa [LinPt.fam] using h0
  have hpos : 0 < (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) *
      ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
    refine mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hv.2.2)) (Finset.prod_pos fun τ _ => ?_)
    have hne : e (T τ).det ≠ 0 := fun h0 => hdet τ ((map_eq_zero e).1 h0)
    have hp : (0 : ℝ) < 4 * Real.pi := by positivity
    have := hgram τ
    positivity
  refine ⟨_, ⟨P', V', _, _, MV', ρ', A.I.map j, hbF, fun τ => e.comp (A.σ (lab τ)), fun τ i => j (bL τ i), hρa, hcoch',
    fun τ a => GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_of_field_map _ _ _ e rfl (hlab (lab τ) a), hbI, fun τ i => ?_,
    GlobalTheory.T.adapted_family_basis_change E L _ V A lab r k m h v q bL T hv hq hT hdet e V' j hjs hji ρ' hρ heig hbF (fun τ c c' =>
      hbv _ _ _ _ (hover _) (hover _))⟩, hpos, rfl⟩
  obtain ⟨v₀, hv₀, e₀⟩ := hb τ i
  refine ⟨LieSigma.pullEps e _ ≫ v₀, GlobalTheory.T.lie_value_pullback_field_ext _ _ _ _ _ 𝔐.M _ _ _ e _ _ hv₀, ?_⟩
  rw [← h1, ← Category.assoc, hjpt, Category.assoc, e₀]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralLatticeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

theorem _root_.GlobalTheory.T.abelian_part_integral_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H → CMType H ⊕ CMType H) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : CMType H → Fin k → A.Λ) (b : CMType H → Fin m → 𝔐.Li) (bL : CMType H → Fin m → V) (T : CMType H → Matrix (Fin m) (Fin m) L), 𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ, IsValues 𝔐 z P MV (b τ) (bL τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ e : L →+* ℂ, (∀ τ, 0 < A.gramDet e (q τ)) ∧ ∃ ν : ℝ, 𝔐.GeoPhi lab (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) b ν ∧ 0 < ν ∧ ν = (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.geo_height_arch <;> assumption)
end
end
